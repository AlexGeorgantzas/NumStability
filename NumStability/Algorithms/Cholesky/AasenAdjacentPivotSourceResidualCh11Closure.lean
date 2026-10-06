/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Theorem 11.8: optimal operational middle-solve correction

The printed proof of Theorem 11.8 bounds the accumulated lower factor of
adjacent-pivot tridiagonal GEPP by `‖M‖∞ ≤ 2`.  The exact symmetric
tridiagonal counterexample in `AasenMiddleGEPPCh11Counterexample` shows that
this step is false: consecutive adjacent interchanges can move arbitrarily
many earlier multipliers into one row.  We therefore do not use that step,
nor the false coefficient-one forward certificate derived from it.

This file proves the strongest unconditional normwise statement supplied by
the literal DGTTRF/DGTTRS executor.  Its row-sparse residual correction is not
merely an a posteriori correction: among *all* matrices making the computed
solution exact, it has minimum infinity norm.  Consequently the remaining
printed quantitative claim is equivalent to bounding this observable optimal
backward error.  A final Aasen wrapper consumes exactly that scalar check.
-/
import NumStability.Algorithms.Cholesky.AasenAdjacentPivotResidualDomainCh11Discrepancy

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenAdjacentOperational

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.AasenAdjacentGEPP
open NumStability.Ch11Closure.AasenDirect
open NumStability.Ch11Closure.AasenDirectGEPP
open NumStability.Ch11Closure.SparseFactor

set_option maxRecDepth 20000

/-- Vector of observable source residuals of a proposed middle solution. -/
noncomputable def dgttrsSourceResidualVector {n : ℕ}
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => dgttrsSourceResidual T z y i

/-- The natural normwise backward-error quotient of a nonzero computed
solution.  For the actual no-breakdown executor, `y = 0` forces `z = 0`, so
the repository's totalized `0 / 0 = 0` convention gives the correct value in
that branch as well. -/
noncomputable def dgttrsOptimalBackwardError {n : ℕ}
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) : ℝ :=
  infNormVec (dgttrsSourceResidualVector T z y) / infNormVec y

/-- The nonnegative sparse budget has the same infinity norm as its signed
correction. -/
theorem dgttrsSparseResidualBudget_infNorm_eq_correction_infNorm
    {n : ℕ} (hn : 0 < n) (T : Fin n → Fin n → ℝ)
    (z y : Fin n → ℝ) :
    infNorm (dgttrsSparseResidualBudget hn T z y) =
      infNorm (dgttrsSparseResidualCorrection hn T z y) := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      simpa [dgttrsSparseResidualBudget, abs_abs] using
        row_sum_le_infNorm (dgttrsSparseResidualCorrection hn T z y) i
    · exact infNorm_nonneg _
  · apply infNorm_le_of_row_sum_le
    · intro i
      have hrow := row_sum_le_infNorm
        (dgttrsSparseResidualBudget hn T z y) i
      simpa [dgttrsSparseResidualBudget, abs_abs] using hrow
    · exact infNorm_nonneg _

/-- For a nonzero solution, every row sum of the row-sparse budget is the
absolute source residual divided by the attained solution infinity norm. -/
theorem dgttrsSparseResidualBudget_row_sum_eq {n : ℕ} (hn : 0 < n)
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (hy : y ≠ 0)
    (i : Fin n) :
    (∑ j : Fin n, |dgttrsSparseResidualBudget hn T z y i j|) =
      |dgttrsSourceResidual T z y i| / infNormVec y := by
  let jmax := dgttrsMaxSolutionIndex hn y
  have hjmax : y jmax ≠ 0 := by
    simpa [jmax] using dgttrsMaxSolutionIndex_ne_zero_of_ne_zero hn y hy
  have hmax : infNormVec y = |y jmax| := by
    simpa [jmax] using dgttrsMaxSolutionIndex_spec hn y
  calc
    (∑ j : Fin n, |dgttrsSparseResidualBudget hn T z y i j|) =
        ∑ j : Fin n, if j = jmax then
          |dgttrsSourceResidual T z y i / y jmax| else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases h : j = jmax <;>
        simp [dgttrsSparseResidualBudget, dgttrsSparseResidualCorrection,
          hy, jmax, h]
    _ = |dgttrsSourceResidual T z y i / y jmax| := by simp
    _ = |dgttrsSourceResidual T z y i| / |y jmax| := abs_div _ _
    _ = |dgttrsSourceResidual T z y i| / infNormVec y := by rw [hmax]

/-- Exact norm formula for the sparse residual correction.  Under the
zero-reflection property enjoyed by the actual no-breakdown solve, its norm is
precisely the standard normwise backward-error quotient. -/
theorem dgttrsSparseResidualBudget_infNorm_eq_optimalBackwardError
    {n : ℕ} (hn : 0 < n) (T : Fin n → Fin n → ℝ)
    (z y : Fin n → ℝ) (hzero : y = 0 → z = 0) :
    infNorm (dgttrsSparseResidualBudget hn T z y) =
      dgttrsOptimalBackwardError T z y := by
  by_cases hy : y = 0
  · have hz : z = 0 := hzero hy
    subst y
    subst z
    have hbudget :
        dgttrsSparseResidualBudget hn T (0 : Fin n → ℝ) 0 = 0 := by
      funext i j
      simp [dgttrsSparseResidualBudget, dgttrsSparseResidualCorrection]
    rw [hbudget]
    have hnorm0 : infNorm (0 : Fin n → Fin n → ℝ) = 0 := by
      apply le_antisymm
      · apply infNorm_le_of_row_sum_le
        · simp
        · norm_num
      · exact infNorm_nonneg _
    have hres0 :
        dgttrsSourceResidualVector T (0 : Fin n → ℝ) 0 = 0 := by
      funext i
      simp [dgttrsSourceResidualVector, dgttrsSourceResidual]
    rw [hnorm0]
    unfold dgttrsOptimalBackwardError
    rw [hres0]
    simp [infNormVec]
  · have hynorm : 0 < infNormVec y := by
      let jmax := dgttrsMaxSolutionIndex hn y
      have hj : y jmax ≠ 0 := by
        simpa [jmax] using dgttrsMaxSolutionIndex_ne_zero_of_ne_zero hn y hy
      calc
        0 < |y jmax| := abs_pos.mpr hj
        _ = infNormVec y := by
          symm
          simpa [jmax] using dgttrsMaxSolutionIndex_spec hn y
    apply le_antisymm
    · apply infNorm_le_of_row_sum_le
      · intro i
        rw [dgttrsSparseResidualBudget_row_sum_eq hn T z y hy i]
        exact div_le_div_of_nonneg_right
          (abs_le_infNormVec (dgttrsSourceResidualVector T z y) i)
          (infNormVec_nonneg y)
      · exact div_nonneg (infNormVec_nonneg _) (infNormVec_nonneg _)
    · obtain ⟨imax, himax⟩ :=
        infNormVec_exists_abs_eq hn (dgttrsSourceResidualVector T z y)
      have hrow := row_sum_le_infNorm
        (dgttrsSparseResidualBudget hn T z y) imax
      rw [dgttrsSparseResidualBudget_row_sum_eq hn T z y hy imax] at hrow
      simpa [dgttrsOptimalBackwardError, dgttrsSourceResidualVector,
        himax] using hrow

/-- Any exact correction must have norm at least the residual quotient.  This
is the usual lower-bound half of normwise backward-error optimality, proved
directly in the repository's finite-function infinity norms. -/
theorem dgttrsOptimalBackwardError_le_infNorm_of_exact_correction
    {n : ℕ} (hn : 0 < n) (T : Fin n → Fin n → ℝ)
    (z y : Fin n → ℝ) (hy : y ≠ 0) (DeltaT : Fin n → Fin n → ℝ)
    (hexact : ∀ i : Fin n,
      ∑ j : Fin n, (T i j + DeltaT i j) * y j = z i) :
    dgttrsOptimalBackwardError T z y ≤ infNorm DeltaT := by
  have hynorm : 0 < infNormVec y := by
    let jmax := dgttrsMaxSolutionIndex hn y
    have hj : y jmax ≠ 0 := by
      simpa [jmax] using dgttrsMaxSolutionIndex_ne_zero_of_ne_zero hn y hy
    calc
      0 < |y jmax| := abs_pos.mpr hj
      _ = infNormVec y := by
        symm
        simpa [jmax] using dgttrsMaxSolutionIndex_spec hn y
  have hres : ∀ i : Fin n,
      |dgttrsSourceResidual T z y i| ≤
        infNorm DeltaT * infNormVec y := by
    intro i
    have hid :
        dgttrsSourceResidual T z y i =
          ∑ j : Fin n, DeltaT i j * y j := by
      unfold dgttrsSourceResidual
      have he := hexact i
      simp_rw [add_mul] at he
      rw [Finset.sum_add_distrib] at he
      linarith
    rw [hid]
    calc
      |∑ j : Fin n, DeltaT i j * y j| ≤
          ∑ j : Fin n, |DeltaT i j * y j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |DeltaT i j| * |y j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
      _ ≤ ∑ j : Fin n, |DeltaT i j| * infNormVec y := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (abs_le_infNormVec y j)
          (abs_nonneg _)
      _ = (∑ j : Fin n, |DeltaT i j|) * infNormVec y := by
        rw [Finset.sum_mul]
      _ ≤ infNorm DeltaT * infNormVec y :=
        mul_le_mul_of_nonneg_right (row_sum_le_infNorm DeltaT i)
          (infNormVec_nonneg y)
  have hv :
      infNormVec (dgttrsSourceResidualVector T z y) ≤
        infNorm DeltaT * infNormVec y :=
    infNormVec_le_of_abs_le _
      (by simpa [dgttrsSourceResidualVector] using hres)
      (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
  apply (div_le_iff₀ hynorm).2
  simpa [dgttrsOptimalBackwardError] using hv

/-- The row-sparse correction attains the minimum possible infinity norm.
This is an exact, unconditional theorem: no target backward-error bound or
accumulated-factor norm estimate is assumed. -/
theorem dgttrsSparseResidualCorrection_is_infNorm_minimal
    {n : ℕ} (hn : 0 < n) (T : Fin n → Fin n → ℝ)
    (z y : Fin n → ℝ) (hy : y ≠ 0) (DeltaT : Fin n → Fin n → ℝ)
    (hexact : ∀ i : Fin n,
      ∑ j : Fin n, (T i j + DeltaT i j) * y j = z i) :
    infNorm (dgttrsSparseResidualCorrection hn T z y) ≤ infNorm DeltaT := by
  rw [← dgttrsSparseResidualBudget_infNorm_eq_correction_infNorm]
  rw [dgttrsSparseResidualBudget_infNorm_eq_optimalBackwardError hn T z y
    (fun h => (hy h).elim)]
  exact dgttrsOptimalBackwardError_le_infNorm_of_exact_correction
    hn T z y hy DeltaT hexact

/-- **Actual DGTTRF/DGTTRS optimality endpoint.**  Under operational
no-breakdown and the bandwidth-two backsolve guard, the literal computed
solution has an exact row-sparse backward correction; its norm is the
observable residual quotient and is no larger than that of any other exact
correction. -/
theorem higham11_8_actual_dgttrs_optimal_operational_middle
    (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hnb : DGTTRFNoBreakdown fp T)
    (hval3 : gammaValid fp 3) :
    let y := flDGTTRS fp n T z
    let DeltaT := dgttrsSparseResidualCorrection hn T z y
    let BT := dgttrsSparseResidualBudget hn T z y
    AasenDirectMiddleBudget fp n T z y DeltaT BT ∧
      infNorm BT = dgttrsOptimalBackwardError T z y ∧
      ∀ E : Fin n → Fin n → ℝ,
        (∀ i : Fin n, ∑ j : Fin n, (T i j + E i j) * y j = z i) →
        infNorm DeltaT ≤ infNorm E := by
  intro y DeltaT BT
  have hzero : y = 0 → z = 0 := by
    intro hy
    exact flDGTTRS_eq_zero_imp_rhs_eq_zero fp n T z hnb hval3 (by
      simpa [y] using hy)
  refine ⟨?_, ?_, ?_⟩
  · simpa [DeltaT, BT, y] using
      higham11_8_actual_dgttrs_sparse_operational_middle_budget
        fp n hn T z hnb hval3
  · exact dgttrsSparseResidualBudget_infNorm_eq_optimalBackwardError
      hn T z y hzero
  · intro E hE
    by_cases hy : y = 0
    ·
      have hDelta : DeltaT = 0 := by
        funext i j
        simp [DeltaT, dgttrsSparseResidualCorrection, hy]
      rw [hDelta]
      have hnorm0 : infNorm (0 : Fin n → Fin n → ℝ) = 0 := by
        apply le_antisymm
        · apply infNorm_le_of_row_sum_le
          · simp
          · norm_num
        · exact infNorm_nonneg _
      rw [hnorm0]
      exact infNorm_nonneg E
    · simpa [DeltaT] using
        dgttrsSparseResidualCorrection_is_infNorm_minimal
          hn T z y hy E hE

/-- **Corrected all-dimension Aasen solve endpoint.**  The literal rounded
`DGTTRF`/`DGTTRS` middle solve is composed with the actual rounded outer
triangular solves and the rounded Aasen factorization.  The resulting
correction makes the computed solution exact and is bounded entrywise by an
explicit factorization-plus-solve budget.  Moreover, the middle part of that
budget has norm exactly equal to the minimum norm of *any* correction making
the computed middle solution exact.

Unlike the printed Theorem 11.8 radius, this statement is valid for every
positive dimension and does not use the false accumulated-factor estimate
`‖M‖∞ ≤ 2` or assume a target-sized residual bound. -/
theorem higham11_8_aasen_backward_error_direct_actual_dgttrs_corrected
    (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A Pmat : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hp : FlAasenPivots fp n A)
    (hnb : DGTTRFNoBreakdown fp (flAasen fp n A).That)
    (hval : gammaValid fp (3 * n)) :
    let Lh := (flAasen fp n A).Lhat
    let Th := (flAasen fp n A).That
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z := fl_forwardSub fp n Lh rhs
    let y := flDGTTRS fp n Th z
    let DeltaT := dgttrsSparseResidualCorrection hn Th z y
    let BT := dgttrsSparseResidualBudget hn Th z y
    let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
    let w := fl_backSub fp n Uouter y
    let Bfactor : Fin n → Fin n → ℝ := fun i j =>
      gamma fp (3 * n) *
        ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
    let Bsolve : Fin n → Fin n → ℝ :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT Lh Th Uouter
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ Bfactor i j + Bsolve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w j = rhs i) ∧
      infNorm DeltaA ≤ infNorm Bfactor + infNorm Bsolve ∧
      infNorm BT = dgttrsOptimalBackwardError Th z y ∧
      ∀ E : Fin n → Fin n → ℝ,
        (∀ i : Fin n, ∑ j : Fin n, (Th i j + E i j) * y j = z i) →
        infNorm DeltaT ≤ infNorm E := by
  intro Lh Th rhs z y DeltaT BT Uouter w Bfactor Bsolve
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval
  have hvaln : gammaValid fp n := gammaValid_mono fp (by omega) hval
  obtain ⟨hmiddle, hBToptimal, hminimal⟩ :=
    higham11_8_actual_dgttrs_optimal_operational_middle
      fp n hn Th z hnb hval3
  have hLdiag_one : ∀ i : Fin n, Lh i i = 1 :=
    flAasen_L_unit_diag fp n A
  have hLdiag_ne : ∀ i : Fin n, Lh i i ≠ 0 := fun i => by
    rw [hLdiag_one i]
    exact one_ne_zero
  have hLlower : ∀ i j : Fin n, i.val < j.val → Lh i j = 0 :=
    flAasen_L_upper_zero fp n A
  let Afact : Fin n → Fin n → ℝ :=
    fun i j => ∑ p : Fin n, ∑ q : Fin n, Lh i p * Th p q * Lh j q
  obtain ⟨DeltaS, hDeltaS, hsource⟩ :=
    higham11_15_fl_aasen_solve_chain_source_backward_error_of_direct_middle_budget
      fp n Afact Pmat Lh Th b y DeltaT BT hLdiag_ne hLlower hvaln
      (by intro i j; rfl) hmiddle
  have hfactor : ∀ i j : Fin n, |Afact i j - A i j| ≤ Bfactor i j :=
    fun i j => fl_aasen_factorization_residual fp n A hp hsymm hval i j
  obtain ⟨DeltaA, hDeltaA, hDeltaA_source⟩ :=
    higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
      n A Afact DeltaS Bfactor Bsolve rhs w hfactor hDeltaS hsource
  have hBfactor_nonneg : ∀ i j : Fin n, 0 ≤ Bfactor i j := by
    intro i j
    exact mul_nonneg (gamma_nonneg fp hval)
      (Finset.sum_nonneg (fun p _ =>
        Finset.sum_nonneg (fun q _ => by positivity)))
  have hBsolve_nonneg : ∀ i j : Fin n, 0 ≤ Bsolve i j :=
    higham11_15_aasenChainDeltaABound_nonneg
      n (gamma fp n) BT Lh Th Uouter (gamma_nonneg fp hvaln) hmiddle.1
  have hDeltaNorm : infNorm DeltaA ≤ infNorm Bfactor + infNorm Bsolve := by
    apply infNorm_le_of_row_sum_le
    · intro i
      have hfrow : ∑ j : Fin n, Bfactor i j ≤ infNorm Bfactor := by
        calc
          ∑ j : Fin n, Bfactor i j = ∑ j : Fin n, |Bfactor i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hBfactor_nonneg i j)]
          _ ≤ infNorm Bfactor := row_sum_le_infNorm Bfactor i
      have hsrow : ∑ j : Fin n, Bsolve i j ≤ infNorm Bsolve := by
        calc
          ∑ j : Fin n, Bsolve i j = ∑ j : Fin n, |Bsolve i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hBsolve_nonneg i j)]
          _ ≤ infNorm Bsolve := row_sum_le_infNorm Bsolve i
      calc
        ∑ j : Fin n, |DeltaA i j| ≤
            ∑ j : Fin n, (Bfactor i j + Bsolve i j) :=
          Finset.sum_le_sum (fun j _ => hDeltaA i j)
        _ = (∑ j : Fin n, Bfactor i j) + ∑ j : Fin n, Bsolve i j :=
          Finset.sum_add_distrib
        _ ≤ infNorm Bfactor + infNorm Bsolve := add_le_add hfrow hsrow
    · exact add_nonneg (infNorm_nonneg _) (infNorm_nonneg _)
  exact ⟨DeltaA, hDeltaA, hDeltaA_source, hDeltaNorm,
    hBToptimal, hminimal⟩

/-- **Source-honest Theorem 11.8 endpoint.**  The printed global Aasen radius
follows from a single executable check on the *minimum possible* normwise
backward error of the actual middle solve.  Unlike the printed proof, this
statement does not assume `‖M‖∞ ≤ 2`, a factor-forward certificate, or the
desired conclusion in componentwise form. -/
theorem higham11_8_aasen_backward_error_direct_of_actual_dgttrs_optimal_error
    (fp : FPModel) (n : ℕ) (hn : 2 ≤ n)
    (A Pmat : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (k : ℕ)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hp : FlAasenPivots fp n A)
    (hLhat_cap : ∀ i j : Fin n, |(flAasen fp n A).Lhat i j| ≤ 1)
    (hnb : DGTTRFNoBreakdown fp (flAasen fp n A).That)
    (hoptimal :
      let T := (flAasen fp n A).That
      let z := fl_forwardSub fp n (flAasen fp n A).Lhat
        (fun i => ∑ j : Fin n, Pmat i j * b j)
      let y := flDGTTRS fp n T z
      dgttrsOptimalBackwardError T z y ≤ gamma fp k * infNorm T)
    (hk : k ≤ 8 * n + 25)
    (hval : gammaValid fp (15 * n + 25)) :
    let Lh := (flAasen fp n A).Lhat
    let Th := (flAasen fp n A).That
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z := fl_forwardSub fp n Lh rhs
    let y := flDGTTRS fp n Th z
    let BT := dgttrsSparseResidualBudget (by omega) Th z y
    let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
    let w := fl_backSub fp n Uouter y
    let Bfactor : Fin n → Fin n → ℝ := fun i j =>
      gamma fp (3 * n) *
        ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
    let Bsolve : Fin n → Fin n → ℝ :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT Lh Th Uouter
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ Bfactor i j + Bsolve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w j = rhs i) ∧
      infNorm DeltaA ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (15 * n + 25) * infNorm Th := by
  intro Lh Th rhs z y BT Uouter w Bfactor Bsolve
  have hn0 : 0 < n := by omega
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval
  let DeltaT := dgttrsSparseResidualCorrection hn0 Th z y
  have hmiddle : AasenDirectMiddleBudget fp n Th z y DeltaT BT := by
    simpa [DeltaT, BT, Th, z, y] using
      higham11_8_actual_dgttrs_sparse_operational_middle_budget
        fp n hn0 Th z hnb hval3
  have hzero : y = 0 → z = 0 := by
    intro hy
    exact flDGTTRS_eq_zero_imp_rhs_eq_zero fp n Th z hnb hval3 (by
      simpa [y] using hy)
  have hBTnorm : infNorm BT ≤ gamma fp k * infNorm Th := by
    rw [show infNorm BT = dgttrsOptimalBackwardError Th z y by
      simpa [BT] using
        dgttrsSparseResidualBudget_infNorm_eq_optimalBackwardError
          hn0 Th z y hzero]
    simpa [Th, z, y] using hoptimal
  exact higham11_8_aasen_backward_error_direct_of_operational_middle_budget
    fp n hn A Pmat b y DeltaT BT k hsymm hp hLhat_cap
    hmiddle hBTnorm hk hval

end NumStability.Ch11Closure.AasenAdjacentOperational
