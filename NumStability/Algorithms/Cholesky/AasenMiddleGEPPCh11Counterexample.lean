/-
Algorithms/Cholesky/AasenMiddleGEPPCh11Counterexample.lean

Chapter 11, Theorem 11.8 honesty certificate: the coefficient-one middle
factor-norm premise used by the direct assembly is not a consequence of the
actual Aasen/tridiagonal-GEPP inputs.  The counterexample below is entirely
exact, uses the repository's constructive `flAasen` output and recursive GEPP
trace, and satisfies every other middle/outer structural premise of the direct
wrapper.
-/
import NumStability.Algorithms.Cholesky.AasenCoupledFpCh11Closure
import NumStability.Algorithms.HighamChapter9

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenDirect

open NumStability

/-- Exact floating-point model used by the coefficient-one counterexample. -/
noncomputable def middleCoeffOneCounterFP : FPModel :=
  FPModel.exactWithUnitRoundoff 0 (by norm_num)

/-- Symmetric tridiagonal counterexample matrix
`[[1,1],[1,-1]]`. -/
noncomputable def middleCoeffOneCounterT : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => -1

/-- Unit-lower GEPP factor of `middleCoeffOneCounterT`. -/
noncomputable def middleCoeffOneCounterL : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 1

/-- Upper GEPP factor of `middleCoeffOneCounterT`. -/
noncomputable def middleCoeffOneCounterU : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => -2

theorem middleCoeffOneCounterT_symm :
    ∀ i j : Fin 2, middleCoeffOneCounterT i j = middleCoeffOneCounterT j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem middleCoeffOneCounterT_tridiagonal :
    IsTridiagonal 2 middleCoeffOneCounterT := by
  intro i j h
  omega

/-- In exact arithmetic, the constructive Aasen sweep returns the counterexample
matrix itself as its computed tridiagonal middle factor. -/
theorem middleCoeffOneCounter_flAasen_That :
    (flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).That =
      middleCoeffOneCounterT := by
  change (flAasenIter middleCoeffOneCounterFP 2 middleCoeffOneCounterT 2).That =
    middleCoeffOneCounterT
  rw [flAasenIter_succ middleCoeffOneCounterFP 2 middleCoeffOneCounterT 1]
  rw [flAasenIter_succ middleCoeffOneCounterFP 2 middleCoeffOneCounterT 0]
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flAasenIter, flAasenStep, flAasenInit,
      aTdiag, aHdiag, aHsub, aUpperH, aHcol, aLcol,
      middleCoeffOneCounterFP, middleCoeffOneCounterT,
      FPModel.exactWithUnitRoundoff, fl_dotProduct, Fin.foldl_succ] <;> rfl

/-- Exact equation-(9.20) certificate: `L U = T` and `DeltaT = 0`. -/
theorem middleCoeffOneCounter_exact_h20 :
    higham9_20_tridiag_lu_perturbation_model 2 middleCoeffOneCounterT
      middleCoeffOneCounterL middleCoeffOneCounterU (fun _ _ => 0) 0 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [middleCoeffOneCounterT, middleCoeffOneCounterL,
        middleCoeffOneCounterU, Fin.sum_univ_two] <;> rfl
  · intro i j
    norm_num

theorem middleCoeffOneCounterT_infNorm :
    infNorm middleCoeffOneCounterT = 2 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;> norm_num [middleCoeffOneCounterT, Fin.sum_univ_two]
    · norm_num
  · have h := row_sum_le_infNorm middleCoeffOneCounterT (0 : Fin 2)
    norm_num [middleCoeffOneCounterT, Fin.sum_univ_two] at h
    exact h

theorem middleCoeffOneCounterL_infNorm :
    infNorm middleCoeffOneCounterL = 2 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;> norm_num [middleCoeffOneCounterL, Fin.sum_univ_two]
    · norm_num
  · have h := row_sum_le_infNorm middleCoeffOneCounterL (1 : Fin 2)
    norm_num [middleCoeffOneCounterL, Fin.sum_univ_two] at h
    exact h

theorem middleCoeffOneCounterU_infNorm :
    infNorm middleCoeffOneCounterU = 2 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;> norm_num [middleCoeffOneCounterU, Fin.sum_univ_two]
    · norm_num
  · have h := row_sum_le_infNorm middleCoeffOneCounterU (1 : Fin 2)
    norm_num [middleCoeffOneCounterU, Fin.sum_univ_two] at h
    exact h

/-- The coefficient-one bound is numerically false: `2 * 2 > 2`. -/
theorem middleCoeffOneCounter_not_le :
    ¬ infNorm middleCoeffOneCounterL * infNorm middleCoeffOneCounterU ≤
      infNorm middleCoeffOneCounterT := by
  rw [middleCoeffOneCounterL_infNorm, middleCoeffOneCounterU_infNorm,
    middleCoeffOneCounterT_infNorm]
  norm_num

theorem middleCoeffOneCounter_flAasen_pivots :
    FlAasenPivots middleCoeffOneCounterFP 2 middleCoeffOneCounterT := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  change (flAasenIter middleCoeffOneCounterFP 2 middleCoeffOneCounterT 2).Hhat
    (1 : Fin 2) (0 : Fin 2) ≠ 0
  rw [flAasenIter_succ middleCoeffOneCounterFP 2 middleCoeffOneCounterT 1]
  rw [flAasenIter_succ middleCoeffOneCounterFP 2 middleCoeffOneCounterT 0]
  norm_num [flAasenIter, flAasenStep, flAasenInit,
    aTdiag, aHdiag, aHsub, aUpperH, aHcol, aLcol,
    middleCoeffOneCounterFP, middleCoeffOneCounterT,
    FPModel.exactWithUnitRoundoff, fl_dotProduct, Fin.foldl_succ] <;>
    exact (one_ne_zero : (1 : ℝ) ≠ 0)

theorem middleCoeffOneCounter_flAasen_Lhat_cap :
    ∀ i j : Fin 2,
      |(flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).Lhat i j| ≤ 1 := by
  intro i j
  change |(flAasenIter middleCoeffOneCounterFP 2 middleCoeffOneCounterT 2).Lhat i j| ≤ 1
  rw [flAasenIter_succ middleCoeffOneCounterFP 2 middleCoeffOneCounterT 1]
  rw [flAasenIter_succ middleCoeffOneCounterFP 2 middleCoeffOneCounterT 0]
  fin_cases i <;> fin_cases j <;>
    norm_num [flAasenIter, flAasenStep, flAasenInit,
      aTdiag, aHdiag, aHsub, aUpperH, aHcol, aLcol,
      middleCoeffOneCounterFP, middleCoeffOneCounterT,
      FPModel.exactWithUnitRoundoff, fl_dotProduct, Fin.foldl_succ]

theorem middleCoeffOneCounter_flAasen_exact_h20 :
    higham9_20_tridiag_lu_perturbation_model 2
      (flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).That
      middleCoeffOneCounterL middleCoeffOneCounterU (fun _ _ => 0)
      (gamma middleCoeffOneCounterFP 2) := by
  rw [middleCoeffOneCounter_flAasen_That]
  simpa [middleCoeffOneCounterFP, gamma, FPModel.exactWithUnitRoundoff] using
    middleCoeffOneCounter_exact_h20

theorem middleCoeffOneCounter_L_diag :
    ∀ i : Fin 2, middleCoeffOneCounterL i i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num [middleCoeffOneCounterL]

theorem middleCoeffOneCounter_U_diag :
    ∀ i : Fin 2, middleCoeffOneCounterU i i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num [middleCoeffOneCounterU]

theorem middleCoeffOneCounter_L_lower :
    ∀ i j : Fin 2, i.val < j.val → middleCoeffOneCounterL i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [middleCoeffOneCounterL]

theorem middleCoeffOneCounter_U_upper :
    ∀ i j : Fin 2, j.val < i.val → middleCoeffOneCounterU i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [middleCoeffOneCounterU]

/-- Every direct Theorem-11.8 input concerning the actual Aasen output and the
middle LU perturbation model can hold while the coefficient-one factor-norm
condition fails. -/
theorem middleCoeffOneCounter_actual_aasen_inputs :
    (∀ i j : Fin 2, middleCoeffOneCounterT i j = middleCoeffOneCounterT j i) ∧
    FlAasenPivots middleCoeffOneCounterFP 2 middleCoeffOneCounterT ∧
    (∀ i j : Fin 2,
      |(flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).Lhat i j| ≤ 1) ∧
    higham9_20_tridiag_lu_perturbation_model 2
      (flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).That
      middleCoeffOneCounterL middleCoeffOneCounterU (fun _ _ => 0)
      (gamma middleCoeffOneCounterFP 2) ∧
    (∀ i : Fin 2, middleCoeffOneCounterL i i ≠ 0) ∧
    (∀ i : Fin 2, middleCoeffOneCounterU i i ≠ 0) ∧
    (∀ i j : Fin 2, i.val < j.val → middleCoeffOneCounterL i j = 0) ∧
    (∀ i j : Fin 2, j.val < i.val → middleCoeffOneCounterU i j = 0) ∧
    gammaValid middleCoeffOneCounterFP (15 * 2 + 25) ∧
    ¬ infNorm middleCoeffOneCounterL * infNorm middleCoeffOneCounterU ≤
      infNorm (flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).That := by
  refine ⟨middleCoeffOneCounterT_symm,
    middleCoeffOneCounter_flAasen_pivots,
    middleCoeffOneCounter_flAasen_Lhat_cap,
    middleCoeffOneCounter_flAasen_exact_h20,
    middleCoeffOneCounter_L_diag,
    middleCoeffOneCounter_U_diag,
    middleCoeffOneCounter_L_lower,
    middleCoeffOneCounter_U_upper, ?_, ?_⟩
  · norm_num [middleCoeffOneCounterFP, gammaValid, FPModel.exactWithUnitRoundoff]
  · rw [middleCoeffOneCounter_flAasen_That]
    exact middleCoeffOneCounter_not_le

/-! The same `U` is not merely an arbitrary exact factor: it is produced by an
accepted recursive partial-pivoting trace (the leading column is a tie, so row
zero is a legal pivot). -/

theorem middleCoeffOneCounter_GEPP_trace :
    higham9_7_PartialPivotGEPPUTrace 2
      middleCoeffOneCounterT middleCoeffOneCounterU := by
  let Uone : Fin 1 → Fin 1 → ℝ := fun _ _ => -2
  have hchoice0 :
      higham9_1_partialPivotChoice middleCoeffOneCounterT 0 0 := by
    constructor
    · norm_num
    · intro i hi
      fin_cases i <;> norm_num [middleCoeffOneCounterT]
  have hpivot0 : middleCoeffOneCounterT (0 : Fin 2) 0 ≠ 0 := by
    norm_num [middleCoeffOneCounterT]
  have hstage1 :
      luFirstSchurComplement
          (higham9_2_rowPermutedMatrix middleCoeffOneCounterT
            (higham9_7_firstPivotRowSwap (0 : Fin 2))) =
        (fun _ _ : Fin 1 => (-2 : ℝ)) := by
    funext i j
    fin_cases i
    fin_cases j
    norm_num [luFirstSchurComplement, higham9_2_rowPermutedMatrix,
      higham9_7_firstPivotRowSwap, middleCoeffOneCounterT]
  have hchoice1 :
      higham9_1_partialPivotChoice (fun _ _ : Fin 1 => (-2 : ℝ)) 0 0 := by
    constructor
    · norm_num
    · intro i hi
      fin_cases i
      norm_num
  have hpivot1 : (fun _ _ : Fin 1 => (-2 : ℝ)) 0 0 ≠ 0 := by norm_num
  have hnext :
      higham9_7_PartialPivotGEPPUTrace 1
        (fun _ _ : Fin 1 => (-2 : ℝ)) Uone := by
    have hzero :
        higham9_7_PartialPivotGEPPUTrace 0
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix (fun _ _ : Fin 1 => (-2 : ℝ))
              (higham9_7_firstPivotRowSwap (0 : Fin 1))))
          (fun i => Fin.elim0 i) :=
      higham9_7_PartialPivotGEPPUTrace.done
    have h := higham9_7_PartialPivotGEPPUTrace.step hchoice1 hpivot1 hzero
    have hUone :
        luFirstStepU
            (higham9_2_rowPermutedMatrix (fun _ _ : Fin 1 => (-2 : ℝ))
              (higham9_7_firstPivotRowSwap (0 : Fin 1)))
            (fun i => Fin.elim0 i) = Uone := by
      funext i j
      fin_cases i
      fin_cases j
      norm_num [Uone, luFirstStepU, higham9_2_rowPermutedMatrix,
        higham9_7_firstPivotRowSwap]
    rw [hUone] at h
    exact h
  have hnext' :
      higham9_7_PartialPivotGEPPUTrace 1
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix middleCoeffOneCounterT
            (higham9_7_firstPivotRowSwap (0 : Fin 2)))) Uone := by
    rw [hstage1]
    exact hnext
  have h := higham9_7_PartialPivotGEPPUTrace.step hchoice0 hpivot0 hnext'
  have hU :
      luFirstStepU
          (higham9_2_rowPermutedMatrix middleCoeffOneCounterT
            (higham9_7_firstPivotRowSwap (0 : Fin 2))) Uone =
        middleCoeffOneCounterU := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [middleCoeffOneCounterU, Uone, luFirstStepU,
        higham9_2_rowPermutedMatrix, higham9_7_firstPivotRowSwap,
        middleCoeffOneCounterT]
  rw [hU] at h
  exact h

/-- Compact certificate that the failed coefficient-one inequality occurs for
the actual computed Aasen middle factor and a genuine exact GEPP trace whose
equation-(9.20) perturbation is zero. -/
theorem middleCoeffOneCounter_actual_GEPP :
    higham9_7_PartialPivotGEPPUTrace 2
      middleCoeffOneCounterT middleCoeffOneCounterU ∧
    (flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).That =
      middleCoeffOneCounterT ∧
    higham9_20_tridiag_lu_perturbation_model 2
      (flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).That
      middleCoeffOneCounterL middleCoeffOneCounterU (fun _ _ => 0)
      (gamma middleCoeffOneCounterFP 2) ∧
    ¬ infNorm middleCoeffOneCounterL * infNorm middleCoeffOneCounterU ≤
      infNorm (flAasen middleCoeffOneCounterFP 2 middleCoeffOneCounterT).That := by
  refine ⟨middleCoeffOneCounter_GEPP_trace,
    middleCoeffOneCounter_flAasen_That,
    middleCoeffOneCounter_flAasen_exact_h20, ?_⟩
  rw [middleCoeffOneCounter_flAasen_That]
  exact middleCoeffOneCounter_not_le

/-! ## The accumulated lower factor does not have infinity norm at most two

The detailed proof cited for Theorem 11.8 argues that the tridiagonal GEPP
lower factor has entries bounded by one and therefore has infinity norm at
most two.  That inference would require at most one off-diagonal entry in
*each row*.  Adjacent row interchanges only give at most one such entry in
each column: earlier multipliers move when a later interchange is accumulated
into the conventional lower-triangular factor.

The following exact three-by-three factorization records the smallest useful
instance.  GEPP interchanges rows at both stages.  Consequently the last row
of the accumulated lower factor contains both earlier multipliers and has row
sum `1 + 9/10 + 10/11 = 309/110 > 2`.
-/

noncomputable def middleAccumCounterT : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 9 / 10
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, ⟨2, _⟩ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 0
  | ⟨1, _⟩, ⟨2, _⟩ => 11 / 10
  | ⟨2, _⟩, ⟨0, _⟩ => 0
  | ⟨2, _⟩, ⟨1, _⟩ => 11 / 10
  | ⟨2, _⟩, ⟨2, _⟩ => -(219 / 100)

/-- The accumulated-factor counterexample lies in the exact source domain:
it is symmetric, not merely an arbitrary matrix admitted by a GEPP API. -/
theorem middleAccumCounterT_symm :
    ∀ i j : Fin 3, middleAccumCounterT i j = middleAccumCounterT j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The same source-domain witness is tridiagonal. -/
theorem middleAccumCounterT_tridiagonal :
    IsTridiagonal 3 middleAccumCounterT := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [middleAccumCounterT]

noncomputable def middleAccumCounterL : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨0, _⟩, ⟨2, _⟩ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨2, _⟩ => 0
  | ⟨2, _⟩, ⟨0, _⟩ => 9 / 10
  | ⟨2, _⟩, ⟨1, _⟩ => 10 / 11
  | ⟨2, _⟩, ⟨2, _⟩ => 1

noncomputable def middleAccumCounterU : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨0, _⟩, ⟨2, _⟩ => 11 / 10
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 11 / 10
  | ⟨1, _⟩, ⟨2, _⟩ => -(219 / 100)
  | ⟨2, _⟩, ⟨0, _⟩ => 0
  | ⟨2, _⟩, ⟨1, _⟩ => 0
  | ⟨2, _⟩, ⟨2, _⟩ => 1101 / 1100

/-- First active Schur complement in the literal adjacent-pivot GEPP run. -/
noncomputable def middleAccumCounterS1 : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => -(99 / 100)
  | ⟨1, _⟩, ⟨0, _⟩ => 11 / 10
  | ⟨1, _⟩, ⟨1, _⟩ => -(219 / 100)

/-- Tail upper factor after the second adjacent pivot. -/
noncomputable def middleAccumCounterU2 : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 11 / 10
  | ⟨0, _⟩, ⟨1, _⟩ => -(219 / 100)
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 1101 / 1100

def middleAccumCounterSigma : Fin 3 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

theorem middleAccumCounter_exact_permuted_lu :
    higham9_2_PermutedLUFactSpec 3 middleAccumCounterT
      middleAccumCounterL middleAccumCounterU middleAccumCounterSigma := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp_all [middleAccumCounterSigma]
    · intro b
      fin_cases b
      · exact ⟨(2 : Fin 3), rfl⟩
      · exact ⟨(0 : Fin 3), rfl⟩
      · exact ⟨(1 : Fin 3), rfl⟩
  · intro i
    fin_cases i <;> norm_num [middleAccumCounterL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [middleAccumCounterL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [middleAccumCounterU]
  · intro i j
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [middleAccumCounterT, middleAccumCounterL,
        middleAccumCounterU, middleAccumCounterSigma, Fin.sum_univ_three,
        zero_add, add_zero]
    case refine_5.«0».«1» => rfl
    case refine_5.«2».«1» =>
      change (0 : ℝ) + 1 = 1
      norm_num
    case refine_5.«2».«2» => rfl

theorem middleAccumCounterL_infNorm :
    infNorm middleAccumCounterL = 309 / 110 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;>
        norm_num [middleAccumCounterL, Fin.sum_univ_three, abs_of_nonneg]
    · norm_num
  · have h := row_sum_le_infNorm middleAccumCounterL (2 : Fin 3)
    norm_num [middleAccumCounterL, Fin.sum_univ_three, abs_of_nonneg] at h
    exact h

/-- Formal refutation of the `‖M‖∞ ≤ 2` shortcut for the conventional
accumulated lower-triangular factor of adjacent-pivot tridiagonal GEPP. -/
theorem middleAccumCounter_not_infNorm_le_two :
    ¬ infNorm middleAccumCounterL ≤ 2 := by
  rw [middleAccumCounterL_infNorm]
  norm_num

/-- The three-by-three counterexample is produced by the literal recursive
partial-pivoting GEPP trace: the first active column selects row one, and the
first active column of the Schur complement again selects row one.  Thus the
failed `‖M‖∞ ≤ 2` step occurs for the algorithmic adjacent-pivot schedule, not
merely for an arbitrary permuted LU factorization. -/
theorem middleAccumCounter_GEPP_trace :
    higham9_7_PartialPivotGEPPUTrace 3
      middleAccumCounterT middleAccumCounterU := by
  have hchoice0 :
      higham9_1_partialPivotChoice middleAccumCounterT 0 (1 : Fin 3) := by
    constructor
    · norm_num
    · intro i hi
      fin_cases i <;> norm_num [middleAccumCounterT]
  have hpivot0 : middleAccumCounterT (1 : Fin 3) 0 ≠ 0 := by
    norm_num [middleAccumCounterT]
  have hstage1 :
      luFirstSchurComplement
          (higham9_2_rowPermutedMatrix middleAccumCounterT
            (higham9_7_firstPivotRowSwap (1 : Fin 3))) =
        middleAccumCounterS1 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [luFirstSchurComplement, higham9_2_rowPermutedMatrix,
        higham9_7_firstPivotRowSwap, middleAccumCounterT,
        middleAccumCounterS1]
    all_goals
      simp only [if_neg (by decide : (2 : Fin 3) ≠ 0),
        if_neg (by decide : (2 : Fin 3) ≠ 1)] <;>
      norm_num
  have hchoice1 :
      higham9_1_partialPivotChoice middleAccumCounterS1 0 (1 : Fin 2) := by
    constructor
    · norm_num
    · intro i hi
      fin_cases i <;> norm_num [middleAccumCounterS1]
  have hpivot1 : middleAccumCounterS1 (1 : Fin 2) 0 ≠ 0 := by
    norm_num [middleAccumCounterS1]
  have hstage2 :
      luFirstSchurComplement
          (higham9_2_rowPermutedMatrix middleAccumCounterS1
            (higham9_7_firstPivotRowSwap (1 : Fin 2))) =
        (fun _ _ : Fin 1 => (1101 / 1100 : ℝ)) := by
    funext i j
    fin_cases i
    fin_cases j
    norm_num [luFirstSchurComplement, higham9_2_rowPermutedMatrix,
      higham9_7_firstPivotRowSwap, middleAccumCounterS1]
  have hchoice2 :
      higham9_1_partialPivotChoice
        (fun _ _ : Fin 1 => (1101 / 1100 : ℝ)) 0 0 := by
    constructor
    · norm_num
    · intro i hi
      fin_cases i
      norm_num
  have hpivot2 : (fun _ _ : Fin 1 => (1101 / 1100 : ℝ)) 0 0 ≠ 0 := by
    norm_num
  have htail1 :
      higham9_7_PartialPivotGEPPUTrace 1
        (fun _ _ : Fin 1 => (1101 / 1100 : ℝ))
        (fun _ _ : Fin 1 => (1101 / 1100 : ℝ)) := by
    have hzero :
        higham9_7_PartialPivotGEPPUTrace 0
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix
              (fun _ _ : Fin 1 => (1101 / 1100 : ℝ))
              (higham9_7_firstPivotRowSwap (0 : Fin 1))))
          (fun i => Fin.elim0 i) :=
      higham9_7_PartialPivotGEPPUTrace.done
    have h := higham9_7_PartialPivotGEPPUTrace.step hchoice2 hpivot2 hzero
    convert h using 1 <;>
      funext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [luFirstStepU, higham9_2_rowPermutedMatrix,
        higham9_7_firstPivotRowSwap]
  have htail2 :
      higham9_7_PartialPivotGEPPUTrace 2
        middleAccumCounterS1 middleAccumCounterU2 := by
    have hnext :
        higham9_7_PartialPivotGEPPUTrace 1
          (luFirstSchurComplement
            (higham9_2_rowPermutedMatrix middleAccumCounterS1
              (higham9_7_firstPivotRowSwap (1 : Fin 2))))
          (fun _ _ : Fin 1 => (1101 / 1100 : ℝ)) := by
      rw [hstage2]
      exact htail1
    have h := higham9_7_PartialPivotGEPPUTrace.step hchoice1 hpivot1 hnext
    convert h using 1 <;>
      funext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [middleAccumCounterU2, luFirstStepU,
        higham9_2_rowPermutedMatrix, higham9_7_firstPivotRowSwap,
        middleAccumCounterS1]
  have hnext :
      higham9_7_PartialPivotGEPPUTrace 2
        (luFirstSchurComplement
          (higham9_2_rowPermutedMatrix middleAccumCounterT
            (higham9_7_firstPivotRowSwap (1 : Fin 3))))
        middleAccumCounterU2 := by
    rw [hstage1]
    exact htail2
  have h := higham9_7_PartialPivotGEPPUTrace.step hchoice0 hpivot0 hnext
  convert h using 1 <;>
    funext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [middleAccumCounterU, middleAccumCounterU2, luFirstStepU,
      higham9_2_rowPermutedMatrix, higham9_7_firstPivotRowSwap,
      middleAccumCounterT]

/-- Compact source-discrepancy certificate: a genuine two-adjacent-swap GEPP
trace has the displayed exact permuted LU factors, yet its accumulated lower
factor violates the `∞`-norm-two step used in the cited proof of Theorem 11.8. -/
theorem middleAccumCounter_actual_GEPP_refutes_infNorm_two :
    higham9_7_PartialPivotGEPPUTrace 3
      middleAccumCounterT middleAccumCounterU ∧
    higham9_2_PermutedLUFactSpec 3 middleAccumCounterT
      middleAccumCounterL middleAccumCounterU middleAccumCounterSigma ∧
    ¬ infNorm middleAccumCounterL ≤ 2 :=
  ⟨middleAccumCounter_GEPP_trace, middleAccumCounter_exact_permuted_lu,
    middleAccumCounter_not_infNorm_le_two⟩

/-- Source-domain form of the proof discrepancy in the analysis cited for
Theorem 11.8.  A symmetric tridiagonal matrix following the literal adjacent-
pivot GEPP path has the displayed exact accumulated lower factor, yet that
factor violates the claimed infinity-norm bound `‖M‖∞ ≤ 2`. -/
theorem middleAccumCounter_source_domain_refutes_infNorm_two :
    (∀ i j : Fin 3,
      middleAccumCounterT i j = middleAccumCounterT j i) ∧
    IsTridiagonal 3 middleAccumCounterT ∧
    higham9_7_PartialPivotGEPPUTrace 3
      middleAccumCounterT middleAccumCounterU ∧
    higham9_2_PermutedLUFactSpec 3 middleAccumCounterT
      middleAccumCounterL middleAccumCounterU middleAccumCounterSigma ∧
    ¬ infNorm middleAccumCounterL ≤ 2 :=
  ⟨middleAccumCounterT_symm, middleAccumCounterT_tridiagonal,
    middleAccumCounter_GEPP_trace, middleAccumCounter_exact_permuted_lu,
    middleAccumCounter_not_infNorm_le_two⟩

end NumStability.Ch11Closure.AasenDirect
