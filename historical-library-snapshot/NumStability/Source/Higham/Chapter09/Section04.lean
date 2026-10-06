import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Budgets
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02

/-!
# Higham Chapter 9: Section04

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 3.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Theorem 9.5**, source-shaped bound after supplying the bridge from
Higham's growth factor to the repository `∞`-norm of `U_hat`. -/
theorem higham9_5_wilkinson_source_bound_of_growth_bridge (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (ρ : ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1)
    (hU_growth : infNorm U_hat ≤ ↑n * ρ * infNorm A) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤ (↑n) ^ 2 * gamma fp (3 * n) * ρ * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    wilkinson_normwise_infNorm_tight fp n hn_pos A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3 hL_bound
  refine ⟨ΔA, ?_, hΔA_eq⟩
  have hγn : 0 ≤ gamma fp (3 * n) * (n : ℝ) :=
    mul_nonneg (gamma_nonneg fp hn3) (Nat.cast_nonneg' n)
  calc
    infNorm ΔA ≤ gamma fp (3 * n) * ↑n * infNorm U_hat := hΔA_bound
    _ ≤ gamma fp (3 * n) * ↑n * (↑n * ρ * infNorm A) :=
        mul_le_mul_of_nonneg_left hU_growth hγn
    _ = (↑n) ^ 2 * gamma fp (3 * n) * ρ * infNorm A := by
        ring

/-- **Theorem 9.5**, source-shaped max-entry growth-factor form.

This removes the free norm-growth bridge hypothesis from
`higham9_5_wilkinson_source_bound_of_growth_bridge`: a bound on Higham's
max-entry growth factor for the final `U_hat` implies the required
`∞`-norm bridge by elementary row-sum/max-entry inequalities. -/
theorem higham9_5_wilkinson_source_bound_of_entry_growth (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (ρ : ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (hρ : 0 ≤ ρ)
    (hρU : growthFactorEntry hn_pos A U_hat hAmax ≤ ρ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤ (↑n) ^ 2 * gamma fp (3 * n) * ρ * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_growth_bridge fp n hn_pos A L_hat U_hat b ρ
    hL_diag hU_diag hLU hn hn3 hL_bound
    (infNorm_le_card_mul_growthFactorEntry_bound hn_pos A U_hat ρ hAmax hρ hρU)

/-- **Theorem 9.5 / equation (9.10)**, source-shaped GEPP normwise
backward-error bound for an explicit partial-pivoting `U` trace.  This
instantiates the max-entry growth hypothesis in
`higham9_5_wilkinson_source_bound_of_entry_growth` from the local exact
Theorem 9.7 trace bound `rho_n^p <= 2^(n-1)`. -/
theorem higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_entry_growth fp n hn_pos A L_hat U_hat b
    ((2 : ℝ) ^ (n - 1)) hAmax
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1))
    (higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two
      hn_pos A U_hat hAmax htrace)
    hL_diag hU_diag hLU hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, row-pivoted GEPP certificate form.

If a supplied row-pivoted backward-error certificate computes the same `U_hat`
as an explicit recursive partial-pivoting trace, then Wilkinson's normwise
source bound applies to the original system after permuting the right-hand side.
The theorem deliberately keeps the GEPP trace, pivoted certificate, nonzero
pivots, and multiplier bound as visible hypotheses; it does not construct them
from a concrete floating-point implementation. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  classical
  let bP : Fin n → ℝ := fun i => b (sigma i)
  let Aperm : Fin n → Fin n → ℝ := higham9_2_rowPermutedMatrix A sigma
  have hApermmax : 0 < maxEntryNorm hn_pos Aperm := by
    simpa [Aperm, higham9_2_rowPermutedMatrix_maxEntryNorm hn_pos A hLU.perm]
      using hAmax
  have hgrowth :
      growthFactorEntry hn_pos Aperm U_hat hApermmax ≤
        (2 : ℝ) ^ (n - 1) := by
    have htrace_growth :
        growthFactorEntry hn_pos A U_hat hAmax ≤ (2 : ℝ) ^ (n - 1) :=
      higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two
        hn_pos A U_hat hAmax htrace
    unfold growthFactorEntry at htrace_growth ⊢
    simpa [Aperm, higham9_2_rowPermutedMatrix_maxEntryNorm hn_pos A hLU.perm]
      using htrace_growth
  have hL_diag : ∀ i : Fin n, L_hat i i ≠ 0 := by
    intro i
    rw [hLU.L_diag i]
    norm_num
  obtain ⟨ΔPA, hΔPA_bound, hΔPA_eq⟩ :=
    higham9_5_wilkinson_source_bound_of_entry_growth fp n hn_pos Aperm
      L_hat U_hat bP ((2 : ℝ) ^ (n - 1)) hApermmax
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 1))
      hgrowth hL_diag hU_diag
      (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU) hn hn3 hL_bound
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.perm
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔPA (eSigma.symm i) j
  refine ⟨ΔA, ?_, ?_⟩
  · have hrow_eq :
        higham9_2_rowPermutedMatrix ΔA sigma = ΔPA := by
      funext i j
      have hsigma_left : eSigma.symm (sigma i) = i := by
        change eSigma.symm (eSigma i) = i
        exact Equiv.symm_apply_apply eSigma i
      simp [ΔA, higham9_2_rowPermutedMatrix, hsigma_left]
    have hΔnorm : infNorm ΔA = infNorm ΔPA := by
      have hpermΔ := higham9_2_rowPermutedMatrix_infNorm ΔA hLU.perm
      rw [hrow_eq] at hpermΔ
      exact hpermΔ.symm
    have hAperm_inf : infNorm Aperm = infNorm A := by
      simpa [Aperm] using higham9_2_rowPermutedMatrix_infNorm A hLU.perm
    calc
      infNorm ΔA = infNorm ΔPA := hΔnorm
      _ ≤ (↑n) ^ 2 * gamma fp (3 * n) *
            (2 : ℝ) ^ (n - 1) * infNorm Aperm := hΔPA_bound
      _ = (↑n) ^ 2 * gamma fp (3 * n) *
            (2 : ℝ) ^ (n - 1) * infNorm A := by
          rw [hAperm_inf]
  · intro i
    have hrow := hΔPA_eq (eSigma.symm i)
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    calc
      ∑ j : Fin n, (A i j + ΔA i j) *
          (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j
          = ∑ j : Fin n, (Aperm (eSigma.symm i) j + ΔPA (eSigma.symm i) j) *
              (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j := by
            apply Finset.sum_congr rfl
            intro j _
            simp [Aperm, higham9_2_rowPermutedMatrix, ΔA, hsigma_symm]
      _ = bP (eSigma.symm i) := hrow
      _ = b i := by simp [bP, hsigma_symm]

/-- **Theorem 9.5 / equation (9.10)**, dense-loop partial-pivoting bridge.

This source-facing wrapper replaces the free pivoted backward-error certificate
in `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace` by a
literal dense Doolittle certificate for the row-permuted matrix `PA`.  The
actual construction of the partial-pivoting trace and the proof that it
produces this dense-loop certificate remain visible hypotheses. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hC : higham9_2_DoolittleDenseLoopCertificate n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat fp)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag
    (higham9_2_permutedDenseLoopCertificate_to_PermutedLUBackwardError
      hsigma hn hC)
    hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, absolute-budget partial-pivoting bridge.

This is the same source-facing Theorem 9.5 wrapper as the dense-loop bridge,
but with the next lower implementation layer: absolute residual budgets for a
dense Doolittle run on `PA` plus their visible compression fields. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (BU BL : Fin n → Fin n → ℝ)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat fp BU BL)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag
    (higham9_2_permutedAbsBudgetCertificate_to_PermutedLUBackwardError
      hsigma hn hC)
    hn hn3 hL_bound

/-- **Theorem 9.5 / Algorithm 9.2**, rectangular rounded-stage
partial-pivoting bridge.

This connects the square-specialized rectangular rounded Doolittle trace for
the row-permuted matrix `PA` to the row-pivoted Wilkinson source bound.  The
GEPP trace and the proof that the rounded rectangular stage trace matches the
chosen pivot sequence remain visible hypotheses. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_rectRoundedStageTrace
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hT : higham9_2_RectDoolittleRoundedStageTrace
      (Nat.le_refl n) (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat fp)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag hsigma
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate
      (higham9_2_rectRoundedStageTrace_to_rectDenseLoopCertificate
        hT hU_diag hn hU_budget_le hL_budget_le))
    hn hn3 hL_bound

/-- **Theorem 9.5 / Algorithm 9.2**, executable rectangular rounded-loop
partial-pivoting bridge.

This specializes the rectangular rounded-stage bridge to the concrete
rectangular rounded Doolittle loop run on the row-permuted matrix `PA`.  The
loop supplies the rounded-stage trace; the remaining nonzero-pivot,
budget-dominance, multiplier-bound, and GEPP trace alignment hypotheses remain
explicit. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_rectRoundedLoop
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
        (higham9_2_rowPermutedMatrix A sigma)))
    (hU_diag : ∀ i : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k k|)
    (hL_bound : ∀ i j : Fin n,
      |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) i j| ≤ 1) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma)
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma)
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_rectRoundedStageTrace
    fp n hn_pos A
    (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma))
    (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma))
    sigma b hAmax htrace hU_diag hsigma
    (higham9_2_rectRoundedLoopStageTrace fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma))
    hn hn3 hU_budget_le hL_budget_le hL_bound

/-- **Theorem 9.5 / equation (9.10)**, literal-source-budget
partial-pivoting bridge.

This exposes the source-level rounded Doolittle hypotheses for the
row-permuted matrix `PA` directly at the Wilkinson normwise bound.  The
concrete GEPP trace-to-loop construction remains a visible hypothesis through
`htrace` and the literal row-permuted Doolittle equations. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_literalSourceBudgets
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_flDoolittleUEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_flDoolittleLEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUAbsBudget fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLAbsBudget fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag hsigma
    (doolittleUAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (doolittleLAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (higham9_2_absBudgetCertificate_of_literal_doolittle_source_budgets
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_budget_le hL_budget_le)
    hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, component-dominance
partial-pivoting bridge.

This is the row-pivoted Wilkinson endpoint with the dense Doolittle
absolute-budget certificate discharged from visible componentwise work/product
and rounded-numerator dominance hypotheses over the row-permuted matrix `PA`. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_componentDominance
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_flDoolittleUEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_flDoolittleLEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_work_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUWorkAbs fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        |U_hat k j|)
    (hU_prod_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUProductAbs fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        |U_hat k j|)
    (hL_work_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLWorkAbs fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_prod_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLProductAbs fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLNumeratorAbs fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag hsigma
    (doolittleUAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (doolittleLAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (higham9_2_absBudgetCertificate_of_literal_doolittle_component_dominance
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_work_le hU_prod_le hL_work_le hL_prod_le hL_num_le)
    hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, exact-product margin
partial-pivoting bridge.

This exposes the no-cancellation exact-product margin hypotheses for the
row-permuted dense Doolittle run directly at the row-pivoted Wilkinson
normwise source-bound endpoint. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductMargins
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_flDoolittleUEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_flDoolittleLEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |higham9_2_rowPermutedMatrix A sigma k j| + (1 + fp.u) *
          doolittleUProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |higham9_2_rowPermutedMatrix A sigma i k| + (1 + fp.u) *
          doolittleLProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLNumeratorAbs fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag hsigma
    (doolittleUAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (doolittleLAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_margins
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_margin hL_margin hL_num_le)
    hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, exact-product numerator-margin
partial-pivoting bridge.

This variant replaces the lower rounded-numerator dominance hypothesis in the
exact-product bridge by the source-visible exact numerator margin for the
row-permuted matrix `PA`. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductNumeratorMargins
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_flDoolittleUEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_flDoolittleLEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |higham9_2_rowPermutedMatrix A sigma k j| + (1 + fp.u) *
          doolittleUProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |higham9_2_rowPermutedMatrix A sigma i k| + (1 + fp.u) *
          doolittleLProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_margin : ∀ i k : Fin n, k.val < i.val →
      (|higham9_2_rowPermutedMatrix A sigma i k| +
          doolittleLProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k) +
        (gamma fp k.val *
            (|higham9_2_rowPermutedMatrix A sigma i k| + (1 + fp.u) *
              doolittleLProductAbs fp n
                (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k) +
          fp.u * doolittleLProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k) ≤
        |L_hat i k * U_hat k k|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag hsigma
    (doolittleUAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (doolittleLAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_margin hL_margin hL_num_margin)
    hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, exact-target-gap
partial-pivoting bridge.

This row-pivoted wrapper discharges the dense Doolittle absolute-budget
certificate from exact-target gap hypotheses for the literal rounded updates
on `PA`. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactTargetGaps
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_flDoolittleUEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_flDoolittleLEntry fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hsigma : IsPermutation n sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |higham9_2_rowPermutedMatrix A sigma k j| + (1 + fp.u) *
          doolittleUProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j ≤
        |doolittleUExactTarget n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |higham9_2_rowPermutedMatrix A sigma i k| + (1 + fp.u) *
          doolittleLProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |doolittleLExactTarget n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|higham9_2_rowPermutedMatrix A sigma i k| +
          doolittleLProductAbs fp n
            (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k ≤
        |doolittleLExactTarget n
          (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat i k|)
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag hsigma
    (doolittleUAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (doolittleLAbsBudget fp n
      (higham9_2_rowPermutedMatrix A sigma) L_hat U_hat)
    (higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_gap hL_gap hL_num_gap)
    hn hn3 hL_bound

/-- **Theorem 9.5 / equation (9.10)**, exact row-pivoted certificate bridge.

This variant replaces the pivoted backward-error certificate in
`higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace` by an
exact `PA = LU` certificate.  The residual is zero and is weakened to
`gamma_n` only to reuse the common Wilkinson source-bound surface.  The
recursive GEPP `U` trace, nonzero pivots, and multiplier bound remain visible
hypotheses. -/
theorem higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (htrace : higham9_7_PartialPivotGEPPUTrace n A U_hat)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_PermutedLUFactSpec n A L_hat U_hat sigma)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤
        (↑n) ^ 2 * gamma fp (3 * n) *
          (2 : ℝ) ^ (n - 1) * infNorm A) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace
    fp n hn_pos A L_hat U_hat sigma b hAmax htrace hU_diag
    (higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma hn hLU)
    hn hn3 hL_bound

/-- **Theorem 9.8**, product lower-bound form:
`1 ≤ ρ^n α^n β^n`, with max-entry norms for `α` and `β`. -/
theorem higham9_8_growth_factor_product_lower_bound {n : ℕ} (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℝ) (hA : 0 < maxEntryNorm hn A)
    (det_A det_Ainv : ℝ)
    (hdet_prod : |det_A| * |det_Ainv| = 1)
    (hdet : |det_A| ≤ ∏ k : Fin n, |U k k|)
    (hdet_inv : |det_Ainv| ≤ (maxEntryNorm hn A_inv) ^ n) :
    1 ≤ (growthFactorEntry hn A U hA) ^ n *
        (maxEntryNorm hn A) ^ n * (maxEntryNorm hn A_inv) ^ n :=
  growth_factor_product_lower_bound hn A A_inv U hA det_A det_Ainv
    hdet_prod hdet hdet_inv

/-- **Theorem 9.8**, real max-entry proof of `θ ≤ n`.
For `α = maxEntry(A)` and `β = maxEntry(A⁻¹)`, a row inverse identity
`∑ⱼ aᵢⱼ (A⁻¹)ⱼᵢ = 1` implies `(αβ)⁻¹ ≤ n`. -/
theorem higham9_8_theta_le_card_real {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (i : Fin n)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤ n :=
  theta_le_card_of_inverse_row_identity hn A A_inv i hA hAinv hrow

/-- **Theorem 9.8**, real max-entry `ρ ≥ θ` bridge.
If the final pivot supplies Higham's inverse-entry witness
`|u|⁻¹ ≤ β` and `|u|` is bounded by the largest entry reached in `U`,
then `growthFactorEntry A U ≥ (αβ)⁻¹`. -/
theorem higham9_8_growth_factor_ge_theta_real {n : ℕ} (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv)
    (u : ℝ) (hu_pos : 0 < |u|)
    (hu_entry : |u| ≤ maxEntryNorm hn U)
    (hu_inv_le : |u|⁻¹ ≤ maxEntryNorm hn A_inv) :
    1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) ≤
      growthFactorEntry hn A U hA :=
  growthFactorEntry_ge_inverse_entry_theta hn A A_inv U hA hAinv
    u hu_pos hu_entry hu_inv_le

/-- **Theorem 9.8**, final-pivot inverse-entry identity for an exact no-pivot
LU certificate.

If `A = L U` with `L` unit lower triangular and `U` upper triangular, and
`A_inv` is a right inverse of `A`, then the final pivot `u_nn` and the final
diagonal entry of `A_inv` satisfy `u_nn * (A_inv)_nn = 1`.  This is the
local algebraic content of Higham's displayed identity (9.11) before adding
row/column permutations. -/
theorem higham9_8_finalPivot_mul_inverse_entry_eq_one {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLU : LUFactSpec (m + 1) A L U)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (Fin.last m) (Fin.last m) = 1 := by
  classical
  let n := m + 1
  let last : Fin n := Fin.last m
  let Y : Fin n → Fin n → ℝ := matMul n U A_inv
  have hLU_product : matMul n L U = A := by
    ext i j
    exact hLU.product_eq i j
  have hYRight : IsRightInverse n L Y := by
    intro i j
    have hassoc := congrFun (congrFun (matMul_assoc n L U A_inv) i) j
    have hright := hRight i j
    calc
      ∑ k : Fin n, L i k * Y k j
          = matMul n L Y i j := rfl
      _ = matMul n (matMul n L U) A_inv i j := by
            simpa [Y] using hassoc.symm
      _ = matMul n A A_inv i j := by rw [hLU_product]
      _ = ∑ k : Fin n, A i k * A_inv k j := rfl
      _ = if i = j then 1 else 0 := hright
  have hLT_transpose :
      ∀ i j : Fin n, j.val < i.val →
        finiteTranspose L i j = 0 := by
    intro i j hji
    exact hLU.L_upper_zero j i (by simpa [finiteTranspose] using hji)
  have hL_diag_ne : ∀ i : Fin n, finiteTranspose L i i ≠ 0 := by
    intro i
    simp [finiteTranspose, hLU.L_diag i]
  have hYLeftT :
      IsLeftInverse n (finiteTranspose L) (finiteTranspose Y) :=
    isLeftInverse_finiteTranspose_of_isRightInverse hYRight
  have hYt_upper :
      ∀ i j : Fin n, j.val < i.val →
        finiteTranspose Y i j = 0 :=
    inv_upper_tri n (finiteTranspose L) (finiteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT
  have hYt_diag :
      ∀ i : Fin n, finiteTranspose Y i i =
        1 / finiteTranspose L i i :=
    inv_diag_entry n (finiteTranspose L) (finiteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT hYt_upper
  have hY_last_diag : Y last last = 1 := by
    have h := hYt_diag last
    simpa [finiteTranspose, hLU.L_diag last] using h
  have hY_last_last :
      Y last last =
        U last last * A_inv last last := by
    unfold Y matMul
    exact Finset.sum_eq_single last
      (fun k _ hk => by
        have hk_val_ne : k.val ≠ last.val := by
          intro hval
          exact hk (Fin.ext hval)
        have hk_lt : k.val < last.val := by
          have hlast_val : last.val = m := by simp [last]
          have hk_le : k.val ≤ m := Nat.le_of_lt_succ k.isLt
          have hk_ne_m : k.val ≠ m := by
            intro hkm
            exact hk_val_ne (by simpa [hlast_val] using hkm)
          have hk_lt_m : k.val < m := lt_of_le_of_ne hk_le hk_ne_m
          simpa [hlast_val] using hk_lt_m
        rw [hLU.U_lower_zero last k (by simpa [last] using hk_lt), zero_mul])
      (fun hnot => (hnot (Finset.mem_univ last)).elim)
  rw [hY_last_last] at hY_last_diag
  exact hY_last_diag

/-- **Theorem 9.8**, final-pivot inverse-entry max-entry witness for an exact
no-pivot LU certificate.

This discharges the witness hypothesis of
`higham9_8_growth_factor_ge_theta_real` directly from `A = L U` and
`A A_inv = I`, for the unpermuted exact-LU case. -/
theorem higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLU : LUFactSpec (m + 1) A L U)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    |U (Fin.last m) (Fin.last m)|⁻¹ ≤
      maxEntryNorm (Nat.succ_pos m) A_inv := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv last last = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one A A_inv L U hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hentry_eq : A_inv last last = u⁻¹ := by
    field_simp [hu_ne]
    simpa [mul_comm] using hprod
  calc
    |U (Fin.last m) (Fin.last m)|⁻¹
        = |u|⁻¹ := by simp [u, last]
    _ = |u⁻¹| := by rw [abs_inv]
    _ = |A_inv last last| := by rw [← hentry_eq]
    _ ≤ maxEntryNorm (Nat.succ_pos m) A_inv :=
        entry_le_maxEntryNorm (Nat.succ_pos m) A_inv last last

/-- **Theorem 9.8**, unpermuted exact-LU lower bound `rho >= theta`.

For an exact no-pivot LU certificate and a visible right inverse of `A`, the
final-pivot identity proves Higham's inverse-entry witness and therefore
`growthFactorEntry(A,U) >= (alpha beta)^{-1}`.  The remaining fully general
source theorem still needs the row/column-permuted `P A Q = L U` trace. -/
theorem higham9_8_growth_factor_ge_theta_of_lu_right_inverse {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hLU : LUFactSpec (m + 1) A L U)
    (hRight : IsRightInverse (m + 1) A A_inv)
    (hA : 0 < maxEntryNorm (Nat.succ_pos m) A)
    (hAinv : 0 < maxEntryNorm (Nat.succ_pos m) A_inv) :
    1 / (maxEntryNorm (Nat.succ_pos m) A *
        maxEntryNorm (Nat.succ_pos m) A_inv) ≤
      growthFactorEntry (Nat.succ_pos m) A U hA := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv last last = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one A A_inv L U hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hu_pos : 0 < |u| := abs_pos.mpr hu_ne
  have hu_entry :
      |u| ≤ maxEntryNorm (Nat.succ_pos m) U := by
    simpa [u, last] using
      entry_le_maxEntryNorm (Nat.succ_pos m) U last last
  have hu_inv_le :
      |u|⁻¹ ≤ maxEntryNorm (Nat.succ_pos m) A_inv := by
    simpa [u, last] using
      higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm
        A A_inv L U hLU hRight
  exact higham9_8_growth_factor_ge_theta_real (Nat.succ_pos m) A A_inv U
    hA hAinv u hu_pos hu_entry hu_inv_le

/-- **Theorem 9.8 / equation (9.11)**, final-pivot identity for an explicit
complete-pivoting certificate `P A Q = L U`.

For a source `PAQ = LU` certificate and a visible right inverse of the original
matrix `A`, the final pivot satisfies
`u_nn * (A_inv)_(tau n, sigma n) = 1`. -/
theorem higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU : higham9_2_CompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (tau (Fin.last m)) (sigma (Fin.last m)) = 1 := by
  classical
  let B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    higham9_2_rowColPermutedMatrix A sigma tau
  let B_inv : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i j => A_inv (tau i) (sigma j)
  have hBRight : IsRightInverse (m + 1) B B_inv :=
    higham9_2_rowColPermutedMatrix_right_inverse hLU.2.perm hLU.1 hRight
  have hBLU : LUFactSpec (m + 1) B L U :=
    higham9_2_completePermutedLUFactSpec_to_LUFactSpec hLU
  simpa [B, B_inv] using
    higham9_8_finalPivot_mul_inverse_entry_eq_one B B_inv L U hBLU hBRight

/-- **Theorem 9.8**, final-pivot inverse-entry max-entry witness for an
explicit complete-pivoting certificate `P A Q = L U`. -/
theorem higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm_of_completePermutedLUFactSpec
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU : higham9_2_CompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : IsRightInverse (m + 1) A A_inv) :
    |U (Fin.last m) (Fin.last m)|⁻¹ ≤
      maxEntryNorm (Nat.succ_pos m) A_inv := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv (tau last) (sigma last) = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
        A A_inv L U sigma tau hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hentry_eq : A_inv (tau last) (sigma last) = u⁻¹ := by
    field_simp [hu_ne]
    simpa [mul_comm] using hprod
  calc
    |U (Fin.last m) (Fin.last m)|⁻¹
        = |u|⁻¹ := by simp [u, last]
    _ = |u⁻¹| := by rw [abs_inv]
    _ = |A_inv (tau last) (sigma last)| := by rw [← hentry_eq]
    _ ≤ maxEntryNorm (Nat.succ_pos m) A_inv :=
        entry_le_maxEntryNorm (Nat.succ_pos m) A_inv (tau last) (sigma last)

/-- **Theorem 9.8**, complete-pivoting exact-LU lower bound `rho >= theta`.

This closes the equation (9.11) inverse-entry instantiation for an explicit
`P A Q = L U` certificate.  It still does not construct the complete-pivoting
trace that produces such a certificate. -/
theorem higham9_8_growth_factor_ge_theta_of_completePermutedLUFactSpec_right_inverse
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU : higham9_2_CompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : IsRightInverse (m + 1) A A_inv)
    (hA : 0 < maxEntryNorm (Nat.succ_pos m) A)
    (hAinv : 0 < maxEntryNorm (Nat.succ_pos m) A_inv) :
    1 / (maxEntryNorm (Nat.succ_pos m) A *
        maxEntryNorm (Nat.succ_pos m) A_inv) ≤
      growthFactorEntry (Nat.succ_pos m) A U hA := by
  classical
  let last : Fin (m + 1) := Fin.last m
  let u : ℝ := U last last
  have hprod :
      u * A_inv (tau last) (sigma last) = 1 := by
    simpa [u, last] using
      higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
        A A_inv L U sigma tau hLU hRight
  have hu_ne : u ≠ 0 := by
    intro hu
    rw [hu] at hprod
    norm_num at hprod
  have hu_pos : 0 < |u| := abs_pos.mpr hu_ne
  have hu_entry :
      |u| ≤ maxEntryNorm (Nat.succ_pos m) U := by
    simpa [u, last] using
      entry_le_maxEntryNorm (Nat.succ_pos m) U last last
  have hu_inv_le :
      |u|⁻¹ ≤ maxEntryNorm (Nat.succ_pos m) A_inv := by
    simpa [u, last] using
      higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm_of_completePermutedLUFactSpec
        A A_inv L U sigma tau hLU hRight
  exact higham9_8_growth_factor_ge_theta_real (Nat.succ_pos m) A A_inv U
    hA hAinv u hu_pos hu_entry hu_inv_le

/-- AM-GM consequence: for nonnegative reals `z i` (`i : Fin n`) whose sum is
`n`, the product `∏ z i ≤ 1`.  This is the arithmetic core of Hadamard's
determinant inequality applied to a correlation matrix. -/
theorem higham9_amgm_prod_le_one_of_sum_eq_card {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (hsum : ∑ i, z i = n) :
    ∏ i, z i ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ (1 / (n : ℝ)) := by
    intro i _; positivity
  have hw' : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (1 / (n : ℝ))) z hw hw' (fun i _ => hz i)
  have hrhs : ∑ i : Fin n, (1 / (n : ℝ)) * z i = 1 := by
    rw [← Finset.mul_sum, hsum]; field_simp
  rw [hrhs] at hgm
  have hprodnn : 0 ≤ ∏ i, z i ^ (1 / (n : ℝ)) := by
    apply Finset.prod_nonneg; intro i _; exact Real.rpow_nonneg (hz i) _
  have hpow : (∏ i, z i ^ (1 / (n : ℝ))) ^ n = ∏ i, z i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast (z i ^ (1 / (n : ℝ))) n, ← Real.rpow_mul (hz i)]
    rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  calc ∏ i, z i = (∏ i, z i ^ (1 / (n : ℝ))) ^ n := hpow.symm
    _ ≤ 1 ^ n := by gcongr
    _ = 1 := one_pow n

/-- **Hadamard's inequality for positive definite matrices**: the determinant of
a real positive definite matrix is at most the product of its diagonal entries.
Proof via congruence to a unit-diagonal (correlation) matrix, whose eigenvalues
are nonnegative and sum to `n`, so their product (the determinant) is `≤ 1`. -/
theorem higham9_posDef_det_le_prod_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) : M.det ≤ ∏ i, M i i := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; simp
  have hpos : ∀ i, 0 < M i i := fun i => hM.diag_pos
  set d : Fin n → ℝ := fun i => (Real.sqrt (M i i))⁻¹ with hd
  set D : Matrix (Fin n) (Fin n) ℝ := diagonal d with hD
  have hdsq : ∀ i, d i * d i = (M i i)⁻¹ := by
    intro i
    have hs : Real.sqrt (M i i) * Real.sqrt (M i i) = M i i :=
      Real.mul_self_sqrt (hpos i).le
    simp only [hd]
    rw [← mul_inv, hs]
  set C : Matrix (Fin n) (Fin n) ℝ := D * M * D with hC
  have hCij : ∀ i j, C i j = d i * M i j * d j := by
    intro i j
    simp [hC, hD, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq]
  have hCii : ∀ i, C i i = 1 := by
    intro i
    rw [hCij i i]
    calc d i * M i i * d i = d i * d i * M i i := by ring
      _ = (M i i)⁻¹ * M i i := by rw [hdsq i]
      _ = 1 := inv_mul_cancel₀ (hpos i).ne'
  have hstar : (star d) = d := by ext i; simp
  have hCpsd : C.PosSemidef := by
    have h1 := hM.posSemidef.conjTranspose_mul_mul_same D
    rw [hD, diagonal_conjTranspose, hstar] at h1
    rw [hC, hD]; exact h1
  have hCherm : C.IsHermitian := hCpsd.1
  have hprodd : (∏ i, d i) * (∏ i, d i) = (∏ i, M i i)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i _ => hdsq i)
  have hdetC : C.det = M.det * (∏ i, M i i)⁻¹ := by
    rw [hC, det_mul, det_mul, det_diagonal]
    calc (∏ i, d i) * M.det * (∏ i, d i)
        = M.det * ((∏ i, d i) * (∏ i, d i)) := by ring
      _ = M.det * (∏ i, M i i)⁻¹ := by rw [hprodd]
  have hdetC_eig : C.det = ∏ i, hCherm.eigenvalues i := by
    rw [hCherm.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC_eig : C.trace = ∑ i, hCherm.eigenvalues i := by
    rw [hCherm.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC : C.trace = (n : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.sum_congr rfl (fun i _ => hCii i)]
    simp
  have hsum_eig : ∑ i, hCherm.eigenvalues i = (n : ℝ) := by
    rw [← htraceC_eig, htraceC]
  have hprod_eig : ∏ i, hCherm.eigenvalues i ≤ 1 :=
    higham9_amgm_prod_le_one_of_sum_eq_card hn _
      (fun i => hCpsd.eigenvalues_nonneg i) hsum_eig
  have hdetC_le : C.det ≤ 1 := by rw [hdetC_eig]; exact hprod_eig
  have hprodpos : 0 < ∏ i, M i i := Finset.prod_pos (fun i _ => hpos i)
  rw [hdetC] at hdetC_le
  have h := mul_le_mul_of_nonneg_right hdetC_le hprodpos.le
  rwa [mul_assoc, inv_mul_cancel₀ hprodpos.ne', mul_one, one_mul] at h

/-- **Hadamard's determinant inequality (real, squared row form)**: for any real
square matrix, the square of the determinant is at most the product of the
squared Euclidean row norms.  This is the form used to bound growth factors in
the section-9.4 complete-pivoting analysis, applied to leading submatrices. -/
theorem higham9_hadamard_det_sq_le_prod_row_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.det) ^ 2 ≤ ∏ i, ∑ j, (A i j) ^ 2 := by
  have hrhs_nonneg : 0 ≤ ∏ i, ∑ j, (A i j) ^ 2 :=
    Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  rcases eq_or_ne A.det 0 with h0 | h0
  · rw [h0]; simpa using hrhs_nonneg
  have hAT : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A
  set G := A * Aᵀ with hG
  have hGpsd : G.PosSemidef := by
    have h := posSemidef_self_mul_conjTranspose A
    rwa [hAT] at h
  have hAunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h0)
  have hATunit : IsUnit Aᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
    exact isUnit_iff_ne_zero.mpr h0
  have hGpd : G.PosDef := (hGpsd.posDef_iff_isUnit).mpr (hAunit.mul hATunit)
  have hdetG : G.det = (A.det) ^ 2 := by rw [hG, det_mul, det_transpose]; ring
  have hGii : ∀ i, G i i = ∑ j, (A i j) ^ 2 := by
    intro i
    rw [hG, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro j _
    rw [Matrix.transpose_apply]; ring
  have hbound := higham9_posDef_det_le_prod_diag G hGpd
  rw [hdetG] at hbound
  calc (A.det) ^ 2 ≤ ∏ i, G i i := hbound
    _ = ∏ i, ∑ j, (A i j) ^ 2 := Finset.prod_congr rfl (fun i _ => hGii i)

/-- **Hadamard's determinant inequality, max-entry form**:
`(det A)^2 ≤ n^n · (maxEntryNorm A)^(2n)`.  This is the form used in the
section-9.4 complete-pivoting growth analysis: every entry of a leading
submatrix produced by complete pivoting is bounded by the largest entry of the
original matrix, so the squared determinant of each `k × k` leading submatrix is
at most `k^k` times the `2k`-th power of that maximal entry. -/
theorem higham9_hadamard_det_sq_le_pow_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.det) ^ 2 ≤ (n : ℝ) ^ n * (maxEntryNorm hn A) ^ (2 * n) := by
  have h1 := higham9_hadamard_det_sq_le_prod_row_sq A
  have hrow : ∀ i : Fin n,
      ∑ j, (A i j) ^ 2 ≤ (n : ℝ) * (maxEntryNorm hn A) ^ 2 := by
    intro i
    calc ∑ j, (A i j) ^ 2
        ≤ ∑ _j : Fin n, (maxEntryNorm hn A) ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          rw [← sq_abs (A i j)]
          gcongr
          exact entry_le_maxEntryNorm hn A i j
      _ = (n : ℝ) * (maxEntryNorm hn A) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ∏ i, ∑ j, (A i j) ^ 2
      ≤ ∏ _i : Fin n, (n : ℝ) * (maxEntryNorm hn A) ^ 2 := by
    apply Finset.prod_le_prod
    · intro i _; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    · intro i _; exact hrow i
  have h3 : ∏ _i : Fin n, (n : ℝ) * (maxEntryNorm hn A) ^ 2
      = (n : ℝ) ^ n * (maxEntryNorm hn A) ^ (2 * n) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
      mul_comm 2 n]
  calc (A.det) ^ 2 ≤ ∏ i, ∑ j, (A i j) ^ 2 := h1
    _ ≤ ∏ _i : Fin n, (n : ℝ) * (maxEntryNorm hn A) ^ 2 := h2
    _ = (n : ℝ) ^ n * (maxEntryNorm hn A) ^ (2 * n) := h3

/-- **Theorem 9.8 application (section 9.4)**, the scaled-transpose inverse
`n⁻¹ Hᵀ` of a Hadamard matrix. -/
noncomputable def higham9_8_hadamardInv (n : ℕ) (H : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (1 / (n : ℝ)) * H j i

/-- **Theorem 9.8 application (section 9.4)**, the max-entry norm of a Hadamard
matrix is `1`, since every entry has absolute value `1`. -/
theorem higham9_8_hadamard_maxEntryNorm_eq_one {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hpm : ∀ i j : Fin n, |H i j| = 1) :
    maxEntryNorm hn H = 1 := by
  refine le_antisymm ?_ ?_
  · exact maxEntryNorm_le_of_entry_le_bound hn H 1 (fun i j => le_of_eq (hpm i j))
  · calc (1 : ℝ) = |H ⟨0, hn⟩ ⟨0, hn⟩| := (hpm _ _).symm
      _ ≤ maxEntryNorm hn H := entry_le_maxEntryNorm hn H _ _

/-- **Theorem 9.8 application (section 9.4)**, the max-entry norm of the
scaled-transpose Hadamard inverse is `1/n`, since every entry has absolute
value `1/n`. -/
theorem higham9_8_hadamardInv_maxEntryNorm_eq_inv {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hpm : ∀ i j : Fin n, |H i j| = 1) :
    maxEntryNorm hn (higham9_8_hadamardInv n H) = 1 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : ∀ i j : Fin n, |higham9_8_hadamardInv n H i j| = 1 / (n : ℝ) := by
    intro i j
    simp only [higham9_8_hadamardInv, abs_mul]
    rw [hpm j i, mul_one, abs_of_nonneg (one_div_nonneg.mpr hnpos.le)]
  refine le_antisymm ?_ ?_
  · exact maxEntryNorm_le_of_entry_le_bound hn _ (1 / (n : ℝ))
      (fun i j => le_of_eq (habs i j))
  · calc 1 / (n : ℝ)
        = |higham9_8_hadamardInv n H ⟨0, hn⟩ ⟨0, hn⟩| := (habs _ _).symm
      _ ≤ maxEntryNorm hn (higham9_8_hadamardInv n H) :=
        entry_le_maxEntryNorm hn _ _ _

/-- **Theorem 9.8 application (section 9.4)**, `n⁻¹ Hᵀ` is a right inverse of a
Hadamard matrix, from the row-orthogonality identity `H Hᵀ = n I`. -/
theorem higham9_8_hadamardInv_isRightInverse {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (horth : ∀ i j : Fin n,
      ∑ k : Fin n, H i k * H j k = if i = j then (n : ℝ) else 0) :
    IsRightInverse n H (higham9_8_hadamardInv n H) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  intro i j
  have hfac : ∑ k : Fin n, H i k * higham9_8_hadamardInv n H k j
      = (1 / (n : ℝ)) * ∑ k : Fin n, H i k * H j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [higham9_8_hadamardInv]
    ring
  rw [hfac, horth i j]
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact one_div_mul_cancel hnpos.ne'
  · simp only [if_neg hij, mul_zero]

/-- **Theorem 9.8 application (section 9.4)**, the Theorem 9.8 lower-bound
candidate `θ = (αβ)⁻¹` equals `n` for a Hadamard matrix and its scaled-transpose
inverse, matching Higham's `ρ_n ≥ n`. -/
theorem higham9_8_hadamard_theta_candidate_eq_card {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hpm : ∀ i j : Fin n, |H i j| = 1) :
    1 / (maxEntryNorm hn H * maxEntryNorm hn (higham9_8_hadamardInv n H))
      = (n : ℝ) := by
  rw [higham9_8_hadamard_maxEntryNorm_eq_one hn H hpm,
    higham9_8_hadamardInv_maxEntryNorm_eq_inv hn H hpm, one_mul, one_div_one_div]

/-- **Theorem 9.8 application (section 9.4)**, Higham's growth-factor bound
`ρ_n ≥ n` for a Hadamard matrix: for any real matrix `H` with `±1` entries and
`H Hᵀ = n I` that admits an LU factorization `H = L U`, the entrywise growth
factor of `U` over `H` is at least `n`.  This instantiates Theorem 9.8
(`higham9_8_growth_factor_ge_theta_of_lu_right_inverse`) with the explicit
inverse `n⁻¹ Hᵀ`, where `θ = (αβ)⁻¹ = n`. -/
theorem higham9_8_hadamard_growthFactorEntry_ge_card_of_lu_right_inverse
    {m : ℕ} (H L U : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hpm : ∀ i j : Fin (m + 1), |H i j| = 1)
    (horth : ∀ i j : Fin (m + 1),
      ∑ k : Fin (m + 1), H i k * H j k = if i = j then ((m + 1 : ℕ) : ℝ) else 0)
    (hLU : LUFactSpec (m + 1) H L U)
    (hApos : 0 < maxEntryNorm (Nat.succ_pos m) H) :
    ((m + 1 : ℕ) : ℝ) ≤ growthFactorEntry (Nat.succ_pos m) H U hApos := by
  have hcard : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hAinvpos :
      0 < maxEntryNorm (Nat.succ_pos m) (higham9_8_hadamardInv (m + 1) H) := by
    rw [higham9_8_hadamardInv_maxEntryNorm_eq_inv (Nat.succ_pos m) H hpm]
    exact one_div_pos.mpr hcard
  have hright : IsRightInverse (m + 1) H (higham9_8_hadamardInv (m + 1) H) :=
    higham9_8_hadamardInv_isRightInverse (Nat.succ_pos m) H horth
  have hbridge :=
    higham9_8_growth_factor_ge_theta_of_lu_right_inverse H
      (higham9_8_hadamardInv (m + 1) H) L U hLU hright hApos hAinvpos
  rwa [higham9_8_hadamard_theta_candidate_eq_card (Nat.succ_pos m) H hpm] at hbridge

/-- **Equation (9.12)**, the real sine matrix
`S_n = sqrt(2/(n+1)) * (sin(i*j*pi/(n+1)))`, with the source's one-based
indices represented by `i.val + 1` and `j.val + 1`.  This is the matrix used in
the complete-pivoting lower-bound discussion and Problem 9.11; the sine
orthogonality/inverse certificate is proved below, while the complete-pivoting
growth witness remains a separate open target. -/
noncomputable def higham9_12_sineMatrix (n : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    Real.sqrt (2 / ((n : ℝ) + 1)) *
      Real.sin ((((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) * Real.pi) /
        ((n : ℝ) + 1))

/-- **Equation (9.12)**, the sine matrix is symmetric. -/
theorem higham9_12_sineMatrix_symm {n : ℕ} (i j : Fin n) :
    higham9_12_sineMatrix n i j = higham9_12_sineMatrix n j i := by
  unfold higham9_12_sineMatrix
  congr 2
  ring

/-- **Equation (9.12)**, every entry of the sine lower-bound witness has
absolute value at most the source scale factor `sqrt(2/(n+1))`. -/
theorem higham9_12_sineMatrix_entry_abs_le_scale (n : ℕ) (i j : Fin n) :
    |higham9_12_sineMatrix n i j| ≤ Real.sqrt (2 / ((n : ℝ) + 1)) := by
  unfold higham9_12_sineMatrix
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_sin_le_one _)

/-- **Equation (9.12)**, max-entry norm of the sine lower-bound witness is
bounded by the source scale factor `sqrt(2/(n+1))`. -/
theorem higham9_12_sineMatrix_maxEntryNorm_le_scale {n : ℕ} (hn : 0 < n) :
    maxEntryNorm hn (higham9_12_sineMatrix n) ≤
      Real.sqrt (2 / ((n : ℝ) + 1)) := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham9_12_sineMatrix_entry_abs_le_scale n i j

/-- **Equation (9.12)**, the first sine-matrix entry is strictly positive.
This supplies the nonzero max-entry side condition used by the local theta
arithmetic. -/
theorem higham9_12_sineMatrix_zero_zero_pos {n : ℕ} (hn : 0 < n) :
    0 < higham9_12_sineMatrix n ⟨0, hn⟩ ⟨0, hn⟩ := by
  unfold higham9_12_sineMatrix
  have hden_pos : 0 < (n : ℝ) + 1 := by positivity
  have hscale_pos : 0 < Real.sqrt (2 / ((n : ℝ) + 1)) := by
    exact Real.sqrt_pos.2 (by positivity)
  have hangle_pos : 0 < Real.pi / ((n : ℝ) + 1) :=
    div_pos Real.pi_pos hden_pos
  have hangle_lt_pi : Real.pi / ((n : ℝ) + 1) < Real.pi := by
    have hn1 : 1 < (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_lt_succ hn
    rw [div_lt_iff₀ hden_pos]
    nlinarith [Real.pi_pos, hn1]
  have hsin_pos : 0 < Real.sin (Real.pi / ((n : ℝ) + 1)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt_pi
  have harg :
      (((((0 + 1 : ℕ) : ℝ) * ((0 + 1 : ℕ) : ℝ) * Real.pi) /
          ((n : ℝ) + 1))) =
        Real.pi / ((n : ℝ) + 1) := by
    norm_num
  rw [harg]
  exact mul_pos hscale_pos hsin_pos

/-- **Equation (9.12)**, the sine witness has positive max-entry norm for
nonempty matrices. -/
theorem higham9_12_sineMatrix_maxEntryNorm_pos {n : ℕ} (hn : 0 < n) :
    0 < maxEntryNorm hn (higham9_12_sineMatrix n) := by
  have hentry_pos := higham9_12_sineMatrix_zero_zero_pos hn
  have hentry_le :=
    entry_le_maxEntryNorm hn (higham9_12_sineMatrix n) ⟨0, hn⟩ ⟨0, hn⟩
  have habs_pos : 0 < |higham9_12_sineMatrix n ⟨0, hn⟩ ⟨0, hn⟩| :=
    abs_pos.mpr (ne_of_gt hentry_pos)
  exact lt_of_lt_of_le habs_pos hentry_le

/-- **Equation (9.12)** support, even sine-root power:
`exp(i * (2q*pi/N))^N = 1`. -/
theorem higham9_12_sineRoot_pow_even (N q : ℕ) (hN : 0 < N) :
    (Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ N = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (N : ℂ) *
        ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (q : ℂ) * (2 * Real.pi * Complex.I) by
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
          norm_num [Complex.ext_iff]
          field_simp [hNR]]
  simp

/-- **Equation (9.12)** support, odd sine-root power:
`exp(i * ((2q+1)*pi/N))^N = -1`. -/
theorem higham9_12_sineRoot_pow_odd (N q : ℕ) (hN : 0 < N) :
    (Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ N = -1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (N : ℂ) *
        ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (q : ℂ) * (2 * Real.pi * Complex.I) + (Real.pi : ℂ) * Complex.I by
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
          norm_num [Complex.ext_iff]
          field_simp [hNR]]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  simp

/-- **Equation (9.12)** support, a nonzero sine root with frequency
`0 < m < 2N` is not `1`. -/
theorem higham9_12_sineRoot_ne_one (N m : ℕ) (hN : 0 < N)
    (hmpos : 0 < m) (hmlt : m < 2 * N) :
    Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I)) ≠ 1 := by
  intro h
  have h' : Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I)) = Complex.exp 0 := by
    simpa using h
  rw [Complex.exp_eq_exp_iff_exists_int] at h'
  rcases h' with ⟨z, hz⟩
  have him := congrArg Complex.im hz
  have hm_real : ((m : ℝ) * Real.pi / (N : ℝ)) =
      (z : ℝ) * (2 * Real.pi) := by
    simpa [Complex.ext_iff, mul_assoc, mul_comm, mul_left_comm] using him
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hz_eq : (z : ℝ) = (m : ℝ) / (2 * (N : ℝ)) := by
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    field_simp [hNR, hpi] at hm_real ⊢
    nlinarith
  have hz_pos : 0 < (z : ℝ) := by
    rw [hz_eq]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hdenR : 0 < (2 : ℝ) * (N : ℝ) := by positivity
    exact div_pos hmR hdenR
  have hz_int_pos : 0 < z := by
    exact_mod_cast hz_pos
  have hz_ge_one : 1 ≤ z := by omega
  have hz_cast_ge_one : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast hz_ge_one
  have hz_lt_one : (z : ℝ) < 1 := by
    rw [hz_eq]
    have hmRlt : (m : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hmlt
    have hdenR : 0 < (2 : ℝ) * (N : ℝ) := by positivity
    rw [div_lt_one hdenR]
    simpa [mul_assoc] using hmRlt
  linarith

/-- **Equation (9.12)** support, shifted geometric sum for an even nonzero
frequency.  The sum is over `r = 1, ..., N-1`, represented as
`Fin (N-1)` with exponent `r.val + 1`. -/
theorem higham9_12_shifted_geometric_sum_even (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q < 2 * N) (hqpos : 0 < q) :
    let ζ : ℂ := Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))
    (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) = -1 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  have hζpow : ζ ^ N = 1 := by
    simpa [ζ] using higham9_12_sineRoot_pow_even N q hNpos
  have hζne : ζ ≠ 1 := by
    have hmpos : 0 < 2 * q := Nat.mul_pos (by norm_num) hqpos
    simpa [ζ] using higham9_12_sineRoot_ne_one N (2 * q) hNpos hmpos hqlt
  have hgeom := geom_sum_eq hζne N
  have hsumN : (∑ i ∈ Finset.range N, ζ ^ i) = 0 := by
    rw [hζpow] at hgeom
    simpa [hζne] using hgeom
  have hNpred : N - 1 + 1 = N :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hNpos)
  have hsplit :
      (∑ i ∈ Finset.range N, ζ ^ i) =
        (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1 := by
    rw [← hNpred]
    simpa [pow_zero, add_comm] using
      (Finset.sum_range_succ' (fun i : ℕ => ζ ^ i) (N - 1))
  have hshift_range : (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) = -1 := by
    have hzero : (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1 = 0 := by
      simpa [hsplit] using hsumN
    calc
      (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1))
          = ((∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1) - 1 := by ring
      _ = 0 - 1 := by rw [hzero]
      _ = -1 := by ring
  change (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) = -1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ (i + 1)) (N - 1)]
  exact hshift_range

/-- **Equation (9.12)** support, real part of a shifted sine-root power. -/
theorem higham9_12_sineRoot_shifted_pow_re_eq_cos (N m K : ℕ) (hN : 0 < N)
    (r : Fin K) :
    let ζ : ℂ := Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))
    (ζ ^ (r.val + 1)).re =
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ)) := by
  let ζ : ℂ := Complex.exp (((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  let x : ℝ :=
    (((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ)
  change (ζ ^ (r.val + 1)).re = Real.cos x
  unfold ζ
  rw [← Complex.exp_nat_mul]
  rw [show ((r.val + 1 : ℕ) : ℂ) *
        ((((m : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) =
        ((x : ℂ) * Complex.I) by
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
          norm_num [Complex.ext_iff]
          field_simp [hNR]
          dsimp [x]
          simp [Nat.cast_add]
          field_simp [hNR]]
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **Equation (9.12)** support, finite cosine sum for an even positive
frequency `2q` with `0 < 2q < 2N`:
`sum_{r=1}^{N-1} cos(r*2q*pi/N) = -1`. -/
theorem higham9_12_cos_sum_even (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q < 2 * N) (hqpos : 0 < q) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q : ℕ) : ℝ) * Real.pi) /
        (N : ℝ))) = -1 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hcomplex :
      (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) = -1 := by
    simpa [ζ] using higham9_12_shifted_geometric_sum_even N q hN hqlt hqpos
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  calc
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q : ℕ) : ℝ) * Real.pi) /
        (N : ℝ)))
        = ∑ r : Fin (N - 1), (ζ ^ (r.val + 1)).re := by
          apply Finset.sum_congr rfl
          intro r _
          exact (higham9_12_sineRoot_shifted_pow_re_eq_cos
            N (2 * q) (N - 1) hNpos r).symm
    _ = (∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re := by simp
    _ = -1 := by rw [hcomplex]; norm_num

private theorem higham9_12_inv_sub_one_re_of_normSq_eq_one {z : ℂ}
    (hzunit : Complex.normSq z = 1) (hzne : z ≠ 1) :
    ((z - 1)⁻¹).re = -1 / 2 := by
  rw [Complex.inv_re]
  have hnorm_sub : Complex.normSq (z - 1) = 2 - 2 * z.re := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num
    rw [Complex.normSq_apply] at hzunit
    nlinarith
  have hden : 2 - 2 * z.re ≠ 0 := by
    intro h
    have hzre : z.re = 1 := by linarith
    have hzim_sq : z.im * z.im = 0 := by
      rw [Complex.normSq_apply] at hzunit
      nlinarith
    have hzim : z.im = 0 := by
      exact mul_self_eq_zero.mp hzim_sq
    apply hzne
    rw [Complex.ext_iff]
    constructor <;> simp [hzre, hzim]
  rw [Complex.sub_re]
  norm_num
  rw [hnorm_sub]
  have hden1 : 1 - z.re ≠ 0 := by
    intro h
    apply hden
    nlinarith
  field_simp [hden, hden1]
  ring

/-- **Equation (9.12)** support, the shifted odd-frequency geometric sum has
zero real part. -/
theorem higham9_12_shifted_geometric_sum_odd_re (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q + 1 < 2 * N) :
    let ζ : ℂ := Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
        Complex.I))
    ((∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re) = 0 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  have hζpow : ζ ^ N = -1 := by
    simpa [ζ] using higham9_12_sineRoot_pow_odd N q hNpos
  have hζne : ζ ≠ 1 := by
    have hmpos : 0 < 2 * q + 1 := by omega
    simpa [ζ] using higham9_12_sineRoot_ne_one N (2 * q + 1) hNpos hmpos hqlt
  have hgeom := geom_sum_eq hζne N
  have hsumN : (∑ i ∈ Finset.range N, ζ ^ i) = (-2 : ℂ) / (ζ - 1) := by
    rw [hζpow] at hgeom
    calc
      (∑ i ∈ Finset.range N, ζ ^ i) = ((-1 : ℂ) - 1) / (ζ - 1) := by
        simpa using hgeom
      _ = (-2 : ℂ) / (ζ - 1) := by norm_num
  have hNpred : N - 1 + 1 = N :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hNpos)
  have hsplit :
      (∑ i ∈ Finset.range N, ζ ^ i) =
        (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1 := by
    rw [← hNpred]
    simpa [pow_zero, add_comm] using
      (Finset.sum_range_succ' (fun i : ℕ => ζ ^ i) (N - 1))
  have hshift_range :
      (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) =
        (-2 : ℂ) / (ζ - 1) - 1 := by
    calc
      (∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1))
          = ((∑ i ∈ Finset.range (N - 1), ζ ^ (i + 1)) + 1) - 1 := by ring
      _ = (∑ i ∈ Finset.range N, ζ ^ i) - 1 := by rw [← hsplit]
      _ = (-2 : ℂ) / (ζ - 1) - 1 := by rw [hsumN]
  have hshift_fin :
      (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) =
        (-2 : ℂ) / (ζ - 1) - 1 := by
    change (∑ r : Fin (N - 1), ζ ^ (r.val + 1)) =
      (-2 : ℂ) / (ζ - 1) - 1
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ (i + 1)) (N - 1)]
    exact hshift_range
  have hζ_normSq : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hinv_re : ((ζ - 1)⁻¹).re = -1 / 2 :=
    higham9_12_inv_sub_one_re_of_normSq_eq_one hζ_normSq hζne
  change ((∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re) = 0
  rw [hshift_fin]
  rw [div_eq_mul_inv]
  rw [Complex.sub_re, Complex.mul_re, hinv_re]
  have hminus_re : ((-2 : ℂ).re) = -2 := by norm_num
  have hminus_im : ((-2 : ℂ).im) = 0 := by norm_num
  have hone_re : ((1 : ℂ).re) = 1 := by norm_num
  rw [hminus_re, hminus_im, hone_re]
  have hprod : (-2 : ℝ) * (-1 / 2) = 1 := by norm_num
  rw [hprod, zero_mul]
  rw [sub_zero]
  exact sub_self (1 : ℝ)

/-- **Equation (9.12)** support, finite cosine sum for an odd positive
frequency `2q+1` with `2q+1 < 2N`:
`sum_{r=1}^{N-1} cos(r*(2q+1)*pi/N) = 0`. -/
theorem higham9_12_cos_sum_odd (N q : ℕ) (hN : 1 < N)
    (hqlt : 2 * q + 1 < 2 * N) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q + 1 : ℕ) : ℝ) * Real.pi) /
        (N : ℝ))) = 0 := by
  classical
  let ζ : ℂ := Complex.exp ((((((2 * q + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hcomplex_re :
      ((∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re) = 0 := by
    simpa [ζ] using higham9_12_shifted_geometric_sum_odd_re N q hN hqlt
  have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
  calc
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * q + 1 : ℕ) : ℝ) * Real.pi) /
        (N : ℝ)))
        = ∑ r : Fin (N - 1), (ζ ^ (r.val + 1)).re := by
          apply Finset.sum_congr rfl
          intro r _
          exact (higham9_12_sineRoot_shifted_pow_re_eq_cos
            N (2 * q + 1) (N - 1) hNpos r).symm
    _ = (∑ r : Fin (N - 1), ζ ^ (r.val + 1)).re := by simp
    _ = 0 := hcomplex_re

/-- **Equation (9.12)** support, finite cosine sum for any positive frequency
`m` with `m < 2N`, split by parity. -/
theorem higham9_12_cos_sum_pos_lt_two_mul (N m : ℕ) (hN : 1 < N)
    (hmpos : 0 < m) (hmlt : m < 2 * N) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ))) =
      if Even m then -1 else 0 := by
  classical
  by_cases hEven : Even m
  · rw [if_pos hEven]
    rcases hEven with ⟨q, hq⟩
    have hm_eq : m = 2 * q := by simpa [two_mul] using hq
    rw [hm_eq] at hmlt ⊢
    have hqpos : 0 < q := by omega
    simpa using higham9_12_cos_sum_even N q hN hmlt hqpos
  · rw [if_neg hEven]
    have hOdd : Odd m := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨q, hq⟩
    have hm_eq : m = 2 * q + 1 := by
      simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
    rw [hm_eq] at hmlt ⊢
    simpa [Nat.cast_add, Nat.cast_mul] using higham9_12_cos_sum_odd N q hN hmlt

/-- **Equation (9.12)** support, positive frequencies below `2N` with the
same parity have the same finite cosine sum. -/
theorem higham9_12_cos_sum_eq_of_mod_two_eq (N m k : ℕ) (hN : 1 < N)
    (hmpos : 0 < m) (hmlt : m < 2 * N)
    (hkpos : 0 < k) (hklt : k < 2 * N)
    (hpar : m % 2 = k % 2) :
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (m : ℝ) * Real.pi) / (N : ℝ))) =
    (∑ r : Fin (N - 1),
      Real.cos ((((r.val + 1 : ℕ) : ℝ) * (k : ℝ) * Real.pi) / (N : ℝ))) := by
  classical
  rw [higham9_12_cos_sum_pos_lt_two_mul N m hN hmpos hmlt,
    higham9_12_cos_sum_pos_lt_two_mul N k hN hkpos hklt]
  have hEven_iff : Even m ↔ Even k := by
    rw [Nat.even_iff, Nat.even_iff, hpar]
  by_cases hm : Even m
  · have hk : Even k := hEven_iff.mp hm
    simp [hm, hk]
  · have hk : ¬ Even k := by
      intro hk
      exact hm (hEven_iff.mpr hk)
    simp [hm, hk]

/-- **Equation (9.12)**, unscaled discrete sine orthogonality:
for `0 < p,q < N`,
`sum_{r=1}^{N-1} sin(r*p*pi/N) sin(r*q*pi/N)` is `N/2` on the
diagonal and `0` off the diagonal. -/
theorem higham9_12_sine_product_sum (N p q : ℕ) (hN : 1 < N)
    (hp : 0 < p) (hpN : p < N) (hq : 0 < q) (hqN : q < N) :
    (∑ r : Fin (N - 1),
      Real.sin ((((r.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
        Real.sin ((((r.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) =
      if p = q then (N : ℝ) / 2 else 0 := by
  classical
  let X : Fin (N - 1) → ℝ :=
    fun r => (((r.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)
  let Y : Fin (N - 1) → ℝ :=
    fun r => (((r.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ)
  let S : ℝ := ∑ r : Fin (N - 1), Real.sin (X r) * Real.sin (Y r)
  have htwo :
      2 * S =
        (∑ r : Fin (N - 1), Real.cos (X r - Y r)) -
          (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
    calc
      2 * S = ∑ r : Fin (N - 1), 2 * (Real.sin (X r) * Real.sin (Y r)) := by
        simp [S, Finset.mul_sum]
      _ = ∑ r : Fin (N - 1), (Real.cos (X r - Y r) - Real.cos (X r + Y r)) := by
        apply Finset.sum_congr rfl
        intro r _
        calc
          2 * (Real.sin (X r) * Real.sin (Y r))
              = 2 * Real.sin (X r) * Real.sin (Y r) := by ring
          _ = Real.cos (X r - Y r) - Real.cos (X r + Y r) :=
              Real.two_mul_sin_mul_sin (X r) (Y r)
      _ = (∑ r : Fin (N - 1), Real.cos (X r - Y r)) -
          (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
        rw [Finset.sum_sub_distrib]
  by_cases hpq : p = q
  · subst q
    have hdiff :
        (∑ r : Fin (N - 1), Real.cos (X r - Y r)) = (N : ℝ) - 1 := by
      simp [X, Y]
      have hNpos : 0 < N := Nat.lt_trans Nat.zero_lt_one hN
      rw [Nat.cast_sub (Nat.succ_le_iff.mpr hNpos)]
      norm_num
    have hsum_arg :
        (∑ r : Fin (N - 1), Real.cos (X r + Y r)) =
          (∑ r : Fin (N - 1),
            Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((2 * p : ℕ) : ℝ) * Real.pi) /
              (N : ℝ))) := by
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
      dsimp [X, Y]
      field_simp [hNR]
      simp [Nat.cast_mul]
      ring
    have hsum :
        (∑ r : Fin (N - 1), Real.cos (X r + Y r)) = -1 := by
      rw [hsum_arg]
      have hp2lt : 2 * p < 2 * N := by omega
      exact higham9_12_cos_sum_even N p hN hp2lt hp
    have htwoN : 2 * S = (N : ℝ) := by
      rw [htwo, hdiff, hsum]
      norm_num
    have hS : S = (N : ℝ) / 2 := by nlinarith
    simpa [S, X, Y] using hS
  · have hoff : S = 0 := by
      have hlt_or_gt : p < q ∨ q < p := lt_or_gt_of_ne hpq
      rcases hlt_or_gt with hpq_lt | hqp_lt
      · have hdiff_arg :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((q - p : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [← Real.cos_neg]
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          have hsub : ((q - p : ℕ) : ℝ) = (q : ℝ) - (p : ℝ) :=
            Nat.cast_sub hpq_lt.le
          dsimp [X, Y]
          field_simp [hNR]
          rw [hsub]
          ring
        have hsum_arg :
            (∑ r : Fin (N - 1), Real.cos (X r + Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((p + q : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          dsimp [X, Y]
          field_simp [hNR]
          simp [Nat.cast_add]
        have hbounds :
            0 < q - p ∧ q - p < 2 * N ∧ 0 < p + q ∧ p + q < 2 * N := by
          omega
        have hpar : (q - p) % 2 = (p + q) % 2 := by omega
        have heq :=
          higham9_12_cos_sum_eq_of_mod_two_eq N (q - p) (p + q) hN
            hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2 hpar
        have hdiff_eq_sum :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
          rw [hdiff_arg, hsum_arg]
          exact heq
        have htwo0 : 2 * S = 0 := by
          rw [htwo, hdiff_eq_sum]
          ring
        nlinarith
      · have hdiff_arg :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((p - q : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          have hsub : ((p - q : ℕ) : ℝ) = (p : ℝ) - (q : ℝ) :=
            Nat.cast_sub hqp_lt.le
          dsimp [X, Y]
          field_simp [hNR]
          rw [hsub]
        have hsum_arg :
            (∑ r : Fin (N - 1), Real.cos (X r + Y r)) =
              (∑ r : Fin (N - 1),
                Real.cos ((((r.val + 1 : ℕ) : ℝ) * ((p + q : ℕ) : ℝ) * Real.pi) /
                  (N : ℝ))) := by
          apply Finset.sum_congr rfl
          intro r _
          congr 1
          have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.lt_trans Nat.zero_lt_one hN)
          dsimp [X, Y]
          field_simp [hNR]
          simp [Nat.cast_add]
        have hbounds :
            0 < p - q ∧ p - q < 2 * N ∧ 0 < p + q ∧ p + q < 2 * N := by
          omega
        have hpar : (p - q) % 2 = (p + q) % 2 := by omega
        have heq :=
          higham9_12_cos_sum_eq_of_mod_two_eq N (p - q) (p + q) hN
            hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2 hpar
        have hdiff_eq_sum :
            (∑ r : Fin (N - 1), Real.cos (X r - Y r)) =
              (∑ r : Fin (N - 1), Real.cos (X r + Y r)) := by
          rw [hdiff_arg, hsum_arg]
          exact heq
        have htwo0 : 2 * S = 0 := by
          rw [htwo, hdiff_eq_sum]
          ring
        nlinarith
    simpa [S, X, Y, hpq] using hoff

/-- **Equation (9.12)**, the scaled sine matrix is its own inverse:
`S_n * S_n = I` entrywise. -/
theorem higham9_12_sineMatrix_mul_self {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (∑ k : Fin n, higham9_12_sineMatrix n i k * higham9_12_sineMatrix n k j) =
      if i = j then 1 else 0 := by
  classical
  let c : ℝ := Real.sqrt (2 / ((n : ℝ) + 1))
  let N : ℕ := n + 1
  let p : ℕ := i.val + 1
  let q : ℕ := j.val + 1
  have hNgt : 1 < N := by
    dsimp [N]
    omega
  have hp_pos : 0 < p := by dsimp [p]; omega
  have hq_pos : 0 < q := by dsimp [q]; omega
  have hp_lt : p < N := by
    dsimp [p, N]
    omega
  have hq_lt : q < N := by
    dsimp [q, N]
    omega
  have hprod_sum :
      (∑ k : Fin n,
        Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
          Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) =
        if p = q then (N : ℝ) / 2 else 0 := by
    simpa [N, p, q, Nat.add_sub_cancel] using
      higham9_12_sine_product_sum N p q hNgt hp_pos hp_lt hq_pos hq_lt
  have hscale_sq : c * c = 2 / ((n : ℝ) + 1) := by
    dsimp [c]
    rw [← pow_two, Real.sq_sqrt]
    positivity
  have hmain :
      (∑ k : Fin n, higham9_12_sineMatrix n i k * higham9_12_sineMatrix n k j) =
        c * c *
          (∑ k : Fin n,
            Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
              Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) := by
    calc
      (∑ k : Fin n, higham9_12_sineMatrix n i k * higham9_12_sineMatrix n k j)
          = ∑ k : Fin n,
              c * Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
                (c * Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) := by
            apply Finset.sum_congr rfl
            intro k _
            unfold higham9_12_sineMatrix
            dsimp [c, p, q, N]
            congr 2 <;> (norm_num [Nat.cast_add]; try ring_nf)
      _ = c * c *
          (∑ k : Fin n,
            Real.sin ((((k.val + 1 : ℕ) : ℝ) * (p : ℝ) * Real.pi) / (N : ℝ)) *
              Real.sin ((((k.val + 1 : ℕ) : ℝ) * (q : ℝ) * Real.pi) / (N : ℝ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
  by_cases hij : i = j
  · subst j
    have hpq : p = q := by dsimp [p, q]
    rw [if_pos rfl]
    rw [hmain, hprod_sum, if_pos hpq, hscale_sq]
    dsimp [N]
    have hnR : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hnR]
    norm_num [Nat.cast_add]
  · have hpq : p ≠ q := by
      intro hpq
      apply hij
      apply Fin.ext
      dsimp [p, q] at hpq
      omega
    rw [if_neg hij]
    rw [hmain, hprod_sum, if_neg hpq]
    ring

/-- **Equation (9.12)**, inverse formula for the sine matrix:
the scaled sine matrix is both a left and right inverse of itself. -/
theorem higham9_12_sineMatrix_inverse_formula {n : ℕ} (hn : 0 < n) :
    IsLeftInverse n (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) ∧
      IsRightInverse n (higham9_12_sineMatrix n) (higham9_12_sineMatrix n) := by
  exact ⟨fun i j => higham9_12_sineMatrix_mul_self hn i j,
    fun i j => higham9_12_sineMatrix_mul_self hn i j⟩

/-- **Problem 9.11 / equation (9.12)**, conditional theta lower bound.
If a matrix and the inverse candidate used in `theta(A) = 1/(alpha(A) beta(A))`
both have max-entry norm at most the sine-matrix scale `sqrt(2/(n+1))`, then
`theta(A) >= (n+1)/2`. -/
theorem higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale {n : ℕ}
    (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hApos : 0 < maxEntryNorm hn A)
    (hAinvpos : 0 < maxEntryNorm hn A_inv)
    (hA_bound :
      maxEntryNorm hn A ≤ Real.sqrt (2 / ((n : ℝ) + 1)))
    (hAinv_bound :
      maxEntryNorm hn A_inv ≤ Real.sqrt (2 / ((n : ℝ) + 1))) :
    ((n : ℝ) + 1) / 2 ≤
      1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv) := by
  let c : ℝ := 2 / ((n : ℝ) + 1)
  have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hA_bound' : maxEntryNorm hn A ≤ Real.sqrt c := by
    simpa [c] using hA_bound
  have hAinv_bound' : maxEntryNorm hn A_inv ≤ Real.sqrt c := by
    simpa [c] using hAinv_bound
  have hprod_le_sqrt :
      maxEntryNorm hn A * maxEntryNorm hn A_inv ≤
        Real.sqrt c * Real.sqrt c := by
    exact mul_le_mul hA_bound' hAinv_bound' (le_of_lt hAinvpos) (Real.sqrt_nonneg c)
  have hsqrt_mul : Real.sqrt c * Real.sqrt c = c := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hcpos)
  have hprod_le :
      maxEntryNorm hn A * maxEntryNorm hn A_inv ≤ c := by
    simpa [hsqrt_mul] using hprod_le_sqrt
  have hinv :
      c⁻¹ ≤ (maxEntryNorm hn A * maxEntryNorm hn A_inv)⁻¹ :=
    inv_anti₀ (mul_pos hApos hAinvpos) hprod_le
  have hhalf : ((n : ℝ) + 1) / 2 = 1 / c := by
    dsimp [c]
    field_simp [hn1_pos.ne']
  rw [hhalf]
  simpa [one_div] using hinv

/-- **Problem 9.11 / equation (9.12)**, the same conditional theta witness in
the doubled form used by the lower-bound consequence: `n + 1 <= 2*theta(A)`. -/
theorem higham9_12_two_theta_ge_succ_of_maxEntryNorm_le_scale {n : ℕ}
    (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hApos : 0 < maxEntryNorm hn A)
    (hAinvpos : 0 < maxEntryNorm hn A_inv)
    (hA_bound :
      maxEntryNorm hn A ≤ Real.sqrt (2 / ((n : ℝ) + 1)))
    (hAinv_bound :
      maxEntryNorm hn A_inv ≤ Real.sqrt (2 / ((n : ℝ) + 1))) :
    (n : ℝ) + 1 ≤
      2 * (1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv)) := by
  have hhalf :=
    higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale hn A A_inv
      hApos hAinvpos hA_bound hAinv_bound
  linarith

/-- **Problem 9.11 / equation (9.12)**, theta arithmetic instantiated for the
sine witness as both matrix and inverse candidate.

This proves the source denominator bound from the entrywise scale and the
positive `(0,0)` entry; the self-inverse certificate is
`higham9_12_sineMatrix_inverse_formula`. -/
theorem higham9_12_sineMatrix_theta_candidate_ge_half_succ {n : ℕ}
    (hn : 0 < n) :
    ((n : ℝ) + 1) / 2 ≤
      1 / (maxEntryNorm hn (higham9_12_sineMatrix n) *
        maxEntryNorm hn (higham9_12_sineMatrix n)) := by
  exact higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale hn
    (higham9_12_sineMatrix n) (higham9_12_sineMatrix n)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)
    (higham9_12_sineMatrix_maxEntryNorm_le_scale hn)
    (higham9_12_sineMatrix_maxEntryNorm_le_scale hn)

/-- **Problem 9.11 / equation (9.12)**, doubled theta arithmetic instantiated
for the sine witness as both matrix and inverse candidate. -/
theorem higham9_12_sineMatrix_two_theta_candidate_ge_succ {n : ℕ}
    (hn : 0 < n) :
    (n : ℝ) + 1 ≤
      2 * (1 / (maxEntryNorm hn (higham9_12_sineMatrix n) *
        maxEntryNorm hn (higham9_12_sineMatrix n))) := by
  have hhalf := higham9_12_sineMatrix_theta_candidate_ge_half_succ hn
  linarith

/-- **Equation (9.13)**, the complex Vandermonde/Fourier matrix
`V_n = (exp(-2*pi*i*(r-1)*(s-1)/n))`.  The source's one-based indices are
represented by `r.val` and `s.val`, since `Fin` indices are zero-based.
The inverse formula `V_n^{-1} = n^{-1} V_nᴴ` and the resulting growth lower
bound is represented below by a scaled-adjoint two-sided inverse; the growth
lower bound remains a separate open target. -/
noncomputable def higham9_13_fourierVandermonde (n : ℕ) :
    Fin n → Fin n → ℂ :=
  fun r s =>
    Complex.exp
      ((((-2 : ℝ) * Real.pi * (r.val : ℝ) * (s.val : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)

/-- **Equation (9.13)**, the Fourier/Vandermonde matrix is symmetric because
the exponent depends on the product `(r-1)*(s-1)`. -/
theorem higham9_13_fourierVandermonde_symm {n : ℕ} (r s : Fin n) :
    higham9_13_fourierVandermonde n r s =
      higham9_13_fourierVandermonde n s r := by
  unfold higham9_13_fourierVandermonde
  congr 2
  ring_nf

/-- **Equation (9.13)**, the first row of the Fourier/Vandermonde matrix is
identically `1`. -/
theorem higham9_13_fourierVandermonde_firstRow {n : ℕ} (hn : 0 < n)
    (s : Fin n) :
    higham9_13_fourierVandermonde n ⟨0, hn⟩ s = 1 := by
  simp [higham9_13_fourierVandermonde]

/-- **Equation (9.13)**, the first column of the Fourier/Vandermonde matrix is
identically `1`. -/
theorem higham9_13_fourierVandermonde_firstCol {n : ℕ} (hn : 0 < n)
    (r : Fin n) :
    higham9_13_fourierVandermonde n r ⟨0, hn⟩ = 1 := by
  simp [higham9_13_fourierVandermonde]

/-- **Equation (9.13)**, every Fourier/Vandermonde entry has complex norm
`1`. This is the unit-circle part of the roots-of-unity example, not the
complete inverse-formula or growth lower-bound argument by itself. -/
theorem higham9_13_fourierVandermonde_norm {n : ℕ} (r s : Fin n) :
    ‖higham9_13_fourierVandermonde n r s‖ = 1 := by
  unfold higham9_13_fourierVandermonde
  rw [Complex.norm_exp_ofReal_mul_I]

/-- **Equation (9.13)**, unit-circle entries give
`conj(v_rs) * v_rs = 1`.  This is the diagonal-entry part of the Fourier
orthogonality calculation, not the off-diagonal roots-of-unity cancellation. -/
theorem higham9_13_fourierVandermonde_conj_mul_self {n : ℕ} (r s : Fin n) :
    conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s = 1 := by
  have hnormSq :
      Complex.normSq (higham9_13_fourierVandermonde n r s) = 1 := by
    rw [Complex.normSq_eq_norm_sq, higham9_13_fourierVandermonde_norm]
    norm_num
  have hmul := Complex.normSq_eq_conj_mul_self
    (z := higham9_13_fourierVandermonde n r s)
  rw [← hmul, hnormSq]
  norm_num

/-- **Equation (9.13)**, diagonal column Gram identity:
each Fourier/Vandermonde column has squared norm `n`.  This is the diagonal
part of the full Gram calculation below. -/
theorem higham9_13_fourierVandermonde_column_norm_sq {n : ℕ} (s : Fin n) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s) = (n : ℂ) := by
  calc
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s)
        = ∑ _r : Fin n, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro r _
          exact higham9_13_fourierVandermonde_conj_mul_self r s
    _ = (n : ℂ) := by simp

/-- **Equation (9.13)**, diagonal row Gram identity:
each Fourier/Vandermonde row has squared norm `n`. -/
theorem higham9_13_fourierVandermonde_row_norm_sq {n : ℕ} (r : Fin n) :
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s) = (n : ℂ) := by
  calc
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r s)
        = ∑ _s : Fin n, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro s _
          exact higham9_13_fourierVandermonde_conj_mul_self r s
    _ = (n : ℂ) := by simp

/-- **Equation (9.13)**, the scalar Fourier root used for a nonzero column
difference has `n`th power `1`. -/
theorem higham9_13_fourierRoot_pow_card (n k : ℕ) (hn : 0 < n) :
    (Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ n = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show (n : ℂ) *
        ((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) =
        (-(k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
          norm_num [Complex.ext_iff]
          field_simp [hnR]]
  simpa using Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))

/-- **Equation (9.13)**, a nonzero Fourier root with `0 < k < n` is not `1`.
This supplies the nontrivial denominator for the geometric-sum cancellation. -/
theorem higham9_13_fourierRoot_ne_one (n k : ℕ) (hn : 0 < n)
    (hkpos : 0 < k) (hklt : k < n) :
    Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)) ≠ 1 := by
  intro h
  have h' : Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)) = Complex.exp 0 := by
    simpa using h
  rw [Complex.exp_eq_exp_iff_exists_int] at h'
  rcases h' with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  have hm_real : ((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ)) =
      (m : ℝ) * (2 * Real.pi) := by
    simpa [Complex.ext_iff, mul_assoc, mul_comm, mul_left_comm] using him
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hm_eq : (m : ℝ) = - (k : ℝ) / (n : ℝ) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    field_simp [hnR, hpi] at hm_real ⊢
    nlinarith
  have hm_lt_zero : (m : ℝ) < 0 := by
    rw [hm_eq]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnegk : - (k : ℝ) < 0 := by linarith
    exact div_neg_of_neg_of_pos hnegk hnRpos
  have hm_int_lt_zero : m < 0 := by
    exact_mod_cast hm_lt_zero
  have hm_le_neg_one : m ≤ -1 := by omega
  have hm_cast_le_neg_one : (m : ℝ) ≤ -1 := by
    exact_mod_cast hm_le_neg_one
  have hm_gt_neg_one : -1 < (m : ℝ) := by
    rw [hm_eq]
    have hkltR : (k : ℝ) < n := by exact_mod_cast hklt
    have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [lt_div_iff₀ hnRpos]
    nlinarith
  linarith

/-- **Equation (9.13)**, roots-of-unity cancellation for a nonzero column
difference. -/
theorem higham9_13_fourierRoot_geometric_sum_zero (n k : ℕ) (hn : 0 < n)
    (hkpos : 0 < k) (hklt : k < n) :
    (∑ r : Fin n,
      (Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ r.val) = 0 := by
  let ζ : ℂ :=
    Complex.exp (((((-2 : ℝ) * Real.pi * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) *
      Complex.I))
  have hζpow : ζ ^ n = 1 := by
    simpa [ζ] using higham9_13_fourierRoot_pow_card n k hn
  have hζne : ζ ≠ 1 := by
    simpa [ζ] using higham9_13_fourierRoot_ne_one n k hn hkpos hklt
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ζ ^ i) n]
  have hgeom := geom_sum_eq hζne n
  rw [hζpow] at hgeom
  simpa [ζ, hζne] using hgeom

/-- **Equation (9.13)**, each off-diagonal column Gram term for ordered
columns is a power of the corresponding nontrivial Fourier root. -/
theorem higham9_13_fourierVandermonde_conj_mul_eq_pow_of_col_lt {n : ℕ}
    {s t : Fin n} (hst : s.val < t.val) (r : Fin n) :
    conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t =
      (Complex.exp (((((-2 : ℝ) * Real.pi * ((t.val - s.val : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I))) ^ r.val := by
  unfold higham9_13_fourierVandermonde
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  have hsub : ((t.val - s.val : ℕ) : ℝ) = (t.val : ℝ) - (s.val : ℝ) := by
    exact Nat.cast_sub hst.le
  norm_num [Complex.ext_iff, hsub]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le s.val) s.isLt)
  field_simp [hnR]
  ring

/-- **Equation (9.13)**, off-diagonal column orthogonality for ordered
columns of the Fourier/Vandermonde matrix. -/
theorem higham9_13_fourierVandermonde_column_orthogonal_of_lt {n : ℕ}
    {s t : Fin n} (hst : s.val < t.val) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t) = 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  have hkpos : 0 < t.val - s.val := Nat.sub_pos_of_lt hst
  have hklt : t.val - s.val < n :=
    lt_of_le_of_lt (Nat.sub_le t.val s.val) t.isLt
  calc
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t)
        = ∑ r : Fin n,
            (Complex.exp (((((-2 : ℝ) * Real.pi *
                ((t.val - s.val : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) *
              Complex.I))) ^ r.val := by
          apply Finset.sum_congr rfl
          intro r _
          exact higham9_13_fourierVandermonde_conj_mul_eq_pow_of_col_lt hst r
    _ = 0 := higham9_13_fourierRoot_geometric_sum_zero n (t.val - s.val) hn hkpos hklt

/-- **Equation (9.13)**, off-diagonal column orthogonality of the
Fourier/Vandermonde matrix.  Together with
`higham9_13_fourierVandermonde_column_norm_sq`, this is the column Gram
calculation behind the source inverse formula. -/
theorem higham9_13_fourierVandermonde_column_orthogonal {n : ℕ}
    {s t : Fin n} (hst : s ≠ t) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t) = 0 := by
  have hval : s.val ≠ t.val := by
    intro h
    exact hst (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact higham9_13_fourierVandermonde_column_orthogonal_of_lt hlt
  · have hswap :=
      higham9_13_fourierVandermonde_column_orthogonal_of_lt (n := n) (s := t) (t := s) hgt
    calc
      (∑ r : Fin n,
        conj (higham9_13_fourierVandermonde n r s) *
          higham9_13_fourierVandermonde n r t)
          = conj (∑ r : Fin n,
              conj (higham9_13_fourierVandermonde n r t) *
                higham9_13_fourierVandermonde n r s) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro r _
            simp [map_mul, mul_comm]
      _ = 0 := by simp [hswap]

/-- **Equation (9.13)**, the full column Gram calculation:
`V_n^H V_n` has diagonal entries `n` and off-diagonal entries `0`. -/
theorem higham9_13_fourierVandermonde_column_gram {n : ℕ} (s t : Fin n) :
    (∑ r : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n r t) =
      if s = t then (n : ℂ) else 0 := by
  by_cases hst : s = t
  · subst t
    simp [higham9_13_fourierVandermonde_column_norm_sq]
  · simp [hst, higham9_13_fourierVandermonde_column_orthogonal hst]

/-- **Equation (9.13)**, off-diagonal row orthogonality, derived from the
column calculation and symmetry of the Fourier/Vandermonde matrix. -/
theorem higham9_13_fourierVandermonde_row_orthogonal {n : ℕ}
    {r q : Fin n} (hrq : r ≠ q) :
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n q s) = 0 := by
  calc
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n q s)
        = ∑ s : Fin n,
            conj (higham9_13_fourierVandermonde n s r) *
              higham9_13_fourierVandermonde n s q := by
          apply Finset.sum_congr rfl
          intro s _
          rw [higham9_13_fourierVandermonde_symm r s,
            higham9_13_fourierVandermonde_symm q s]
    _ = 0 := higham9_13_fourierVandermonde_column_orthogonal hrq

/-- **Equation (9.13)**, the full row Gram calculation:
`V_n V_n^H` has diagonal entries `n` and off-diagonal entries `0`. -/
theorem higham9_13_fourierVandermonde_row_gram {n : ℕ} (r q : Fin n) :
    (∑ s : Fin n,
      conj (higham9_13_fourierVandermonde n r s) *
        higham9_13_fourierVandermonde n q s) =
      if r = q then (n : ℂ) else 0 := by
  by_cases hrq : r = q
  · subst q
    simp [higham9_13_fourierVandermonde_row_norm_sq]
  · simp [hrq, higham9_13_fourierVandermonde_row_orthogonal hrq]

/-- **Equation (9.13)**, the source inverse candidate `n^{-1} V_nᴴ`,
written entrywise with zero-based `Fin` indices. -/
noncomputable def higham9_13_fourierVandermondeScaledAdjoint (n : ℕ) :
    Fin n → Fin n → ℂ :=
  fun s r => ((n : ℂ)⁻¹) * conj (higham9_13_fourierVandermonde n r s)

/-- **Equation (9.13)**, the scaled adjoint is a left inverse of the
Fourier/Vandermonde matrix: `(n^{-1} V_nᴴ) V_n = I`. -/
theorem higham9_13_scaledAdjoint_mul_fourierVandermonde {n : ℕ} (s t : Fin n) :
    (∑ r : Fin n,
      higham9_13_fourierVandermondeScaledAdjoint n s r *
        higham9_13_fourierVandermonde n r t) =
      if s = t then 1 else 0 := by
  unfold higham9_13_fourierVandermondeScaledAdjoint
  calc
    (∑ r : Fin n,
      (((n : ℂ)⁻¹) * conj (higham9_13_fourierVandermonde n r s)) *
        higham9_13_fourierVandermonde n r t)
        = ((n : ℂ)⁻¹) * (∑ r : Fin n,
            conj (higham9_13_fourierVandermonde n r s) *
              higham9_13_fourierVandermonde n r t) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = ((n : ℂ)⁻¹) * (if s = t then (n : ℂ) else 0) := by
          rw [higham9_13_fourierVandermonde_column_gram]
    _ = if s = t then 1 else 0 := by
          by_cases hst : s = t
          · subst t
            have hnNat : n ≠ 0 :=
              Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le s.val) s.isLt)
            have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hnNat
            simp [hn]
          · simp [hst]

/-- **Equation (9.13)**, the scaled adjoint is a right inverse of the
Fourier/Vandermonde matrix: `V_n (n^{-1} V_nᴴ) = I`. -/
theorem higham9_13_fourierVandermonde_mul_scaledAdjoint {n : ℕ} (r q : Fin n) :
    (∑ s : Fin n,
      higham9_13_fourierVandermonde n r s *
        higham9_13_fourierVandermondeScaledAdjoint n s q) =
      if r = q then 1 else 0 := by
  unfold higham9_13_fourierVandermondeScaledAdjoint
  calc
    (∑ s : Fin n,
      higham9_13_fourierVandermonde n r s *
        (((n : ℂ)⁻¹) * conj (higham9_13_fourierVandermonde n q s)))
        = ((n : ℂ)⁻¹) * (∑ s : Fin n,
            conj (higham9_13_fourierVandermonde n q s) *
              higham9_13_fourierVandermonde n r s) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = ((n : ℂ)⁻¹) * (if q = r then (n : ℂ) else 0) := by
          rw [higham9_13_fourierVandermonde_row_gram]
    _ = if r = q then 1 else 0 := by
          by_cases hrq : r = q
          · subst q
            have hnNat : n ≠ 0 :=
              Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le r.val) r.isLt)
            have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hnNat
            simp [hn]
          · have hqr : q ≠ r := fun h => hrq h.symm
            simp [hrq, hqr]

/-- **Equation (9.13)**, entrywise formalization of the source inverse formula
`V_n^{-1} = n^{-1} V_nᴴ`: the displayed scaled adjoint is both a left and a
right inverse of `V_n`. -/
theorem higham9_13_fourierVandermonde_inverse_formula (n : ℕ) :
    (∀ s t : Fin n,
      (∑ r : Fin n,
        higham9_13_fourierVandermondeScaledAdjoint n s r *
          higham9_13_fourierVandermonde n r t) =
        if s = t then 1 else 0) ∧
    (∀ r q : Fin n,
      (∑ s : Fin n,
        higham9_13_fourierVandermonde n r s *
          higham9_13_fourierVandermondeScaledAdjoint n s q) =
        if r = q then 1 else 0) := by
  exact ⟨higham9_13_scaledAdjoint_mul_fourierVandermonde,
    higham9_13_fourierVandermonde_mul_scaledAdjoint⟩

/-- **Equation (9.13)**, complex max-entry norm used for the
Fourier/Vandermonde lower-bound witness:
`max_{i,j} ‖A i j‖`.  The repository's standard Chapter 9 max-entry growth
factor is real-valued, so this local complex analogue records the source
quantity for the complex example without introducing a complex pivoting API. -/
noncomputable def higham9_13_complexMaxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      (fun j => ‖A i j‖))

/-- Every complex entry norm is bounded by
`higham9_13_complexMaxEntryNorm`. -/
lemma higham9_13_entry_norm_le_complexMaxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ higham9_13_complexMaxEntryNorm hn A := by
  apply le_trans
  · exact Finset.le_sup' (fun j => ‖A i j‖) (Finset.mem_univ j)
  · exact Finset.le_sup' (fun i => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => ‖A i j‖))
      (Finset.mem_univ i)

/-- The complex max-entry norm is nonnegative. -/
lemma higham9_13_complexMaxEntryNorm_nonneg {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) :
    0 ≤ higham9_13_complexMaxEntryNorm hn A := by
  let i0 : Fin n := ⟨0, hn⟩
  exact le_trans (norm_nonneg (A i0 i0))
    (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i0 i0)

/-- Complex max-entry norm bound from a uniform entrywise norm bound. -/
lemma higham9_13_complexMaxEntryNorm_le_of_entry_le_bound {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℂ) (M : ℝ)
    (hentry : ∀ i j : Fin n, ‖A i j‖ ≤ M) :
    higham9_13_complexMaxEntryNorm hn A ≤ M := by
  unfold higham9_13_complexMaxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact hentry i j

/-- Complex max-entry norm monotonicity when every entry is bounded by another
matrix's complex max-entry norm, possibly at different indices. -/
lemma higham9_13_complexMaxEntryNorm_le_of_entry_le_max {n : ℕ}
    (hn : 0 < n) (A B : Fin n → Fin n → ℂ)
    (hentry : ∀ i j : Fin n, ‖A i j‖ ≤ higham9_13_complexMaxEntryNorm hn B) :
    higham9_13_complexMaxEntryNorm hn A ≤ higham9_13_complexMaxEntryNorm hn B :=
  higham9_13_complexMaxEntryNorm_le_of_entry_le_bound hn A
    (higham9_13_complexMaxEntryNorm hn B) hentry

/-- **Theorem 9.8 / equation (9.13)**, complex max-entry `theta <= n` core
estimate.  If a row of `A * A_inv` has diagonal entry `1`, then
`1 <= n * alpha(A) * beta(A)` with complex entry norms. -/
theorem higham9_13_inverse_row_identity_le_card_mul_complexMaxEntryNorm
    {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℂ) (i : Fin n)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 ≤ (n : ℝ) * higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv := by
  have h_norm :
      ‖∑ j : Fin n, A i j * A_inv j i‖ ≤
        ∑ j : Fin n, ‖A i j * A_inv j i‖ := by
    simpa using
      (norm_sum_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => A i j * A_inv j i))
  have h_terms : ∀ j : Fin n,
      ‖A i j * A_inv j i‖ ≤
        higham9_13_complexMaxEntryNorm hn A *
          higham9_13_complexMaxEntryNorm hn A_inv := by
    intro j
    rw [norm_mul]
    exact mul_le_mul
      (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j)
      (higham9_13_entry_norm_le_complexMaxEntryNorm hn A_inv j i)
      (norm_nonneg _)
      (le_trans (norm_nonneg _) (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j))
  have h_sum :
      ∑ j : Fin n, ‖A i j * A_inv j i‖ ≤
        ∑ _j : Fin n,
          higham9_13_complexMaxEntryNorm hn A *
            higham9_13_complexMaxEntryNorm hn A_inv :=
    Finset.sum_le_sum (fun j _ => h_terms j)
  calc
    1 = ‖∑ j : Fin n, A i j * A_inv j i‖ := by rw [hrow, norm_one]
    _ ≤ ∑ j : Fin n, ‖A i j * A_inv j i‖ := h_norm
    _ ≤ ∑ _j : Fin n,
          higham9_13_complexMaxEntryNorm hn A *
            higham9_13_complexMaxEntryNorm hn A_inv := h_sum
    _ = (n : ℝ) * higham9_13_complexMaxEntryNorm hn A *
          higham9_13_complexMaxEntryNorm hn A_inv := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **Theorem 9.8 / equation (9.13)**, complex max-entry `theta <= n`.
This is the complex analogue of `higham9_8_theta_le_card_real`; the remaining
growth lower-bound rows still need the complete-pivoting trace/final-pivot
witness. -/
theorem higham9_8_theta_le_card_complex {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℂ) (i : Fin n)
    (hA : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hAinv : 0 < higham9_13_complexMaxEntryNorm hn A_inv)
    (hrow : ∑ j : Fin n, A i j * A_inv j i = 1) :
    1 / (higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv) ≤ n := by
  have hmain :=
    higham9_13_inverse_row_identity_le_card_mul_complexMaxEntryNorm
      hn A A_inv i hrow
  have hprod :
      0 < higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv :=
    mul_pos hA hAinv
  rw [div_le_iff₀ hprod]
  simpa [mul_assoc] using hmain

/-- **Equation (9.13)**, the Fourier/Vandermonde witness has
`max_{r,s} ‖(V_n)_{rs}‖ = 1`. -/
theorem higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one {n : ℕ}
    (hn : 0 < n) :
    higham9_13_complexMaxEntryNorm hn (higham9_13_fourierVandermonde n) = 1 := by
  apply le_antisymm
  · unfold higham9_13_complexMaxEntryNorm
    apply Finset.sup'_le
    intro r _
    apply Finset.sup'_le
    intro s _
    rw [higham9_13_fourierVandermonde_norm]
  · have hentry :=
      higham9_13_entry_norm_le_complexMaxEntryNorm hn
        (higham9_13_fourierVandermonde n) ⟨0, hn⟩ ⟨0, hn⟩
    simpa [higham9_13_fourierVandermonde_norm] using hentry

/-- **Equation (9.13)**, every entry of the scaled adjoint
`n⁻¹ V_nᴴ` has norm `1/n`. -/
theorem higham9_13_fourierVandermondeScaledAdjoint_norm {n : ℕ} (s r : Fin n) :
    ‖higham9_13_fourierVandermondeScaledAdjoint n s r‖ = ((n : ℝ)⁻¹) := by
  unfold higham9_13_fourierVandermondeScaledAdjoint
  rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_conj,
    higham9_13_fourierVandermonde_norm]
  ring

/-- **Equation (9.13)**, the inverse candidate `n⁻¹ V_nᴴ` has
`max_{r,s} ‖(n⁻¹ V_nᴴ)_{rs}‖ = 1/n`. -/
theorem higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv
    {n : ℕ} (hn : 0 < n) :
    higham9_13_complexMaxEntryNorm hn
        (higham9_13_fourierVandermondeScaledAdjoint n) =
      ((n : ℝ)⁻¹) := by
  apply le_antisymm
  · unfold higham9_13_complexMaxEntryNorm
    apply Finset.sup'_le
    intro s _
    apply Finset.sup'_le
    intro r _
    rw [higham9_13_fourierVandermondeScaledAdjoint_norm]
  · have hentry :=
      higham9_13_entry_norm_le_complexMaxEntryNorm hn
        (higham9_13_fourierVandermondeScaledAdjoint n) ⟨0, hn⟩ ⟨0, hn⟩
    simpa [higham9_13_fourierVandermondeScaledAdjoint_norm] using hentry

/-- **Equation (9.13)**, the Fourier/Vandermonde witness has source theta
quantity exactly `n`: with `α = max |V_n| = 1` and
`β = max |V_n⁻¹| = 1/n`, `(αβ)⁻¹ = n`.  The separate pivoting/growth bridge
from this theta witness to `rho_n(V_n) >= n` remains recorded in the report. -/
theorem higham9_13_fourierVandermonde_theta_eq_card {n : ℕ} (hn : 0 < n) :
    1 /
        (higham9_13_complexMaxEntryNorm hn (higham9_13_fourierVandermonde n) *
          higham9_13_complexMaxEntryNorm hn
            (higham9_13_fourierVandermondeScaledAdjoint n)) =
      (n : ℝ) := by
  rw [higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one hn,
    higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv hn]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  field_simp [hnR]

/-- Complex max-entry growth factor for the source complex example in
Theorem 9.8/equation (9.13).  This mirrors `growthFactorEntry` using complex
entry norms and is kept local to the Fourier/Vandermonde lower-bound branch,
since the repository's main LU growth API is real-valued. -/
noncomputable def higham9_13_complexGrowthFactorEntry {n : ℕ} (hn : 0 < n)
    (A U : Fin n → Fin n → ℂ) : ℝ :=
  higham9_13_complexMaxEntryNorm hn U / higham9_13_complexMaxEntryNorm hn A

/-- **Theorem 9.8**, complex max-entry bridge `rho >= theta`.

If a final pivot `u` has inverse equal to an entry of a visible inverse
candidate and `u` is bounded by the largest entry reached by elimination, then
the complex max-entry growth factor is at least `(alpha beta)^{-1}`.  This is
the complex analogue of `growthFactorEntry_ge_inverse_entry_theta`; it does
not construct the complete-pivoting trace that supplies such a pivot witness. -/
theorem higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta {n : ℕ}
    (hn : 0 < n)
    (A A_inv U : Fin n → Fin n → ℂ)
    (hA : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hAinv : 0 < higham9_13_complexMaxEntryNorm hn A_inv)
    (u : ℂ) (hu_pos : 0 < ‖u‖)
    (hu_entry : ‖u‖ ≤ higham9_13_complexMaxEntryNorm hn U)
    (hu_inv_entry : ∃ i j : Fin n, u⁻¹ = A_inv i j) :
    1 / (higham9_13_complexMaxEntryNorm hn A *
      higham9_13_complexMaxEntryNorm hn A_inv) ≤
      higham9_13_complexGrowthFactorEntry hn A U := by
  obtain ⟨i, j, hu_inv_entry⟩ := hu_inv_entry
  have hu_inv_le :
      ‖u‖⁻¹ ≤ higham9_13_complexMaxEntryNorm hn A_inv := by
    calc
      ‖u‖⁻¹ = ‖u⁻¹‖ := by rw [norm_inv]
      _ = ‖A_inv i j‖ := by rw [hu_inv_entry]
      _ ≤ higham9_13_complexMaxEntryNorm hn A_inv :=
          higham9_13_entry_norm_le_complexMaxEntryNorm hn A_inv i j
  have hbeta_inv_le_u :
      (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ ≤ ‖u‖ :=
    inv_le_of_inv_le₀ hu_pos hu_inv_le
  have hbeta_inv_le_U :
      (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ ≤
        higham9_13_complexMaxEntryNorm hn U :=
    le_trans hbeta_inv_le_u hu_entry
  have hdiv :
      (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ /
          higham9_13_complexMaxEntryNorm hn A ≤
        higham9_13_complexMaxEntryNorm hn U /
          higham9_13_complexMaxEntryNorm hn A :=
    div_le_div_of_nonneg_right hbeta_inv_le_U (le_of_lt hA)
  have htheta :
      1 / (higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv) =
        (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ /
          higham9_13_complexMaxEntryNorm hn A := by
    field_simp [ne_of_gt hA, ne_of_gt hAinv]
  calc
    1 / (higham9_13_complexMaxEntryNorm hn A *
        higham9_13_complexMaxEntryNorm hn A_inv)
        = (higham9_13_complexMaxEntryNorm hn A_inv)⁻¹ /
          higham9_13_complexMaxEntryNorm hn A := htheta
    _ ≤ higham9_13_complexMaxEntryNorm hn U /
          higham9_13_complexMaxEntryNorm hn A := hdiv
    _ = higham9_13_complexGrowthFactorEntry hn A U := rfl

/-- **Equation (9.13)**, Fourier/Vandermonde growth lower-bound bridge.

For the source matrix `V_n`, the already-proved theta identity turns the
complex Theorem 9.8 bridge into `n <= rho`, once a pivoting trace supplies a
final-pivot inverse-entry witness.  The later complete-pivoting construction
theorems discharge that witness for nonsingular inputs. -/
theorem higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card
    {n : ℕ} (hn : 0 < n)
    (U : Fin n → Fin n → ℂ) (u : ℂ)
    (hu_pos : 0 < ‖u‖)
    (hu_entry : ‖u‖ ≤ higham9_13_complexMaxEntryNorm hn U)
    (hu_inv_entry :
      ∃ i j : Fin n, u⁻¹ =
        higham9_13_fourierVandermondeScaledAdjoint n i j) :
    (n : ℝ) ≤
      higham9_13_complexGrowthFactorEntry hn
        (higham9_13_fourierVandermonde n) U := by
  have hA :
      0 < higham9_13_complexMaxEntryNorm hn
        (higham9_13_fourierVandermonde n) := by
    rw [higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one hn]
    norm_num
  have hAinv :
      0 < higham9_13_complexMaxEntryNorm hn
        (higham9_13_fourierVandermondeScaledAdjoint n) := by
    rw [higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv hn]
    exact inv_pos.mpr (by exact_mod_cast hn)
  have htheta :=
    higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta hn
      (higham9_13_fourierVandermonde n)
      (higham9_13_fourierVandermondeScaledAdjoint n) U
      hA hAinv u hu_pos hu_entry hu_inv_entry
  rw [higham9_13_fourierVandermonde_theta_eq_card hn] at htheta
  exact htheta

/-- Complex right-inverse predicate for the local complex complete-pivoting
certificate branch of Theorem 9.8/equation (9.13). -/
def higham9_8_ComplexIsRightInverse (n : ℕ)
    (T T_inv : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, ∑ k : Fin n, T i k * T_inv k j = if i = j then 1 else 0

/-- Complex left-inverse predicate for the local complex complete-pivoting
certificate branch of Theorem 9.8/equation (9.13). -/
def higham9_8_ComplexIsLeftInverse (n : ℕ)
    (T T_inv : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, ∑ k : Fin n, T_inv i k * T k j = if i = j then 1 else 0

/-- Complex row/column permutation used for the certificate-level version of
equation (9.13). -/
def higham9_2_complexRowColPermutedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℂ) (sigma tau : Fin n → Fin n) :
    Fin n → Fin n → ℂ :=
  fun i j => A (sigma i) (tau j)

/-- Complex transpose in the repository's function-shaped matrix style. -/
def higham9_8_complexFiniteTranspose {ι κ : Type*} (M : ι → κ → ℂ) :
    κ → ι → ℂ :=
  fun j i => M i j

/-- Complex LU certificate used only for the complex Fourier/Vandermonde
complete-pivoting bridge.  It mirrors the real `LUFactSpec` surface but avoids
claiming that the real-valued LU trace infrastructure has been generalized. -/
structure higham9_8_ComplexLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) : Prop where
  L_diag : ∀ i : Fin n, L i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  product_eq : ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j = A i j

/-- Complex `PAQ = LU` certificate for equation (9.13).  This is a certificate
surface, not a construction of the complex complete-pivoting trace. -/
structure higham9_8_ComplexCompletePermutedLUFactSpec (n : ℕ)
    (A L U : Fin n → Fin n → ℂ) (sigma tau : Fin n → Fin n) : Prop where
  row_perm : IsPermutation n sigma
  col_perm : IsPermutation n tau
  L_diag : ∀ i : Fin n, L i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0
  product_eq :
    ∀ i j : Fin n, ∑ k : Fin n, L i k * U k j =
      higham9_2_complexRowColPermutedMatrix A sigma tau i j

/-- Complex complete-pivoting first-stage choice, ordered by complex entry
norms.  This is the complex analogue of `higham9_1_completePivotChoice` used
only for the equation (9.13) Fourier/Vandermonde branch. -/
def higham9_8_complexCompletePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℂ) (k r s : Fin n) : Prop :=
  k.val ≤ r.val ∧ k.val ≤ s.val ∧
    ∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
      ‖Astage i j‖ ≤ ‖Astage r s‖

/-- A complex complete-pivoting maximum exists on the finite active submatrix. -/
theorem higham9_8_exists_complexCompletePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℂ) (k : Fin n) :
    ∃ r s : Fin n, higham9_8_complexCompletePivotChoice Astage k r s := by
  classical
  let active : Finset (Fin n × Fin n) :=
    Finset.univ.filter fun p => k.val ≤ p.1.val ∧ k.val ≤ p.2.val
  have hactive : active.Nonempty := by
    refine ⟨(k, k), ?_⟩
    simp [active]
  obtain ⟨p, hp_mem, hp_max⟩ :=
    Finset.exists_max_image active
      (fun p : Fin n × Fin n => ‖Astage p.1 p.2‖)
      hactive
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hp_mem).2.1
  · exact (Finset.mem_filter.mp hp_mem).2.2
  · intro i j hi hj
    exact hp_max (i, j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), ⟨hi, hj⟩⟩)

/-- A complex complete-pivoting maximum is nonzero if the active submatrix
contains a nonzero entry. -/
theorem higham9_8_complexCompletePivotChoice_pivot_ne_zero_of_exists {n : ℕ}
    (Astage : Fin n → Fin n → ℂ) (k r s : Fin n)
    (hchoice : higham9_8_complexCompletePivotChoice Astage k r s)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    Astage r s ≠ 0 := by
  rcases hactive with ⟨i, j, hi, hj, hne⟩
  intro hrs
  have hle : ‖Astage i j‖ ≤ 0 := by
    simpa [hrs] using hchoice.2.2 i j hi hj
  have hzero : ‖Astage i j‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact hne (norm_eq_zero.mp hzero)

/-- A complex active matrix with nonzero determinant has at least one nonzero
entry. -/
theorem higham9_8_complex_exists_entry_ne_zero_of_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    ∃ i j : Fin (m + 1), A i j ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hzero :
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 0 := by
    ext i j
    exact hnone i j
  rw [hzero] at hdet
  have hdet_zero :
      Matrix.det (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 0 := by
    rw [Matrix.det_zero]
    exact ⟨0⟩
  exact hdet hdet_zero

/-- A nonsingular complex matrix admits a nonzero first complete pivot. -/
theorem higham9_8_exists_first_complexCompletePivotChoice_pivot_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    ∃ r s : Fin (m + 1),
      higham9_8_complexCompletePivotChoice A 0 r s ∧ A r s ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    higham9_8_complex_exists_entry_ne_zero_of_det_ne_zero A hdet
  obtain ⟨r, s, hchoice⟩ :=
    higham9_8_exists_complexCompletePivotChoice A 0
  exact ⟨r, s, hchoice,
    higham9_8_complexCompletePivotChoice_pivot_ne_zero_of_exists
      A 0 r s hchoice
      ⟨i, j, Nat.zero_le i.val, Nat.zero_le j.val, hij⟩⟩

/-- Complex first Schur complement after a no-pivot first step. -/
noncomputable def higham9_8_complexFirstSchurComplement {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ) :
    Fin m → Fin m → ℂ :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

/-- Explicit complex lower factor for one exact no-pivot LU construction step. -/
noncomputable def higham9_8_complexLUFirstStepL {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (L₁ : Fin m → Fin m → ℂ) : Fin (m + 1) → Fin (m + 1) → ℂ :=
  fun i j =>
    if hi : i = 0 then
      if _hj : j = 0 then 1 else 0
    else
      if hj : j = 0 then A i 0 / A 0 0 else L₁ (i.pred hi) (j.pred hj)

/-- Explicit complex upper factor for one exact no-pivot LU construction step. -/
noncomputable def higham9_8_complexLUFirstStepU {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (U₁ : Fin m → Fin m → ℂ) : Fin (m + 1) → Fin (m + 1) → ℂ :=
  fun i j =>
    if hi : i = 0 then A 0 j
    else
      if hj : j = 0 then 0 else U₁ (i.pred hi) (j.pred hj)

/-- One exact complex no-pivot LU construction step. -/
theorem higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ}
    (hpivot : A 0 0 ≠ 0)
    {L₁ U₁ : Fin m → Fin m → ℂ}
    (hS :
      higham9_8_ComplexLUFactSpec m
        (higham9_8_complexFirstSchurComplement A) L₁ U₁) :
    higham9_8_ComplexLUFactSpec (m + 1) A
      (higham9_8_complexLUFirstStepL A L₁)
      (higham9_8_complexLUFirstStepU A U₁) := by
  classical
  let L : Fin (m + 1) → Fin (m + 1) → ℂ :=
    higham9_8_complexLUFirstStepL A L₁
  let U : Fin (m + 1) → Fin (m + 1) → ℂ :=
    higham9_8_complexLUFirstStepU A U₁
  change higham9_8_ComplexLUFactSpec (m + 1) A L U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      simp [L, higham9_8_complexLUFirstStepL]
    · simp [L, higham9_8_complexLUFirstStepL, hi, hS.L_diag]
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by
        intro h
        subst h
        exact (Nat.lt_irrefl 0 hij).elim
      simp [L, higham9_8_complexLUFirstStepL, hj]
    · have hj : j ≠ 0 := by
        intro h
        subst h
        exact (Nat.not_lt_zero _ hij).elim
      simp only [L, higham9_8_complexLUFirstStepL, dif_neg hi, dif_neg hj]
      exact hS.L_upper_zero (i.pred hi) (j.pred hj) (by
        have hival := Fin.val_pred i hi
        have hjval := Fin.val_pred j hj
        have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      exact (Nat.not_lt_zero _ hij).elim
    · by_cases hj : j = 0
      · subst hj
        simp [U, higham9_8_complexLUFirstStepU, hi]
      · simp only [U, higham9_8_complexLUFirstStepU, dif_neg hi, dif_neg hj]
        exact hS.U_lower_zero (i.pred hi) (j.pred hj) (by
          have hival := Fin.val_pred i hi
          have hjval := Fin.val_pred j hj
          have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
  · intro i j
    rw [Fin.sum_univ_succ]
    have hL0 : ∀ p : Fin (m + 1), L 0 p = if p = 0 then 1 else 0 := by
      intro p
      simp [L, higham9_8_complexLUFirstStepL]
    have hU0 : ∀ p : Fin (m + 1), U 0 p = A 0 p := by
      intro p
      simp [U, higham9_8_complexLUFirstStepU]
    have hL0s : ∀ k : Fin m, L 0 k.succ = 0 := by
      intro k
      rw [hL0]
      simp [Fin.succ_ne_zero]
    have hLs0 : ∀ k : Fin m, L k.succ 0 = A k.succ 0 / A 0 0 := by
      intro k
      simp [L, higham9_8_complexLUFirstStepL, Fin.succ_ne_zero]
    have hUs0 : ∀ k : Fin m, U k.succ 0 = 0 := by
      intro k
      simp [U, higham9_8_complexLUFirstStepU, Fin.succ_ne_zero]
    have hLss : ∀ p q : Fin m, L p.succ q.succ = L₁ p q := by
      intro p q
      simp [L, higham9_8_complexLUFirstStepL, Fin.succ_ne_zero, Fin.pred_succ]
    have hUss : ∀ p q : Fin m, U p.succ q.succ = U₁ p q := by
      intro p q
      simp [U, higham9_8_complexLUFirstStepU, Fin.succ_ne_zero, Fin.pred_succ]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi
      subst hj
      rw [hL0 0, hU0 0]
      have hzero :
          (∑ x : Fin m, L 0 x.succ * U x.succ 0) = 0 := by
        simp [hL0s]
      rw [hzero]
      simp
    · subst hi
      rw [hL0 0, hU0 j]
      have hzero :
          (∑ x : Fin m, L 0 x.succ * U x.succ j) = 0 := by
        simp [hL0s]
      rw [hzero]
      simp
    · subst hj
      rw [hU0 0]
      have hzero :
          (∑ x : Fin m, L i x.succ * U x.succ 0) = 0 := by
        simp [hUs0]
      have hLi0 : L i 0 = A i 0 / A 0 0 := by
        have h := hLs0 (i.pred hi)
        simpa [Fin.succ_pred i hi] using h
      rw [hzero, hLi0]
      field_simp [hpivot]
      ring
    · rw [hU0 j]
      have hprod := hS.product_eq (i.pred hi) (j.pred hj)
      have hsucc :
          (∑ x : Fin m, L i x.succ * U x.succ j) =
            ∑ x : Fin m, L₁ (i.pred hi) x * U₁ x (j.pred hj) := by
        apply Finset.sum_congr rfl
        intro x _
        have hLix : L i x.succ = L₁ (i.pred hi) x := by
          have h := hLss (i.pred hi) x
          simpa [Fin.succ_pred i hi] using h
        have hUxj : U x.succ j = U₁ x (j.pred hj) := by
          have h := hUss x (j.pred hj)
          simpa [Fin.succ_pred j hj] using h
        rw [hLix, hUxj]
      have hLi0 : L i 0 = A i 0 / A 0 0 := by
        have h := hLs0 (i.pred hi)
        simpa [Fin.succ_pred i hi] using h
      rw [hLi0, hsucc, hprod]
      simp only [higham9_8_complexFirstSchurComplement, Fin.succ_pred]
      field_simp [hpivot]
      ring

/-- Complex row/column swaps moving a first complete pivot to `(0,0)` preserve
nonsingularity. -/
theorem higham9_8_complex_firstPivotRowColSwap_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (r s : Fin (m + 1))
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (higham9_2_complexRowColPermutedMatrix A
          (higham9_7_firstPivotRowSwap r)
          (higham9_7_firstPivotRowSwap s)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0 := by
  classical
  let sigma := higham9_7_firstPivotRowSwap r
  let tau := higham9_7_firstPivotRowSwap s
  let B : Fin (m + 1) → Fin (m + 1) → ℂ := fun i j => A (sigma i) j
  have hB_det :
      Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0 := by
    let e : Equiv.Perm (Fin (m + 1)) :=
      Equiv.ofBijective sigma (higham9_7_firstPivotRowSwap_isPermutation r)
    have hdet_eq :
        Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
          ((Equiv.Perm.sign e : ℤ) : ℂ) *
            Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
      have hperm :=
        Matrix.det_permute (R := ℂ) e
          (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      simpa [B, e, sigma, Matrix.of_apply] using hperm
    rw [hdet_eq]
    exact mul_ne_zero (by simp) hdet
  let eTau : Equiv.Perm (Fin (m + 1)) :=
    Equiv.ofBijective tau (higham9_7_firstPivotRowSwap_isPermutation s)
  have hdet_eq :
      Matrix.det
        (Matrix.of
          (higham9_2_complexRowColPermutedMatrix A sigma tau) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
        ((Equiv.Perm.sign eTau : ℤ) : ℂ) *
          Matrix.det (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    have hperm :=
      Matrix.det_permute' eTau
        (Matrix.of B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    simpa [B, sigma, tau, eTau, higham9_2_complexRowColPermutedMatrix,
      Matrix.of_apply] using hperm
  rw [hdet_eq]
  exact mul_ne_zero (by simp) hB_det

/-- If a complex matrix is nonsingular and its leading pivot is nonzero, then
the first Schur complement is nonsingular. -/
theorem higham9_8_complexFirstSchurComplement_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hpivot : A 0 0 ≠ 0)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_8_complexFirstSchurComplement A) :
        Matrix (Fin m) (Fin m) ℂ) ≠ 0 := by
  classical
  let A11 : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => A 0 0
  let B : Matrix (Fin 1) (Fin m) ℂ := fun _ c => A 0 c.succ
  let C : Matrix (Fin m) (Fin 1) ℂ := fun r _ => A r.succ 0
  let D : Matrix (Fin m) (Fin m) ℂ := fun r c => A r.succ c.succ
  have hdetA11 : Matrix.det A11 = A 0 0 := by
    simp [A11]
  have hdetA11_ne : Matrix.det A11 ≠ 0 := by
    simpa [hdetA11] using hpivot
  letI : Invertible (Matrix.det A11) := invertibleOfNonzero hdetA11_ne
  letI : Invertible A11 := Matrix.invertibleOfDetInvertible A11
  have hA11_inv : ⅟A11 = (fun _ _ : Fin 1 => (A 0 0)⁻¹) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [A11]
  have hschur :
      Matrix.det (Matrix.fromBlocks A11 B C D) =
        A 0 0 *
          Matrix.det
            (Matrix.of (higham9_8_complexFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℂ) := by
    rw [Matrix.det_fromBlocks₁₁, hdetA11]
    congr 1
    apply congrArg Matrix.det
    ext r c
    simp [A11, B, C, D, hA11_inv, higham9_8_complexFirstSchurComplement,
      Matrix.mul_apply]
    rw [div_eq_mul_inv]
    ring_nf
  have hdetBlock :
      Matrix.det (Matrix.fromBlocks A11 B C D) =
        Matrix.det ((Matrix.fromBlocks A11 B C D).submatrix
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)) :=
    (Matrix.det_submatrix_equiv_self
      (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)
      (Matrix.fromBlocks A11 B C D)).symm
  have hsub :
      (Matrix.fromBlocks A11 B C D).submatrix
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m)
          (finSumFinEquiv.symm : Fin (1 + m) ≃ Fin 1 ⊕ Fin m) =
        (Matrix.of (fun i j : Fin (1 + m) =>
          A (finCongr (Nat.add_comm 1 m) i)
            (finCongr (Nat.add_comm 1 m) j)) :
          Matrix (Fin (1 + m)) (Fin (1 + m)) ℂ) := by
    have hcast_zero :
        finCongr (Nat.add_comm 1 m) (Fin.castAdd m (0 : Fin 1)) =
          (0 : Fin (m + 1)) := by
      ext
      simp
    have hcast_zero' :
        Fin.cast (Nat.add_comm 1 m) (Fin.castAdd m (0 : Fin 1)) =
          (0 : Fin (m + 1)) := by
      ext
      simp [Fin.cast]
    ext r c
    cases r using Fin.addCases with
    | left r0 =>
        fin_cases r0
        cases c using Fin.addCases with
        | left c0 =>
            fin_cases c0
            simp [A11, B, C, D]
            rw [hcast_zero']
        | right c0 =>
            simp [A11, B, C, D]
            rw [hcast_zero']
    | right r0 =>
        cases c using Fin.addCases with
        | left c0 =>
            fin_cases c0
            simp [A11, B, C, D]
            rw [hcast_zero']
        | right c0 =>
            simp [A11, B, C, D]
  have hdetA_eq :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
        A 0 0 *
          Matrix.det
            (Matrix.of (higham9_8_complexFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℂ) := by
    calc
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
          =
        Matrix.det
          (Matrix.of (fun i j : Fin (1 + m) =>
            A (finCongr (Nat.add_comm 1 m) i)
              (finCongr (Nat.add_comm 1 m) j)) :
            Matrix (Fin (1 + m)) (Fin (1 + m)) ℂ) := by
            change
              Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
                Matrix.det
                  ((Matrix.of A :
                    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix
                    (finCongr (Nat.add_comm 1 m) : Fin (1 + m) ≃ Fin (m + 1))
                    (finCongr (Nat.add_comm 1 m) : Fin (1 + m) ≃ Fin (m + 1)))
            exact
              (Matrix.det_submatrix_equiv_self
                (finCongr (Nat.add_comm 1 m) : Fin (1 + m) ≃ Fin (m + 1))
                (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).symm
      _ = Matrix.det (Matrix.fromBlocks A11 B C D) := by
            rw [← hsub, ← hdetBlock]
      _ = A 0 0 *
          Matrix.det
            (Matrix.of (higham9_8_complexFirstSchurComplement A) :
              Matrix (Fin m) (Fin m) ℂ) := hschur
  intro hSzero
  apply hdet
  rw [hdetA_eq, hSzero, mul_zero]

/-- A complex `PAQ = LU` certificate is an ordinary complex LU certificate for
the row-and-column permuted matrix. -/
theorem higham9_8_complexCompletePermutedLUFactSpec_to_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℂ} {sigma tau : Fin n → Fin n}
    (hLU : higham9_8_ComplexCompletePermutedLUFactSpec n A L U sigma tau) :
    higham9_8_ComplexLUFactSpec n
      (higham9_2_complexRowColPermutedMatrix A sigma tau) L U where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  product_eq := hLU.product_eq

/-- Complex right-inverse transport through row and column permutations. -/
theorem higham9_2_complexRowColPermutedMatrix_right_inverse {n : ℕ}
    {A A_inv : Fin n → Fin n → ℂ} {sigma tau : Fin n → Fin n}
    (hsigma : IsPermutation n sigma) (htau : IsPermutation n tau)
    (hRight : higham9_8_ComplexIsRightInverse n A A_inv) :
    higham9_8_ComplexIsRightInverse n
      (higham9_2_complexRowColPermutedMatrix A sigma tau)
      (fun i j => A_inv (tau i) (sigma j)) := by
  classical
  intro i j
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau htau
  have hsum :
      (∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j)) =
        ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := by
    simpa [eTau] using
      (Equiv.sum_comp eTau
        (fun k : Fin n => A (sigma i) k * A_inv k (sigma j)))
  calc
    ∑ k : Fin n,
        higham9_2_complexRowColPermutedMatrix A sigma tau i k *
          (fun i j => A_inv (tau i) (sigma j)) k j
        = ∑ k : Fin n, A (sigma i) (tau k) * A_inv (tau k) (sigma j) := by
            simp [higham9_2_complexRowColPermutedMatrix]
    _ = ∑ k : Fin n, A (sigma i) k * A_inv k (sigma j) := hsum
    _ = (if sigma i = sigma j then (1 : ℂ) else 0) := hRight (sigma i) (sigma j)
    _ = (if i = j then (1 : ℂ) else 0) := by
      by_cases hij : i = j
      · simp [hij]
      · have hsne : sigma i ≠ sigma j := by
          intro hs
          exact hij (hsigma.injective hs)
        simp [hij, hsne]

/-- Transposing a complex right inverse gives a complex left inverse. -/
theorem higham9_8_complex_isLeftInverse_finiteTranspose_of_isRightInverse {n : ℕ}
    {T T_inv : Fin n → Fin n → ℂ}
    (hInv : higham9_8_ComplexIsRightInverse n T T_inv) :
    higham9_8_ComplexIsLeftInverse n
      (higham9_8_complexFiniteTranspose T)
      (higham9_8_complexFiniteTranspose T_inv) := by
  intro i j
  have h := hInv j i
  calc
    ∑ k : Fin n,
        higham9_8_complexFiniteTranspose T_inv i k *
          higham9_8_complexFiniteTranspose T k j
        = ∑ k : Fin n, T j k * T_inv k i := by
            apply Finset.sum_congr rfl
            intro k _
            simp [higham9_8_complexFiniteTranspose, mul_comm]
    _ = if j = i then 1 else 0 := h
    _ = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · simp [hij]
      · have hji : j ≠ i := by exact fun h => hij h.symm
        simp [hij, hji]

/-- The left inverse of a complex upper triangular matrix is upper triangular.
This local complex analogue supports the equation (9.13) final-pivot bridge. -/
theorem higham9_8_complex_inv_upper_tri (n : ℕ)
    (U U_inv : Fin n → Fin n → ℂ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : higham9_8_ComplexIsLeftInverse n U U_inv) :
    ∀ i j : Fin n, j.val < i.val → U_inv i j = 0 := by
  suffices ∀ (jv : ℕ) (hjv : jv < n), ∀ i : Fin n, jv < i.val →
      U_inv i ⟨jv, hjv⟩ = 0 by
    intro i j hij
    exact this j.val j.isLt i hij
  intro jv hjv i hi
  revert hjv i
  refine Nat.strongRecOn jv ?_
  intro jv ih hjv i hi
  let j : Fin n := ⟨jv, hjv⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [j]; omega)
  have h := hInv i j
  simp [hij] at h
  have hterm : U_inv i j * U j j = 0 := by
    suffices ∑ k : Fin n, U_inv i k * U k j = U_inv i j * U j j by
      simpa [this] using h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hzero :
        ∑ k ∈ Finset.univ.erase j, U_inv i k * U k j = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne := Finset.ne_of_mem_erase hk
      by_cases hklt : k.val < jv
      · have hki : k.val < i.val := by omega
        rw [ih k.val hklt k.isLt i hki, zero_mul]
      · push_neg at hklt
        have hjk : jv < k.val := by
          by_contra hc
          push_neg at hc
          have hval : k.val = jv := le_antisymm hc hklt
          exact hk_ne (Fin.ext (by simp [j, hval]))
        rw [hUT k j (by simpa [j] using hjk), mul_zero]
    simp [hzero]
  exact (mul_eq_zero.mp hterm).elim id (fun hdiag => absurd hdiag (hU_diag j))

/-- Diagonal entries of a complex upper-triangular inverse. -/
theorem higham9_8_complex_inv_diag_entry (n : ℕ)
    (U U_inv : Fin n → Fin n → ℂ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hInv : higham9_8_ComplexIsLeftInverse n U U_inv)
    (hInv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0) :
    ∀ i : Fin n, U_inv i i = 1 / U i i := by
  intro i
  have h := hInv i i
  simp at h
  have honly : ∑ k : Fin n, U_inv i k * U k i = U_inv i i * U i i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hzero :
        ∑ k ∈ Finset.univ.erase i, U_inv i k * U k i = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hlt : k.val < i.val
      · rw [hInv_ut i k hlt, zero_mul]
      · push_neg at hlt
        have hk_ne := Finset.ne_of_mem_erase hk
        have hik : i.val < k.val := by
          exact lt_of_le_of_ne hlt (fun hval => hk_ne (Fin.ext hval.symm))
        rw [hUT k i hik, mul_zero]
    simp [hzero]
  rw [honly] at h
  have hmul : U_inv i i * U i i = 1 := h
  field_simp [hU_diag i] at hmul ⊢
  simpa [div_eq_mul_inv, mul_comm] using hmul

/-- Complex final-pivot identity for an exact no-pivot LU certificate. -/
theorem higham9_8_complex_finalPivot_mul_inverse_entry_eq_one {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℂ)
    (hLU : higham9_8_ComplexLUFactSpec (m + 1) A L U)
    (hRight : higham9_8_ComplexIsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (Fin.last m) (Fin.last m) = 1 := by
  classical
  let n := m + 1
  let last : Fin n := Fin.last m
  let Y : Fin n → Fin n → ℂ := fun i j => ∑ k : Fin n, U i k * A_inv k j
  have hYRight : higham9_8_ComplexIsRightInverse n L Y := by
    intro i j
    have hassoc :
        ∑ k : Fin n, L i k * Y k j =
          ∑ k : Fin n, A i k * A_inv k j := by
      calc
        ∑ k : Fin n, L i k * Y k j
            = ∑ k : Fin n, ∑ l : Fin n, L i k * (U k l * A_inv l j) := by
                apply Finset.sum_congr rfl
                intro k _
                simp [Y, Finset.mul_sum]
        _ = ∑ l : Fin n, ∑ k : Fin n, L i k * (U k l * A_inv l j) := by
              exact Finset.sum_comm
        _ = ∑ l : Fin n, (∑ k : Fin n, L i k * U k l) * A_inv l j := by
              apply Finset.sum_congr rfl
              intro l _
              calc
                ∑ k : Fin n, L i k * (U k l * A_inv l j)
                    = ∑ k : Fin n, (L i k * U k l) * A_inv l j := by
                        apply Finset.sum_congr rfl
                        intro k _
                        ring
                _ = (∑ k : Fin n, L i k * U k l) * A_inv l j := by
                        rw [Finset.sum_mul]
        _ = ∑ l : Fin n, A i l * A_inv l j := by
              apply Finset.sum_congr rfl
              intro l _
              rw [hLU.product_eq i l]
    calc
      ∑ k : Fin n, L i k * Y k j
          = ∑ k : Fin n, A i k * A_inv k j := hassoc
      _ = if i = j then 1 else 0 := hRight i j
  have hLT_transpose :
      ∀ i j : Fin n, j.val < i.val →
        higham9_8_complexFiniteTranspose L i j = 0 := by
    intro i j hji
    exact hLU.L_upper_zero j i (by simpa [higham9_8_complexFiniteTranspose] using hji)
  have hL_diag_ne :
      ∀ i : Fin n, higham9_8_complexFiniteTranspose L i i ≠ 0 := by
    intro i
    simp [higham9_8_complexFiniteTranspose, hLU.L_diag i]
  have hYLeftT :
      higham9_8_ComplexIsLeftInverse n
        (higham9_8_complexFiniteTranspose L)
        (higham9_8_complexFiniteTranspose Y) :=
    higham9_8_complex_isLeftInverse_finiteTranspose_of_isRightInverse hYRight
  have hYt_upper :
      ∀ i j : Fin n, j.val < i.val →
        higham9_8_complexFiniteTranspose Y i j = 0 :=
    higham9_8_complex_inv_upper_tri n
      (higham9_8_complexFiniteTranspose L)
      (higham9_8_complexFiniteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT
  have hYt_diag :
      ∀ i : Fin n, higham9_8_complexFiniteTranspose Y i i =
        1 / higham9_8_complexFiniteTranspose L i i :=
    higham9_8_complex_inv_diag_entry n
      (higham9_8_complexFiniteTranspose L)
      (higham9_8_complexFiniteTranspose Y)
      hLT_transpose hL_diag_ne hYLeftT hYt_upper
  have hY_last_diag : Y last last = 1 := by
    have h := hYt_diag last
    simpa [higham9_8_complexFiniteTranspose, hLU.L_diag last] using h
  have hY_last_last :
      Y last last =
        U last last * A_inv last last := by
    unfold Y
    exact Finset.sum_eq_single last
      (fun k _ hk => by
        have hk_val_ne : k.val ≠ last.val := by
          intro hval
          exact hk (Fin.ext hval)
        have hk_lt : k.val < last.val := by
          have hlast_val : last.val = m := by simp [last]
          have hk_le : k.val ≤ m := Nat.le_of_lt_succ k.isLt
          have hk_ne_m : k.val ≠ m := by
            intro hkm
            exact hk_val_ne (by simpa [hlast_val] using hkm)
          have hk_lt_m : k.val < m := lt_of_le_of_ne hk_le hk_ne_m
          simpa [hlast_val] using hk_lt_m
        rw [hLU.U_lower_zero last k (by simpa [last] using hk_lt), zero_mul])
      (fun hnot => (hnot (Finset.mem_univ last)).elim)
  rw [hY_last_last] at hY_last_diag
  exact hY_last_diag

/-- Complex final-pivot inverse-entry identity for an explicit complex
complete-pivoting certificate `P A Q = L U`. -/
theorem higham9_8_complex_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
    {m : ℕ}
    (A A_inv L U : Fin (m + 1) → Fin (m + 1) → ℂ)
    (sigma tau : Fin (m + 1) → Fin (m + 1))
    (hLU :
      higham9_8_ComplexCompletePermutedLUFactSpec (m + 1) A L U sigma tau)
    (hRight : higham9_8_ComplexIsRightInverse (m + 1) A A_inv) :
    U (Fin.last m) (Fin.last m) *
      A_inv (tau (Fin.last m)) (sigma (Fin.last m)) = 1 := by
  classical
  let B : Fin (m + 1) → Fin (m + 1) → ℂ :=
    higham9_2_complexRowColPermutedMatrix A sigma tau
  let B_inv : Fin (m + 1) → Fin (m + 1) → ℂ :=
    fun i j => A_inv (tau i) (sigma j)
  have hBRight : higham9_8_ComplexIsRightInverse (m + 1) B B_inv :=
    higham9_2_complexRowColPermutedMatrix_right_inverse hLU.row_perm hLU.col_perm hRight
  have hBLU : higham9_8_ComplexLUFactSpec (m + 1) B L U :=
    higham9_8_complexCompletePermutedLUFactSpec_to_LUFactSpec hLU
  simpa [B, B_inv] using
    higham9_8_complex_finalPivot_mul_inverse_entry_eq_one B B_inv L U hBLU hBRight

/-- **Equation (9.13)**, Fourier/Vandermonde growth lower bound from an
explicit complex complete-pivoting certificate.

This removes the final-pivot inverse-entry witness hypothesis from
`higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card`; it still does
not itself construct the complex complete-pivoting trace or certificate; those
are supplied by the later existence theorems. -/
theorem higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_completePermutedLUFactSpec
    {n : ℕ} (hn : 0 < n)
    (L U : Fin n → Fin n → ℂ) (sigma tau : Fin n → Fin n)
    (hLU :
      higham9_8_ComplexCompletePermutedLUFactSpec n
        (higham9_13_fourierVandermonde n) L U sigma tau) :
    (n : ℝ) ≤
      higham9_13_complexGrowthFactorEntry hn
        (higham9_13_fourierVandermonde n) U := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | succ m =>
      let V : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_13_fourierVandermonde (m + 1)
      let V_inv : Fin (m + 1) → Fin (m + 1) → ℂ :=
        higham9_13_fourierVandermondeScaledAdjoint (m + 1)
      have hRight : higham9_8_ComplexIsRightInverse (m + 1) V V_inv := by
        exact (higham9_13_fourierVandermonde_inverse_formula (m + 1)).2
      let last : Fin (m + 1) := Fin.last m
      let u : ℂ := U last last
      have hprod :
          u * V_inv (tau last) (sigma last) = 1 := by
        simpa [u, V, V_inv, last] using
          higham9_8_complex_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec
            V V_inv L U sigma tau hLU hRight
      have hu_ne : u ≠ 0 := by
        intro hu
        rw [hu] at hprod
        norm_num at hprod
      have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
      have hu_entry :
          ‖u‖ ≤ higham9_13_complexMaxEntryNorm (Nat.succ_pos m) U := by
        simpa [u, last] using
          higham9_13_entry_norm_le_complexMaxEntryNorm
            (Nat.succ_pos m) U last last
      have hentry_eq : u⁻¹ = V_inv (tau last) (sigma last) := by
        exact (eq_inv_of_mul_eq_one_right hprod).symm
      have hu_inv_entry :
          ∃ i j : Fin (m + 1), u⁻¹ = V_inv i j :=
        ⟨tau last, sigma last, hentry_eq⟩
      simpa [V, V_inv] using
        higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card
          (Nat.succ_pos m) U u hu_pos hu_entry hu_inv_entry

/-- **Problem 9.11**, the doubled block matrix
`B = [[A, A], [A, -A]]`, represented as a `2 × 2` block matrix. -/
def higham9_11_blockMatrix {n : ℕ} (A : Fin n → Fin n → ℝ) :
    Fin 2 → Fin 2 → (Fin n → Fin n → ℝ) :=
  fun bi bj i j => if bi = (1 : Fin 2) ∧ bj = (1 : Fin 2) then -A i j else A i j

/-- **Problem 9.11**, the displayed inverse candidate
`(1/2) [[A⁻¹, A⁻¹], [A⁻¹, -A⁻¹]]`. -/
noncomputable def higham9_11_blockInverseCandidate {n : ℕ} (A_inv : Fin n → Fin n → ℝ) :
    Fin 2 → Fin 2 → (Fin n → Fin n → ℝ) :=
  fun bi bj i j => (1 / 2 : ℝ) * higham9_11_blockMatrix A_inv bi bj i j

/-- Row/column block selector for flattening a `2 × 2` block matrix with
`n × n` blocks into an ordinary `(2n) × (2n)` matrix. -/
def higham9_11_flatBlockIndex {n : ℕ} (i : Fin (2 * n)) : Fin 2 :=
  if i.val < n then 0 else 1

/-- Intra-block row/column selector for flattening a `2 × 2` block matrix with
`n × n` blocks into an ordinary `(2n) × (2n)` matrix. -/
def higham9_11_flatInnerIndex {n : ℕ} (_hn : 0 < n) (i : Fin (2 * n)) : Fin n :=
  if hi : i.val < n then
    ⟨i.val, hi⟩
  else
    ⟨i.val - n, by
      have hi_lt : i.val < 2 * n := i.isLt
      have hni : n ≤ i.val := le_of_not_gt hi
      omega⟩

/-- **Problem 9.11**, flatten the displayed `2 × 2` block matrix into the
ordinary `Fin (2n)` matrix surface used by the complete-pivoting growth
family. -/
def higham9_11_flattenTwoBlock {n : ℕ} (hn : 0 < n)
    (B : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ)) :
    Fin (2 * n) → Fin (2 * n) → ℝ :=
  fun i j =>
    B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
      (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)

/-- Inverse direction for `higham9_11_flattenTwoBlock`: embed a block row or
column index and an in-block row or column into the flattened `Fin (2 * n)`
surface. -/
def higham9_11_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (bi : Fin 2) (i : Fin n) : Fin (2 * n) :=
  ⟨bi.val * n + i.val, by
    have hi : i.val < n := i.isLt
    fin_cases bi <;> simp <;> omega⟩

lemma higham9_11_flatBlockIndex_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (bi : Fin 2) (i : Fin n) :
    higham9_11_flatBlockIndex (higham9_11_flatIndexOfBlock hn bi i) = bi := by
  fin_cases bi
  · simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex, i.isLt]
  · simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex]

lemma higham9_11_flatInnerIndex_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (bi : Fin 2) (i : Fin n) :
    higham9_11_flatInnerIndex hn (higham9_11_flatIndexOfBlock hn bi i) = i := by
  fin_cases bi
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatInnerIndex, i.isLt]
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatInnerIndex]

lemma higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex {n : ℕ}
    (hn : 0 < n) (i : Fin (2 * n)) :
    higham9_11_flatIndexOfBlock hn
        (higham9_11_flatBlockIndex i) (higham9_11_flatInnerIndex hn i) = i := by
  by_cases hi : i.val < n
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex,
      higham9_11_flatInnerIndex, hi]
  · ext
    simp [higham9_11_flatIndexOfBlock, higham9_11_flatBlockIndex,
      higham9_11_flatInnerIndex, hi]
    omega

lemma higham9_11_flatBlockInner_eq_iff {n : ℕ} (hn : 0 < n)
    (i j : Fin (2 * n)) :
    (higham9_11_flatBlockIndex i = higham9_11_flatBlockIndex j ∧
        higham9_11_flatInnerIndex hn i = higham9_11_flatInnerIndex hn j) ↔
      i = j := by
  constructor
  · intro h
    calc
      i =
          higham9_11_flatIndexOfBlock hn
            (higham9_11_flatBlockIndex i) (higham9_11_flatInnerIndex hn i) := by
            rw [higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex]
      _ =
          higham9_11_flatIndexOfBlock hn
            (higham9_11_flatBlockIndex j) (higham9_11_flatInnerIndex hn j) := by
            rw [h.1, h.2]
      _ = j := by
            rw [higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex]
  · intro h
    subst h
    exact ⟨rfl, rfl⟩

/-- **Problem 9.11 support**, the ordinary flattened `Fin (2*n)` index is
equivalent to a block index and an in-block index. -/
noncomputable def higham9_11_flatBlockEquiv {n : ℕ} (hn : 0 < n) :
    (Fin 2 × Fin n) ≃ Fin (2 * n) where
  toFun x := higham9_11_flatIndexOfBlock hn x.1 x.2
  invFun i := (higham9_11_flatBlockIndex i, higham9_11_flatInnerIndex hn i)
  left_inv := by
    intro x
    cases x with
    | mk bi i =>
        simp [higham9_11_flatBlockIndex_flatIndexOfBlock,
          higham9_11_flatInnerIndex_flatIndexOfBlock]
  right_inv := by
    intro i
    exact higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex hn i

lemma higham9_11_flattenTwoBlock_entry_flatIndexOfBlock {n : ℕ} (hn : 0 < n)
    (B : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ))
    (bi bj : Fin 2) (i j : Fin n) :
    higham9_11_flattenTwoBlock hn B
        (higham9_11_flatIndexOfBlock hn bi i)
        (higham9_11_flatIndexOfBlock hn bj j) =
      B bi bj i j := by
  simp [higham9_11_flattenTwoBlock,
    higham9_11_flatBlockIndex_flatIndexOfBlock,
    higham9_11_flatInnerIndex_flatIndexOfBlock]

/-- **Problem 9.11**, flattening preserves Chapter 12's block max-entry norm
as the ordinary max-entry norm of the flattened `Fin (2 * n)` matrix. -/
theorem higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm {n : ℕ}
    (hn : 0 < n) (B : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ)) :
    maxEntryNorm (by omega : 0 < 2 * n) (higham9_11_flattenTwoBlock hn B) =
      blockMaxNorm (by norm_num : 0 < 2) hn B := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have hentry :
        |B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
            (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)| ≤
          maxEntryNorm hn
            (B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)) :=
      entry_le_maxEntryNorm hn
        (B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j))
        (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)
    exact le_trans (by simpa [higham9_11_flattenTwoBlock] using hentry)
      (block_le_blockMaxNorm (by norm_num : 0 < 2) hn B
        (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j))
  · unfold blockMaxNorm
    apply Finset.sup'_le
    intro bi _
    apply Finset.sup'_le
    intro bj _
    conv_lhs => unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have h :=
      entry_le_maxEntryNorm (by omega : 0 < 2 * n)
        (higham9_11_flattenTwoBlock hn B)
        (higham9_11_flatIndexOfBlock hn bi i)
        (higham9_11_flatIndexOfBlock hn bj j)
    simpa [higham9_11_flattenTwoBlock_entry_flatIndexOfBlock] using h

lemma higham9_11_blockMatrix_abs {n : ℕ} (A : Fin n → Fin n → ℝ)
    (bi bj : Fin 2) (i j : Fin n) :
    |higham9_11_blockMatrix A bi bj i j| = |A i j| := by
  unfold higham9_11_blockMatrix
  by_cases h : bi = (1 : Fin 2) ∧ bj = (1 : Fin 2)
  · simp [h]
  · simp [h]

lemma higham9_11_blockInverseCandidate_abs {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (bi bj : Fin 2) (i j : Fin n) :
    |higham9_11_blockInverseCandidate A_inv bi bj i j| =
      (1 / 2 : ℝ) * |A_inv i j| := by
  unfold higham9_11_blockInverseCandidate
  rw [abs_mul, higham9_11_blockMatrix_abs]
  norm_num

private lemma higham9_11_sum_half_add_half {n : ℕ} (f : Fin n → ℝ) :
    (∑ l : Fin n, (1 / 2 : ℝ) * f l) +
      (∑ l : Fin n, (1 / 2 : ℝ) * f l) =
        ∑ l : Fin n, f l := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

private lemma higham9_11_sum_half_add_neg_half {n : ℕ} (f : Fin n → ℝ) :
    (∑ l : Fin n, (1 / 2 : ℝ) * f l) +
      (∑ l : Fin n, -(1 / 2 : ℝ) * f l) =
        0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l _
  ring

/-- **Problem 9.11**, left-inverse half of the displayed identity
`B⁻¹ = (1/2) [[A⁻¹,A⁻¹],[A⁻¹,-A⁻¹]]`. -/
theorem higham9_11_blockInverseCandidate_left {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    ∀ bi bj : Fin 2, ∀ i j : Fin n,
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) bi bj i j =
        if bi = bj then if i = j then 1 else 0 else 0 := by
  intro bi bj i j
  fin_cases bi <;> fin_cases bj
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 0 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A_inv i l * A l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A_inv i l * A l j)
        _ = if i = j then 1 else 0 := hLeft i j
        _ = (if (0 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 0 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A_inv i l * A l j)
        _ = (if (0 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 1 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A_inv i l * A l j)
        _ = (if (1 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockInverseCandidate A_inv)
          (higham9_11_blockMatrix A) 1 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A_inv i l * A l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A_inv i l * A l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A_inv i l * A l j)
        _ = if i = j then 1 else 0 := hLeft i j
        _ = (if (1 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp

/-- **Problem 9.11**, right-inverse half of the displayed identity
`B⁻¹ = (1/2) [[A⁻¹,A⁻¹],[A⁻¹,-A⁻¹]]`. -/
theorem higham9_11_blockInverseCandidate_right {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    ∀ bi bj : Fin 2, ∀ i j : Fin n,
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) bi bj i j =
        if bi = bj then if i = j then 1 else 0 else 0 := by
  intro bi bj i j
  fin_cases bi <;> fin_cases bj
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 0 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A i l * A_inv l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A i l * A_inv l j)
        _ = if i = j then 1 else 0 := hRight i j
        _ = (if (0 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 0 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A i l * A_inv l j)
        _ = (if (0 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 1 0 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, -(1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
              · apply Finset.sum_congr rfl
                intro l _
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix]
                ring
        _ = 0 := higham9_11_sum_half_add_neg_half (fun l : Fin n => A i l * A_inv l j)
        _ = (if (1 : Fin 2) = 0 then if i = j then 1 else 0 else 0) := by simp
  · calc
      blockMatProd (higham9_11_blockMatrix A)
          (higham9_11_blockInverseCandidate A_inv) 1 1 i j
          = (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) +
              (∑ l : Fin n, (1 / 2 : ℝ) * (A i l * A_inv l j)) := by
              rw [blockMatProd, Fin.sum_univ_two]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro l _ <;>
                simp [higham9_11_blockInverseCandidate, higham9_11_blockMatrix] <;>
                ring
        _ = ∑ l : Fin n, A i l * A_inv l j :=
              higham9_11_sum_half_add_half (fun l : Fin n => A i l * A_inv l j)
        _ = if i = j then 1 else 0 := hRight i j
        _ = (if (1 : Fin 2) = 1 then if i = j then 1 else 0 else 0) := by simp

/-- **Problem 9.11 support**, flattening transports block multiplication to
ordinary matrix multiplication on `Fin (2*n)`. -/
theorem higham9_11_flattenTwoBlock_matMul_entry {n : ℕ} (hn : 0 < n)
    (B C : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ))
    (i j : Fin (2 * n)) :
    matMul (2 * n) (higham9_11_flattenTwoBlock hn B)
        (higham9_11_flattenTwoBlock hn C) i j =
      blockMatProd B C
        (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
        (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j) := by
  classical
  unfold matMul blockMatProd higham9_11_flattenTwoBlock
  let e := higham9_11_flatBlockEquiv hn
  rw [← Equiv.sum_comp e
    (fun k : Fin (2 * n) =>
      B (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex k)
          (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn k) *
        C (higham9_11_flatBlockIndex k) (higham9_11_flatBlockIndex j)
          (higham9_11_flatInnerIndex hn k) (higham9_11_flatInnerIndex hn j))]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [e, higham9_11_flatBlockEquiv, higham9_11_flatBlockIndex_flatIndexOfBlock,
    higham9_11_flatInnerIndex_flatIndexOfBlock]

/-- **Problem 9.11 support**, the displayed block right inverse remains a
right inverse after flattening to an ordinary `Fin (2*n)` matrix. -/
theorem higham9_11_flattenTwoBlock_right_inverse {n : ℕ} (hn : 0 < n)
    {B C : Fin 2 → Fin 2 → (Fin n → Fin n → ℝ)}
    (hRight :
      ∀ bi bj : Fin 2, ∀ i j : Fin n,
        blockMatProd B C bi bj i j =
          if bi = bj then if i = j then 1 else 0 else 0) :
    IsRightInverse (2 * n)
      (higham9_11_flattenTwoBlock hn B) (higham9_11_flattenTwoBlock hn C) := by
  intro i j
  change
    matMul (2 * n) (higham9_11_flattenTwoBlock hn B)
        (higham9_11_flattenTwoBlock hn C) i j =
      if i = j then 1 else 0
  rw [higham9_11_flattenTwoBlock_matMul_entry hn B C i j]
  rw [hRight (higham9_11_flatBlockIndex i) (higham9_11_flatBlockIndex j)
    (higham9_11_flatInnerIndex hn i) (higham9_11_flatInnerIndex hn j)]
  by_cases hij : i = j
  · subst j
    simp
  · have hnot :
        ¬ (higham9_11_flatBlockIndex i = higham9_11_flatBlockIndex j ∧
          higham9_11_flatInnerIndex hn i = higham9_11_flatInnerIndex hn j) := by
      intro h
      exact hij ((higham9_11_flatBlockInner_eq_iff hn i j).mp h)
    by_cases hb : higham9_11_flatBlockIndex i = higham9_11_flatBlockIndex j
    · have hi_ne :
          higham9_11_flatInnerIndex hn i ≠ higham9_11_flatInnerIndex hn j := by
        intro hi_eq
        exact hnot ⟨hb, hi_eq⟩
      simp [hij, hb, hi_ne]
    · simp [hij, hb]

/-- **Problem 9.11 support**, a function-shaped right inverse gives a
nonzero determinant for the corresponding Mathlib matrix. -/
theorem higham9_det_ne_zero_of_isRightInverse {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  exact
    Matrix.det_ne_zero_of_right_inverse
      (A := (Matrix.of A : Matrix (Fin n) (Fin n) ℝ))
      (B := (Matrix.of A_inv : Matrix (Fin n) (Fin n) ℝ))
      (by
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        exact hRight i j)

lemma higham9_11_blockMatrix_block_max_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (bi bj : Fin 2) :
    maxEntryNorm hn (higham9_11_blockMatrix A bi bj) = maxEntryNorm hn A := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    rw [higham9_11_blockMatrix_abs]
    exact entry_le_maxEntryNorm hn A i j
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    have h := entry_le_maxEntryNorm hn (higham9_11_blockMatrix A bi bj) i j
    rwa [higham9_11_blockMatrix_abs] at h

/-- **Problem 9.11**, `alpha(B) = alpha(A)` for
`B = [[A,A],[A,-A]]`, using the repository entrywise block max norm. -/
theorem higham9_11_alpha_block_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    blockMaxNorm (by norm_num : 0 < 2) hn (higham9_11_blockMatrix A) =
      maxEntryNorm hn A := by
  apply le_antisymm
  · unfold blockMaxNorm
    apply Finset.sup'_le
    intro bi _
    apply Finset.sup'_le
    intro bj _
    rw [higham9_11_blockMatrix_block_max_eq hn A bi bj]
  · have h :=
      block_le_blockMaxNorm (by norm_num : 0 < 2) hn
        (higham9_11_blockMatrix A) (0 : Fin 2) (0 : Fin 2)
    simpa [higham9_11_blockMatrix_block_max_eq hn A (0 : Fin 2) (0 : Fin 2)] using h

/-- **Problem 9.11**, flattened source-surface form of `alpha(B)=alpha(A)`. -/
theorem higham9_11_flatten_blockMatrix_maxEntryNorm_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm (by omega : 0 < 2 * n)
        (higham9_11_flattenTwoBlock hn (higham9_11_blockMatrix A)) =
      maxEntryNorm hn A := by
  rw [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm hn
    (higham9_11_blockMatrix A), higham9_11_alpha_block_eq hn A]

lemma higham9_11_blockInverseCandidate_block_max_eq {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (bi bj : Fin 2) :
    maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) =
      (1 / 2 : ℝ) * maxEntryNorm hn A_inv := by
  apply le_antisymm
  · unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    rw [higham9_11_blockInverseCandidate_abs]
    exact mul_le_mul_of_nonneg_left
      (entry_le_maxEntryNorm hn A_inv i j) (by norm_num)
  · have hentry :
        ∀ i j : Fin n,
          (1 / 2 : ℝ) * |A_inv i j| ≤
            maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) := by
      intro i j
      have h :=
        entry_le_maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) i j
      simpa [higham9_11_blockInverseCandidate_abs] using h
    have hmax_le :
        maxEntryNorm hn A_inv ≤
          2 * maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) := by
      conv_lhs => unfold maxEntryNorm
      apply Finset.sup'_le
      intro i _
      apply Finset.sup'_le
      intro j _
      have hij := hentry i j
      have hmul :=
        mul_le_mul_of_nonneg_left hij (by norm_num : (0 : ℝ) ≤ 2)
      calc
        |A_inv i j| = 2 * ((1 / 2 : ℝ) * |A_inv i j|) := by ring
        _ ≤ 2 * maxEntryNorm hn (higham9_11_blockInverseCandidate A_inv bi bj) := hmul
    linarith

/-- **Problem 9.11**, `beta(B) = beta(A)/2` for the displayed inverse
candidate of `B = [[A,A],[A,-A]]`. -/
theorem higham9_11_beta_blockInv_eq {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) :
    blockMaxNorm (by norm_num : 0 < 2) hn (higham9_11_blockInverseCandidate A_inv) =
      (1 / 2 : ℝ) * maxEntryNorm hn A_inv := by
  apply le_antisymm
  · unfold blockMaxNorm
    apply Finset.sup'_le
    intro bi _
    apply Finset.sup'_le
    intro bj _
    rw [higham9_11_blockInverseCandidate_block_max_eq hn A_inv bi bj]
  · have h :=
      block_le_blockMaxNorm (by norm_num : 0 < 2) hn
        (higham9_11_blockInverseCandidate A_inv) (0 : Fin 2) (0 : Fin 2)
    simpa [higham9_11_blockInverseCandidate_block_max_eq hn A_inv
      (0 : Fin 2) (0 : Fin 2)] using h

/-- **Problem 9.11**, flattened source-surface form of `beta(B)=beta(A)/2`
for the displayed inverse candidate. -/
theorem higham9_11_flatten_blockInverseCandidate_maxEntryNorm_eq {n : ℕ}
    (hn : 0 < n) (A_inv : Fin n → Fin n → ℝ) :
    maxEntryNorm (by omega : 0 < 2 * n)
        (higham9_11_flattenTwoBlock hn (higham9_11_blockInverseCandidate A_inv)) =
      (1 / 2 : ℝ) * maxEntryNorm hn A_inv := by
  rw [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm hn
    (higham9_11_blockInverseCandidate A_inv), higham9_11_beta_blockInv_eq hn A_inv]

/-- **Problem 9.11**, the source identity
`theta(B) = 2 * theta(A)` for `theta(A) = 1/(alpha(A) * beta(A))`.

This is the local block-matrix algebra used by the appendix solution; it does
not assert the later `g(2n)` lower-bound specialization for the sine matrix. -/
theorem higham9_11_theta_block_eq_two_theta {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hAinv : 0 < maxEntryNorm hn A_inv) :
    1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn (higham9_11_blockMatrix A) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate A_inv)) =
      2 * (1 / (maxEntryNorm hn A * maxEntryNorm hn A_inv)) := by
  rw [higham9_11_alpha_block_eq hn A, higham9_11_beta_blockInv_eq hn A_inv]
  field_simp [ne_of_gt hA, ne_of_gt hAinv]

/-- **Problem 9.11 / equation (9.12)**, the block-doubled theta lower-bound
arithmetic for the sine witness used as both the matrix and inverse candidate.

This combines the already proved block identity `theta(B) = 2 * theta(A)` with
the sine-matrix theta bound.  It does not construct the complete-pivoting
growth trace. -/
theorem higham9_11_sine_block_theta_candidate_ge_succ {n : ℕ}
    (hn : 0 < n) :
    (n : ℝ) + 1 ≤
      1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))) := by
  rw [higham9_11_theta_block_eq_two_theta hn
    (higham9_12_sineMatrix n) (higham9_12_sineMatrix n)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)
    (higham9_12_sineMatrix_maxEntryNorm_pos hn)]
  exact higham9_12_sineMatrix_two_theta_candidate_ge_succ hn

/-- **Problem 9.11**, final lower-bound bridge from the sine block matrix to a
visible growth witness.

The theorem uses the closed sine-block theta estimate and explicit hypotheses
`theta(B) <= rhoB <= g(2n)`.  It does not construct the complete-pivoting
growth trace or hide the source witness as an assumption. -/
theorem higham9_11_complete_pivoting_lower_bound_from_sine_block_theta {n : ℕ}
    (hn : 0 < n)
    (g2n rhoB : ℝ)
    (hg : rhoB ≤ g2n)
    (hrho :
      1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))) ≤ rhoB) :
    (n : ℝ) + 1 ≤ g2n :=
  le_trans (higham9_11_sine_block_theta_candidate_ge_succ hn) (le_trans hrho hg)

/-- Problem 9.11's final lower-bound arithmetic: once the complete-pivoting
growth function and sine-matrix specialization supply
`g(2n) ≥ rho(B) ≥ 2 theta(S_n) = n + 1`, the advertised bound follows. -/
theorem higham9_11_complete_pivoting_lower_bound_consequence (n : ℕ)
    (g2n rhoB thetaSn : ℝ)
    (hg : rhoB ≤ g2n)
    (hrho : 2 * thetaSn ≤ rhoB)
    (hSn : 2 * thetaSn = (n : ℝ) + 1) :
    (n : ℝ) + 1 ≤ g2n := by
  linarith

/-- Problem 9.11's lower-bound arithmetic in inequality form.  This is the
form supplied by the conditional max-entry sine witness
`higham9_12_two_theta_ge_succ_of_maxEntryNorm_le_scale`. -/
theorem higham9_11_complete_pivoting_lower_bound_consequence_le (n : ℕ)
    (g2n rhoB thetaSn : ℝ)
    (hg : rhoB ≤ g2n)
    (hrho : 2 * thetaSn ≤ rhoB)
    (hSn : (n : ℝ) + 1 ≤ 2 * thetaSn) :
    (n : ℝ) + 1 ≤ g2n := by
  linarith

/-- **Foundation for equation (9.14): leading principal minor = product of the
first `k` pivots.**  For an exact LU certificate `A = L U` with `L` unit lower
triangular and `U` upper triangular, the determinant of the `k × k` leading
principal submatrix of `A` equals the product of the first `k` diagonal entries
of `U` (the first `k` pivots).

This is the "pivot-to-leading-minor" relation named in the Chapter 9 report as
the next step of the Wilkinson complete-pivoting upper bound (9.14): combined
with the Hadamard determinant inequality `higham9_hadamard_det_sq_le_prod_row_sq`
(applied to each completely-pivoted leading submatrix) it converts pivot
magnitudes into the `2·3^{1/2}⋯` product.  The proof uses that the leading `k × k`
block of `L·U` is the product of the leading `k × k` blocks of `L` and `U` — the
tail terms (index `≥ k`) vanish because `L` is lower triangular — so the block
determinant factors as `(∏ pivots of L_k)·(∏ pivots of U_k) = ∏ U_ii`. -/
theorem higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    {k : ℕ} (hk : k ≤ n) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
          (Fin.castLE hk) (Fin.castLE hk)) =
      ∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) := by
  classical
  set e : Fin k → Fin n := Fin.castLE hk with he
  have hinj : Function.Injective e := Fin.castLE_injective hk
  set Lk : Matrix (Fin k) (Fin k) ℝ :=
    (Matrix.of L : Matrix (Fin n) (Fin n) ℝ).submatrix e e with hLk
  set Uk : Matrix (Fin k) (Fin k) ℝ :=
    (Matrix.of U : Matrix (Fin n) (Fin n) ℝ).submatrix e e with hUk
  set Ak : Matrix (Fin k) (Fin k) ℝ :=
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix e e with hAk
  -- The leading `k × k` block of `A = L U` is the product of the leading blocks.
  have hprod : Ak = Lk * Uk := by
    ext i j
    have hAij : Ak i j = ∑ p : Fin n, L (e i) p * U p (e j) := by
      simp only [hAk, Matrix.submatrix_apply, Matrix.of_apply]
      rw [← hLU.product_eq (e i) (e j)]
    have hLUij : (Lk * Uk) i j = ∑ m : Fin k, L (e i) (e m) * U (e m) (e j) := by
      simp only [hLk, hUk, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.of_apply]
    rw [hAij, hLUij]
    -- Reindex the `Fin k` sum as a sum over the image of `e`, then extend to
    -- `Fin n`; the extra terms vanish since `L` is lower triangular.
    rw [show (∑ m : Fin k, L (e i) (e m) * U (e m) (e j))
          = ∑ p ∈ Finset.univ.map ⟨e, hinj⟩, L (e i) p * U p (e j) from
        (Finset.sum_map Finset.univ ⟨e, hinj⟩
          (fun p => L (e i) p * U p (e j))).symm]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro p _ hp
    have hpk : k ≤ p.val := by
      by_contra hlt
      push_neg at hlt
      exact hp (Finset.mem_map.mpr
        ⟨⟨p.val, hlt⟩, Finset.mem_univ _, by
          apply Fin.ext; simp [he, Fin.coe_castLE]⟩)
    have hlt : (e i).val < p.val := by
      have h1 : (e i).val = i.val := by simp [he, Fin.coe_castLE]
      have h2 : i.val < k := i.isLt
      omega
    rw [hLU.L_upper_zero (e i) p hlt, zero_mul]
  -- `L_k` is unit lower triangular, `U_k` upper triangular.
  have hLtri : Matrix.BlockTriangular Lk OrderDual.toDual := by
    intro a b hab
    have hab' : a.val < b.val := by simpa using hab
    have : (e a).val < (e b).val := by simp [he, Fin.coe_castLE]; exact hab'
    simp only [hLk, Matrix.submatrix_apply, Matrix.of_apply]
    exact hLU.L_upper_zero (e a) (e b) this
  have hUtri : Matrix.BlockTriangular Uk id := by
    intro a b hab
    have hab' : b.val < a.val := by simpa using hab
    have : (e b).val < (e a).val := by simp [he, Fin.coe_castLE]; exact hab'
    simp only [hUk, Matrix.submatrix_apply, Matrix.of_apply]
    exact hLU.U_lower_zero (e a) (e b) this
  have hLdet : Lk.det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ hLtri]
    refine Finset.prod_eq_one ?_
    intro i _
    simp only [hLk, Matrix.submatrix_apply, Matrix.of_apply]
    exact hLU.L_diag (e i)
  calc
    Ak.det = (Lk * Uk).det := by rw [hprod]
    _ = Lk.det * Uk.det := Matrix.det_mul _ _
    _ = Uk.det := by rw [hLdet, one_mul]
    _ = ∏ i : Fin k, Uk i i := Matrix.det_of_upperTriangular hUtri
    _ = ∏ i : Fin k, U (e i) (e i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [hUk, Matrix.submatrix_apply, Matrix.of_apply]

/-- **Foundation for equation (9.14): Hadamard pivot-product bound.**  If every
entry of the `k × k` leading principal submatrix of `A` is bounded in magnitude
by `M`, then the magnitude of the product of the first `k` pivots is bounded by
`sqrt(k^k) · M^k`.

This is the Hadamard step of Wilkinson's complete-pivoting analysis (9.14): the
leading-minor identity `higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag`
turns the pivot product into the determinant of the leading submatrix, and
`higham9_hadamard_det_sq_le_pow_maxEntryNorm` bounds that squared determinant by
`k^k · M^{2k}`.  The entry bound `M` is left as an explicit hypothesis: it is
supplied, under complete pivoting, by the (still open, research-grade) per-stage
invariant that every active-submatrix entry stays below the current pivot.  This
lemma is therefore an honest reduction of the (9.14) upper bound to that entry
invariant, not a proof of the full bound. -/
theorem higham9_14_abs_prod_leadingPivots_le_of_entries_le {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    {k : ℕ} (hk : k ≤ n) (hkpos : 0 < k) {M : ℝ}
    (hM : ∀ i j : Fin k,
      |A (Fin.castLE hk i) (Fin.castLE hk j)| ≤ M) :
    |∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i)|
      ≤ Real.sqrt ((k : ℝ) ^ k) * M ^ k := by
  classical
  set B : Matrix (Fin k) (Fin k) ℝ :=
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
      (Fin.castLE hk) (Fin.castLE hk) with hB
  have hdet : B.det = ∏ i : Fin k, U (Fin.castLE hk i) (Fin.castLE hk i) :=
    higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag hLU hk
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM ⟨0, hkpos⟩ ⟨0, hkpos⟩)
  have hmax : maxEntryNorm hkpos B ≤ M := by
    refine maxEntryNorm_le_of_entry_le_bound hkpos B M ?_
    intro i j
    simpa [hB, Matrix.submatrix_apply, Matrix.of_apply] using hM i j
  have hhad := higham9_hadamard_det_sq_le_pow_maxEntryNorm hkpos B
  have hpow : (maxEntryNorm hkpos B) ^ (2 * k) ≤ M ^ (2 * k) :=
    pow_le_pow_left₀ (maxEntryNorm_nonneg hkpos B) hmax (2 * k)
  have hstep : (B.det) ^ 2 ≤ (k : ℝ) ^ k * M ^ (2 * k) :=
    hhad.trans (by
      exact mul_le_mul_of_nonneg_left hpow (by positivity))
  have habs : |B.det| ≤ Real.sqrt ((k : ℝ) ^ k * M ^ (2 * k)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hstep
  have hrhs : Real.sqrt ((k : ℝ) ^ k * M ^ (2 * k))
      = Real.sqrt ((k : ℝ) ^ k) * M ^ k := by
    rw [Real.sqrt_mul (by positivity), show 2 * k = k * 2 from by ring, pow_mul,
      Real.sqrt_sq (pow_nonneg hMnn k)]
  rw [hdet, hrhs] at habs
  exact habs

/-- **Foundation for equation (9.14): consecutive leading-minor / pivot
relation.**  The determinant of the `(k+1) × (k+1)` leading principal submatrix
equals the `(k+1)`-th pivot times the determinant of the `k × k` leading
principal submatrix.

This is the classical "the `k`-th pivot is the ratio of consecutive leading
principal minors" step of Wilkinson's complete-pivoting analysis, stated as a
division-free product identity (so no nonsingularity hypothesis is needed).  It
is the recursion that turns the leading-minor bound
`higham9_14_abs_prod_leadingPivots_le_of_entries_le` into a per-pivot bound and
ultimately the Wilkinson product. -/
theorem higham9_14_leadingSubmatrix_det_succ {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    {k : ℕ} (hk1 : k + 1 ≤ n) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
          (Fin.castLE hk1) (Fin.castLE hk1)) =
      U (Fin.castLE hk1 (Fin.last k)) (Fin.castLE hk1 (Fin.last k)) *
        Matrix.det
          ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix
            (Fin.castLE (Nat.le_of_succ_le hk1))
            (Fin.castLE (Nat.le_of_succ_le hk1))) := by
  rw [higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag hLU hk1,
    higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag hLU
      (Nat.le_of_succ_le hk1),
    Fin.prod_univ_castSucc
      (f := fun i : Fin (k + 1) => U (Fin.castLE hk1 i) (Fin.castLE hk1 i))]
  have hprodeq :
      (∏ i : Fin k,
          U (Fin.castLE hk1 i.castSucc) (Fin.castLE hk1 i.castSucc))
        = ∏ i : Fin k,
            U (Fin.castLE (Nat.le_of_succ_le hk1) i)
              (Fin.castLE (Nat.le_of_succ_le hk1) i) :=
    Finset.prod_congr rfl (fun i _ => by rw [Fin.castLE_castSucc])
  rw [hprodeq, mul_comm]

/-- **Foundation for equation (9.14): full-matrix Hadamard pivot-product bound.**
The magnitude of the product of all pivots (equivalently `|det A|`) is bounded
by `sqrt(n^n) · (maxEntryNorm A)^n`.  This is the `k = n` specialization of the
Hadamard growth bound, stated directly via the full-determinant identity
`LUFactSpec.det_eq_prod_U_diag`, giving a clean growth-factor-facing surface
(the entry bound is the concrete `maxEntryNorm A`, so no extra hypothesis is
needed). -/
theorem higham9_14_abs_prod_pivots_le_maxEntryNorm {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U) :
    |∏ i : Fin n, U i i| ≤ Real.sqrt ((n : ℝ) ^ n) * (maxEntryNorm hn A) ^ n := by
  have hdet : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).det = ∏ i, U i i :=
    hLU.det_eq_prod_U_diag
  have hMnn : 0 ≤ maxEntryNorm hn A := maxEntryNorm_nonneg hn A
  have hhad := higham9_hadamard_det_sq_le_pow_maxEntryNorm hn
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
  have habs : |(Matrix.of A : Matrix (Fin n) (Fin n) ℝ).det|
      ≤ Real.sqrt ((n : ℝ) ^ n * (maxEntryNorm hn A) ^ (2 * n)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hhad
  have hrhs : Real.sqrt ((n : ℝ) ^ n * (maxEntryNorm hn A) ^ (2 * n))
      = Real.sqrt ((n : ℝ) ^ n) * (maxEntryNorm hn A) ^ n := by
    rw [Real.sqrt_mul (by positivity), show 2 * n = n * 2 from by ring, pow_mul,
      Real.sqrt_sq (pow_nonneg hMnn n)]
  rw [hdet, hrhs] at habs
  exact habs

/-- **Equation (9.14)**, Wilkinson's scalar product inside the complete-pivoting
growth upper bound:
`2 * 3^(1/2) * ... * n^(1/(n-1))`.

This records the scalar surface only; the source growth theorem
`rho_n^c <= sqrt n * sqrt(product)` still requires the complete-pivoting trace
and Wilkinson growth proof recorded as open in the Chapter 9 report. -/
noncomputable def higham9_14_completePivotWilkinsonProduct (n : ℕ) : ℝ :=
  (Finset.Icc 2 n).prod fun k => (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1))

/-- **Equation (9.14)**, Wilkinson's displayed complete-pivoting upper-bound
RHS `sqrt n * sqrt(2 * 3^(1/2) * ... * n^(1/(n-1)))`. -/
noncomputable def higham9_14_completePivotWilkinsonBound (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.sqrt (higham9_14_completePivotWilkinsonProduct n)

lemma higham9_14_completePivotWilkinsonProduct_nonneg (n : ℕ) :
    0 ≤ higham9_14_completePivotWilkinsonProduct n := by
  unfold higham9_14_completePivotWilkinsonProduct
  exact Finset.prod_nonneg fun k _ =>
    Real.rpow_nonneg (Nat.cast_nonneg k) ((1 : ℝ) / ((k : ℝ) - 1))

lemma higham9_14_completePivotWilkinsonProduct_pos (n : ℕ) :
    0 < higham9_14_completePivotWilkinsonProduct n := by
  unfold higham9_14_completePivotWilkinsonProduct
  exact Finset.prod_pos fun k hk => by
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkposNat : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk2
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkposNat
    exact Real.rpow_pos_of_pos hkpos _

lemma higham9_14_completePivotWilkinsonBound_nonneg (n : ℕ) :
    0 ≤ higham9_14_completePivotWilkinsonBound n := by
  unfold higham9_14_completePivotWilkinsonBound
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma higham9_14_completePivotWilkinsonBound_pos {n : ℕ} (hn : 0 < n) :
    0 < higham9_14_completePivotWilkinsonBound n := by
  unfold higham9_14_completePivotWilkinsonBound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos (Real.sqrt_pos_of_pos hnR)
    (Real.sqrt_pos_of_pos (higham9_14_completePivotWilkinsonProduct_pos n))

/-- **Theorem 9.15 / Equation (9.14)**, Wilkinson's complete-pivoting growth-factor
upper bound — analytic core (Wilkinson [1229, 1961]; the book gives only a
citation).  Given positive "pivots" `p 1, …, p n` satisfying the Hadamard
determinant constraint `∏_{i=1}^k p i ≤ √(k^k) · (p k)^k` for every `k`
(exactly `higham9_14_abs_prod_leadingPivots_le_of_entries_le` combined with the
complete-pivoting fact that the `k`-th iterate's max entry is `p k`), the ratio
`p 1 / p n` is bounded by Wilkinson's product
`√n · (2·3^{1/2}⋯n^{1/(n-1)})^{1/2}` (`higham9_14_completePivotWilkinsonBound n`).

This is Wilkinson's actual one-page proof: writing `q k = log (p k)` and
`T k = (∑_{i≤k} q i)/k`, the constraint gives `T m - T (m+1) ≤ log(m+1)/(2m)`,
which telescopes to `q 1 - q n ≤ (1/2)(log n + ∑_{k=2}^n log k/(k-1)) =
log(bound)`.  The pivot constraint is an explicit hypothesis: under complete
pivoting it is discharged by the Hadamard bound above together with the
identification of the growth factor as `max_k p k / p n`; the remaining
Gaussian-elimination iterate model (the completely-pivoted Schur-complement
chain) is the only piece of the source row (9.14) not yet formalized. -/
theorem higham9_14_wilkinson_ratio_bound {n : ℕ} (hn : 1 ≤ n)
    (p : ℕ → ℝ) (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < p k)
    (hpiv : ∀ k, 1 ≤ k → k ≤ n →
      ∏ i ∈ Finset.Icc 1 k, p i ≤ Real.sqrt ((k : ℝ) ^ k) * (p k) ^ k) :
    p 1 / p n ≤ higham9_14_completePivotWilkinsonBound n := by
  classical
  set q : ℕ → ℝ := fun k => Real.log (p k) with hq
  set Ssum : ℕ → ℝ := fun k => ∑ i ∈ Finset.Icc 1 k, q i with hSsum
  set T : ℕ → ℝ := fun k => Ssum k / (k : ℝ) with hT
  have hSsucc : ∀ m : ℕ, Ssum (m + 1) = Ssum m + q (m + 1) := by
    intro m
    simp only [hSsum]
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1)]
  have hlog : ∀ k, 1 ≤ k → k ≤ n → Ssum k ≤ (k : ℝ) / 2 * Real.log k + k * q k := by
    intro k hk1 hkn
    have hmem : ∀ i ∈ Finset.Icc 1 k, 0 < p i := by
      intro i hi
      exact hpos i (Finset.mem_Icc.mp hi).1 (le_trans (Finset.mem_Icc.mp hi).2 hkn)
    have hprodpos : 0 < ∏ i ∈ Finset.Icc 1 k, p i := Finset.prod_pos hmem
    have hkpos : (0 : ℝ) < (k : ℝ) ^ k := by positivity
    have hsqrtpos : 0 < Real.sqrt ((k : ℝ) ^ k) := Real.sqrt_pos.mpr hkpos
    have hpkpos : 0 < (p k) ^ k := pow_pos (hpos k hk1 hkn) k
    have hlogle : Real.log (∏ i ∈ Finset.Icc 1 k, p i)
        ≤ Real.log (Real.sqrt ((k : ℝ) ^ k) * (p k) ^ k) :=
      Real.log_le_log hprodpos (hpiv k hk1 hkn)
    have hLHS : Real.log (∏ i ∈ Finset.Icc 1 k, p i) = Ssum k := by
      rw [Real.log_prod (fun i hi => ne_of_gt (hmem i hi)), hSsum]
    have hRHS : Real.log (Real.sqrt ((k : ℝ) ^ k) * (p k) ^ k)
        = (k : ℝ) / 2 * Real.log k + k * q k := by
      rw [Real.log_mul (ne_of_gt hsqrtpos) (ne_of_gt hpkpos),
        Real.log_sqrt (le_of_lt hkpos), Real.log_pow, Real.log_pow, hq]
      push_cast
      ring
    rw [hLHS, hRHS] at hlogle
    exact hlogle
  have hstep : ∀ m : ℕ, 1 ≤ m → m + 1 ≤ n →
      T m - T (m + 1) ≤ Real.log ((m : ℝ) + 1) / (2 * (m : ℝ)) := by
    intro m hm1 hmn
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hc := hlog (m + 1) (by omega) hmn
    rw [hSsucc m] at hc
    push_cast at hc
    have hTm : T m * (m : ℝ) = Ssum m := by
      simp only [hT]; field_simp
    have hTm1 : T (m + 1) * ((m : ℝ) + 1) = Ssum (m + 1) := by
      simp only [hT]; push_cast; field_simp
    rw [hSsucc m] at hTm1
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))]
    nlinarith [hc, hTm, hTm1, hmR, hm1R, mul_pos hmR hm1R]
  have hlast : T n - q n ≤ Real.log n / 2 := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hc := hlog n hn (le_refl n)
    have hTn : T n * (n : ℝ) = Ssum n := by simp only [hT]; field_simp
    nlinarith [hc, hTn, hnR]
  set F : ℕ → ℝ := fun j => T (j + 1) with hF
  have htele : F 0 - F (n - 1) = ∑ j ∈ Finset.range (n - 1), (F j - F (j + 1)) :=
    (Finset.sum_range_sub' F (n - 1)).symm
  have hsum_le : ∑ j ∈ Finset.range (n - 1), (F j - F (j + 1))
      ≤ ∑ j ∈ Finset.range (n - 1), Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjlt : j < n - 1 := Finset.mem_range.mp hj
    have hstepj := hstep (j + 1) (by omega) (by omega)
    have hcast1 : ((j : ℝ) + 1 + 1) = (j : ℝ) + 2 := by ring
    simp only [hF]
    push_cast at hstepj ⊢
    rw [hcast1] at hstepj
    convert hstepj using 2
  have hF0 : F 0 = q 1 := by
    simp [hF, hT, hSsum]
  have hFn : F (n - 1) = T n := by
    simp only [hF]
    congr 1
    omega
  have hmain : q 1 - q n
      ≤ (∑ j ∈ Finset.range (n - 1), Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1)))
        + Real.log n / 2 := by
    have h1 : q 1 - T n
        ≤ ∑ j ∈ Finset.range (n - 1), Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1)) := by
      rw [← hF0, ← hFn, htele]; exact hsum_le
    linarith [h1, hlast]
  have hbound_pos : 0 < higham9_14_completePivotWilkinsonBound n :=
    higham9_14_completePivotWilkinsonBound_pos hn
  have hprod_pos : 0 < higham9_14_completePivotWilkinsonProduct n :=
    higham9_14_completePivotWilkinsonProduct_pos n
  have hprodlog : Real.log (higham9_14_completePivotWilkinsonProduct n)
      = ∑ j ∈ Finset.range (n - 1), Real.log ((j : ℝ) + 2) / ((j : ℝ) + 1) := by
    rw [higham9_14_completePivotWilkinsonProduct,
      Real.log_prod (fun k hk => by have := (Finset.mem_Icc.mp hk).1; positivity),
      ← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
      Finset.sum_Ico_eq_sum_range, show n + 1 - 2 = n - 1 from by omega]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.log_rpow (by positivity)]
    push_cast
    rw [show (2 : ℝ) + (j : ℝ) - 1 = (j : ℝ) + 1 from by ring]
    ring
  have hlogbound : Real.log (higham9_14_completePivotWilkinsonBound n)
      = Real.log n / 2
        + (∑ j ∈ Finset.range (n - 1), Real.log ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1))) := by
    rw [higham9_14_completePivotWilkinsonBound,
      Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn)))
        (ne_of_gt (Real.sqrt_pos.mpr hprod_pos)),
      Real.log_sqrt (by positivity), Real.log_sqrt (le_of_lt hprod_pos),
      hprodlog, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [div_div, mul_comm ((j : ℝ) + 1) 2]
  have hp1 : 0 < p 1 := hpos 1 (le_refl 1) hn
  have hpn : 0 < p n := hpos n hn (le_refl n)
  have hlogratio : Real.log (p 1 / p n)
      ≤ Real.log (higham9_14_completePivotWilkinsonBound n) := by
    rw [Real.log_div (ne_of_gt hp1) (ne_of_gt hpn), hlogbound]
    have hqq : q 1 - q n = Real.log (p 1) - Real.log (p n) := by simp [hq]
    rw [← hqq]
    linarith [hmain]
  have hfin := Real.exp_le_exp.mpr hlogratio
  rwa [Real.exp_log (by positivity), Real.exp_log hbound_pos] at hfin

/-- **Equation (9.14)**, scalar product lower bound.

Every factor in Wilkinson's displayed complete-pivoting product is at least
one, so the whole scalar product is at least one. -/
lemma higham9_14_completePivotWilkinsonProduct_ge_one (n : ℕ) :
    1 ≤ higham9_14_completePivotWilkinsonProduct n := by
  unfold higham9_14_completePivotWilkinsonProduct
  have hprod :
      (Finset.Icc 2 n).prod (fun _ : ℕ => (1 : ℝ)) ≤
        (Finset.Icc 2 n).prod
          (fun k => (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1))) := by
    apply Finset.prod_le_prod
    · intro k hk
      norm_num
    · intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_ge_one_nat : 1 ≤ k := le_trans (by decide : 1 ≤ 2) hk2
      have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_one_nat
      have hk_gt_one_nat : 1 < k :=
        Nat.lt_of_lt_of_le (by decide : 1 < 2) hk2
      have hden_pos : 0 < (k : ℝ) - 1 := by
        have hk_gt_one : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk_gt_one_nat
        linarith
      have hexp_nonneg : 0 ≤ (1 : ℝ) / ((k : ℝ) - 1) :=
        div_nonneg zero_le_one (le_of_lt hden_pos)
      exact Real.one_le_rpow hk_ge_one hexp_nonneg
  simpa using hprod

/-- **Equation (9.14)**, base value of Wilkinson's scalar product. -/
lemma higham9_14_completePivotWilkinsonProduct_two :
    higham9_14_completePivotWilkinsonProduct 2 = 2 := by
  norm_num [higham9_14_completePivotWilkinsonProduct]

/-- **Equation (9.14)**, one-step recurrence for Wilkinson's scalar product.

This exposes the factor appended when the product endpoint is increased from
`n` to `n + 1`, which is the form needed by inductive scalar-product
arguments. -/
lemma higham9_14_completePivotWilkinsonProduct_succ {n : ℕ} (hn : 1 ≤ n) :
    higham9_14_completePivotWilkinsonProduct (n + 1) =
      higham9_14_completePivotWilkinsonProduct n *
        ((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)) := by
  unfold higham9_14_completePivotWilkinsonProduct
  have hab : 2 ≤ n + 1 := by omega
  have hprod :=
    Finset.prod_Icc_succ_top (a := 2) (b := n)
      (f := fun k : ℕ => (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1))) hab
  have hden : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by norm_num
  simpa [hden] using hprod

/-- **Equation (9.14)**, the factor appended in Wilkinson's scalar product is
at least one. -/
lemma higham9_14_completePivotWilkinsonProduct_factor_ge_one {n : ℕ}
    (hn : 1 ≤ n) :
    1 ≤ ((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)) := by
  have hbaseNat : 1 ≤ n + 1 := by omega
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hbaseNat
  have hnposNat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hexp_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) :=
    div_nonneg zero_le_one (le_of_lt hnpos)
  exact Real.one_le_rpow hbase hexp_nonneg

/-- **Equation (9.14)**, one-step monotonicity of Wilkinson's scalar product.

This is scalar support for comparing nested complete-pivoting product bounds;
the trace-level complete-pivoting growth proof remains separate. -/
lemma higham9_14_completePivotWilkinsonProduct_le_succ (n : ℕ) :
    higham9_14_completePivotWilkinsonProduct n ≤
      higham9_14_completePivotWilkinsonProduct (n + 1) := by
  cases n with
  | zero =>
      norm_num [higham9_14_completePivotWilkinsonProduct]
  | succ k =>
      have hn : 1 ≤ k + 1 := by omega
      rw [higham9_14_completePivotWilkinsonProduct_succ hn]
      have hprod_nonneg :
          0 ≤ higham9_14_completePivotWilkinsonProduct (k + 1) :=
        higham9_14_completePivotWilkinsonProduct_nonneg (k + 1)
      have hfactor :
          1 ≤ ((k + 1 + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) :=
        higham9_14_completePivotWilkinsonProduct_factor_ge_one hn
      calc
        higham9_14_completePivotWilkinsonProduct (k + 1) =
            higham9_14_completePivotWilkinsonProduct (k + 1) * 1 := by
          rw [mul_one]
        _ ≤ higham9_14_completePivotWilkinsonProduct (k + 1) *
              ((k + 1 + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hfactor hprod_nonneg

/-- **Equation (9.14)**, successor-ratio form of Wilkinson scalar-product
monotonicity. -/
lemma higham9_14_completePivotWilkinsonProduct_succ_div_ge_one (n : ℕ) :
    (1 : ℝ) ≤
      higham9_14_completePivotWilkinsonProduct (n + 1) /
        higham9_14_completePivotWilkinsonProduct n := by
  have hpos := higham9_14_completePivotWilkinsonProduct_pos n
  rw [le_div_iff₀ hpos]
  simpa [one_mul] using higham9_14_completePivotWilkinsonProduct_le_succ n

/-- **Equation (9.14)**, Wilkinson's scalar product is monotone in the matrix
order parameter. -/
theorem higham9_14_completePivotWilkinsonProduct_monotone :
    Monotone higham9_14_completePivotWilkinsonProduct :=
  monotone_nat_of_le_succ higham9_14_completePivotWilkinsonProduct_le_succ

/-- **Equation (9.14)**, order form of Wilkinson scalar-product
monotonicity. -/
theorem higham9_14_completePivotWilkinsonProduct_le_of_le {n m : ℕ}
    (hnm : n ≤ m) :
    higham9_14_completePivotWilkinsonProduct n ≤
      higham9_14_completePivotWilkinsonProduct m :=
  higham9_14_completePivotWilkinsonProduct_monotone hnm

/-- **Equation (9.14)**, Wilkinson RHS dominates its leading `sqrt n` factor.

This is only scalar support for the displayed RHS; it does not prove the
complete-pivoting trace growth theorem. -/
lemma higham9_14_completePivotWilkinsonBound_ge_sqrt (n : ℕ) :
    Real.sqrt (n : ℝ) ≤ higham9_14_completePivotWilkinsonBound n := by
  unfold higham9_14_completePivotWilkinsonBound
  have hsqrt_prod :
      1 ≤ Real.sqrt (higham9_14_completePivotWilkinsonProduct n) := by
    simpa using
      (Real.sqrt_le_sqrt
        (higham9_14_completePivotWilkinsonProduct_ge_one n) :
          Real.sqrt (1 : ℝ) ≤
            Real.sqrt (higham9_14_completePivotWilkinsonProduct n))
  calc
    Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) * 1 := by rw [mul_one]
    _ ≤ Real.sqrt (n : ℝ) *
          Real.sqrt (higham9_14_completePivotWilkinsonProduct n) :=
        mul_le_mul_of_nonneg_left hsqrt_prod (Real.sqrt_nonneg _)

/-- **Equation (9.14)**, Wilkinson's displayed complete-pivoting RHS is at
least one in every positive dimension. -/
lemma higham9_14_completePivotWilkinsonBound_ge_one {n : ℕ} (hn : 0 < n) :
    1 ≤ higham9_14_completePivotWilkinsonBound n := by
  have hn_one_nat : 1 ≤ n := Nat.succ_le_of_lt hn
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
  have hsqrt_one :
      (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa using
      (Real.sqrt_le_sqrt hn_one :
        Real.sqrt (1 : ℝ) ≤ Real.sqrt (n : ℝ))
  exact hsqrt_one.trans (higham9_14_completePivotWilkinsonBound_ge_sqrt n)

/-- **Equation (9.14)**, base value of Wilkinson's displayed complete-pivoting
RHS. -/
lemma higham9_14_completePivotWilkinsonBound_two :
    higham9_14_completePivotWilkinsonBound 2 = 2 := by
  unfold higham9_14_completePivotWilkinsonBound
  rw [higham9_14_completePivotWilkinsonProduct_two]
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast]
  rw [← pow_two]
  exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)

/-- **Equation (9.14)**, base value of Wilkinson's displayed complete-pivoting
RHS in dimension one. -/
lemma higham9_14_completePivotWilkinsonBound_one :
    higham9_14_completePivotWilkinsonBound 1 = 1 := by
  norm_num [higham9_14_completePivotWilkinsonBound,
    higham9_14_completePivotWilkinsonProduct]

/-- **Equation (9.14)**, in dimension one Wilkinson's displayed
complete-pivoting RHS dominates the elementary recursive trace bound. -/
lemma higham9_14_pow_two_le_completePivotWilkinsonBound_of_eq_one {n : ℕ}
    (hone : n = 1) :
    (2 : ℝ) ^ (n - 1) ≤ higham9_14_completePivotWilkinsonBound n := by
  subst n
  simp [higham9_14_completePivotWilkinsonBound_one]

/-- **Equation (9.14)**, in dimensions one and two Wilkinson's displayed
complete-pivoting RHS dominates the elementary recursive trace bound
`2^(n-1)`. -/
lemma higham9_14_pow_two_le_completePivotWilkinsonBound_of_le_two {n : ℕ}
    (hn : 0 < n) (hle : n ≤ 2) :
    (2 : ℝ) ^ (n - 1) ≤ higham9_14_completePivotWilkinsonBound n := by
  have hn_cases : n = 1 ∨ n = 2 := by omega
  rcases hn_cases with rfl | rfl
  · simp [higham9_14_completePivotWilkinsonBound_one]
  · simp [higham9_14_completePivotWilkinsonBound_two]

/-- **Equation (9.14)**, order form of monotonicity for Wilkinson's displayed
complete-pivoting RHS. -/
theorem higham9_14_completePivotWilkinsonBound_le_of_le {n m : ℕ}
    (hnm : n ≤ m) :
    higham9_14_completePivotWilkinsonBound n ≤
      higham9_14_completePivotWilkinsonBound m := by
  unfold higham9_14_completePivotWilkinsonBound
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hsqrt_n : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_le_sqrt hnmR
  have hsqrt_prod :
      Real.sqrt (higham9_14_completePivotWilkinsonProduct n) ≤
        Real.sqrt (higham9_14_completePivotWilkinsonProduct m) :=
    Real.sqrt_le_sqrt (higham9_14_completePivotWilkinsonProduct_le_of_le hnm)
  exact mul_le_mul hsqrt_n hsqrt_prod (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **Equation (9.14)**, successor-ratio form of Wilkinson displayed-bound
monotonicity. -/
lemma higham9_14_completePivotWilkinsonBound_succ_div_ge_one {n : ℕ}
    (hn : 0 < n) :
    (1 : ℝ) ≤
      higham9_14_completePivotWilkinsonBound (n + 1) /
        higham9_14_completePivotWilkinsonBound n := by
  have hpos := higham9_14_completePivotWilkinsonBound_pos hn
  rw [le_div_iff₀ hpos]
  simpa [one_mul] using
    higham9_14_completePivotWilkinsonBound_le_of_le (Nat.le_succ n)

/-- **Equation (9.14)**, Wilkinson's displayed complete-pivoting RHS is at
least two in every dimension at least two. -/
lemma higham9_14_completePivotWilkinsonBound_ge_two_of_ge_two {n : ℕ}
    (hn : 2 ≤ n) :
    (2 : ℝ) ≤ higham9_14_completePivotWilkinsonBound n := by
  rw [← higham9_14_completePivotWilkinsonBound_two]
  exact higham9_14_completePivotWilkinsonBound_le_of_le hn

/-- **Equation (9.14)**, Wilkinson's displayed complete-pivoting RHS is
monotone in the matrix order parameter. -/
theorem higham9_14_completePivotWilkinsonBound_monotone :
    Monotone higham9_14_completePivotWilkinsonBound := by
  intro n m hnm
  exact higham9_14_completePivotWilkinsonBound_le_of_le hnm

/-- **Equation (9.14)**, Wilkinson's complete-pivoting max-pivot bound —
sequence level.  If positive "pivots" `p 1, …, p n` satisfy the segment
Hadamard constraint `∏_{i=m}^{k} p i ≤ √(j^j) · (p m)^j` with `j = k - m + 1`
for every `1 ≤ m ≤ k ≤ n` (under complete pivoting this is the Hadamard
determinant bound applied to the leading `j × j` block of the stage-`m`
reduced matrix, whose largest-magnitude entry is the pivot `p m`), then EVERY
pivot — not only the last — satisfies
`p k / p 1 ≤ higham9_14_completePivotWilkinsonBound n`.

The proof applies the analytic core `higham9_14_wilkinson_ratio_bound` to the
reversed truncated sequence `t ↦ p (k + 1 - t)` of length `k`, whose length-`j`
prefix constraints are exactly the `[k+1-j, k]` segment instances of `hpiv`,
and then enlarges the resulting `WilkinsonBound k` to `WilkinsonBound n` by
`higham9_14_completePivotWilkinsonBound_le_of_le`.  Together with the
growth-factor identification `rho_n^c = max_k p k / p 1`, this is the full
sequence-level content of the (9.14) upper bound; only the
Gaussian-elimination iterate model discharging `hpiv` remains matrix-level. -/
theorem higham9_14_wilkinson_max_pivot_bound {n : ℕ}
    (p : ℕ → ℝ) (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < p k)
    (hpiv : ∀ m k, 1 ≤ m → m ≤ k → k ≤ n →
      ∏ i ∈ Finset.Icc m k, p i
        ≤ Real.sqrt (((k - m + 1 : ℕ) : ℝ) ^ (k - m + 1)) * p m ^ (k - m + 1))
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    p k / p 1 ≤ higham9_14_completePivotWilkinsonBound n := by
  classical
  set r : ℕ → ℝ := fun t => p (k + 1 - t) with hr
  have hrpos : ∀ t, 1 ≤ t → t ≤ k → 0 < r t := by
    intro t ht1 htk
    exact hpos (k + 1 - t) (by omega) (by omega)
  have hrpiv : ∀ j, 1 ≤ j → j ≤ k →
      ∏ t ∈ Finset.Icc 1 j, r t
        ≤ Real.sqrt ((j : ℝ) ^ j) * r j ^ j := by
    intro j hj1 hjk
    have hm1 : 1 ≤ k + 1 - j := by omega
    have hmk : k + 1 - j ≤ k := by omega
    have hj_eq : k - (k + 1 - j) + 1 = j := by omega
    have hseg := hpiv (k + 1 - j) k hm1 hmk hkn
    rw [hj_eq] at hseg
    have hprod_eq : ∏ t ∈ Finset.Icc 1 j, r t
        = ∏ i ∈ Finset.Icc (k + 1 - j) k, p i := by
      refine Finset.prod_nbij' (fun t => k + 1 - t) (fun i => k + 1 - i)
        ?_ ?_ ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_Icc] at ht ⊢
        omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi ⊢
        omega
      · intro t ht
        simp only [Finset.mem_Icc] at ht
        show k + 1 - (k + 1 - t) = t
        omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        show k + 1 - (k + 1 - i) = i
        omega
      · intro t ht
        rfl
    rw [hprod_eq]
    simpa [hr] using hseg
  have hcore := higham9_14_wilkinson_ratio_bound (n := k) hk1 r hrpos hrpiv
  have hr1 : r 1 = p k := by simp [hr]
  have hrk : r k = p 1 := by
    have hkk : k + 1 - k = 1 := by omega
    simp [hr, hkk]
  rw [hr1, hrk] at hcore
  exact hcore.trans (higham9_14_completePivotWilkinsonBound_le_of_le hkn)

/-- **Equation (9.14)**, product form of the sequence-level max-pivot bound:
every pivot is bounded by Wilkinson's displayed complete-pivoting RHS times
the first pivot.  This is the shape consumed by max-entry growth-factor
adapters (`p 1` is the max entry of the original matrix under complete
pivoting, `p k` the max entry of the stage-`k` reduced matrix). -/
theorem higham9_14_wilkinson_pivot_le_bound_mul {n : ℕ} (hn : 1 ≤ n)
    (p : ℕ → ℝ) (hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < p k)
    (hpiv : ∀ m k, 1 ≤ m → m ≤ k → k ≤ n →
      ∏ i ∈ Finset.Icc m k, p i
        ≤ Real.sqrt (((k - m + 1 : ℕ) : ℝ) ^ (k - m + 1)) * p m ^ (k - m + 1))
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    p k ≤ higham9_14_completePivotWilkinsonBound n * p 1 := by
  have h := higham9_14_wilkinson_max_pivot_bound p hpos hpiv hk1 hkn
  have hp1 : 0 < p 1 := hpos 1 le_rfl hn
  exact (div_le_iff₀ hp1).mp h

/-- Index embedding for the stage-`m` Gaussian-elimination iterate: position
`i` of the trailing `(n - m) × (n - m)` block sits at row/column `m + i` of
the full matrix. -/
def higham9_14_geShift {n : ℕ} (m : ℕ) (hm : m ≤ n) :
    Fin (n - m) → Fin n :=
  fun i => ⟨m + i.val, by have := i.isLt; omega⟩

@[simp] lemma higham9_14_geShift_val {n : ℕ} (m : ℕ) (hm : m ≤ n)
    (i : Fin (n - m)) :
    (higham9_14_geShift m hm i).val = m + i.val := rfl

/-- The stage-`m` Gaussian-elimination iterate (reduced matrix / Schur
complement) of an LU factorization: `S_m = L₂₂ · U₂₂`, the product of the
trailing `(n - m) × (n - m)` blocks of `L` and `U`. -/
noncomputable def higham9_14_geIterate {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    Fin (n - m) → Fin (n - m) → ℝ :=
  fun i j => ∑ t : Fin (n - m),
    L (higham9_14_geShift m hm i) (higham9_14_geShift m hm t) *
      U (higham9_14_geShift m hm t) (higham9_14_geShift m hm j)

/-- The trailing blocks of `L` and `U` form an exact LU certificate for the
stage-`m` iterate. -/
theorem higham9_14_geIterate_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    (m : ℕ) (hm : m ≤ n) :
    LUFactSpec (n - m) (higham9_14_geIterate L U m hm)
      (fun i j => L (higham9_14_geShift m hm i) (higham9_14_geShift m hm j))
      (fun i j => U (higham9_14_geShift m hm i) (higham9_14_geShift m hm j)) where
  L_diag i := hLU.L_diag _
  L_upper_zero i j hij :=
    hLU.L_upper_zero _ _ (by simp only [higham9_14_geShift_val]; omega)
  U_lower_zero i j hij :=
    hLU.U_lower_zero _ _ (by simp only [higham9_14_geShift_val]; omega)
  product_eq i j := rfl

/-- The stage-`0` iterate is the original matrix. -/
theorem higham9_14_geIterate_zero_apply {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    (i j : Fin (n - 0)) :
    higham9_14_geIterate L U 0 (Nat.zero_le n) i j
      = A ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le n 0)⟩
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.sub_le n 0)⟩ := by
  have hsh : ∀ x : Fin (n - 0), higham9_14_geShift 0 (Nat.zero_le n) x
      = (⟨x.val, lt_of_lt_of_le x.isLt (Nat.sub_le n 0)⟩ : Fin n) :=
    fun x => Fin.ext (by simp)
  unfold higham9_14_geIterate
  simp only [hsh]
  exact hLU.product_eq _ _

/-- Row `0` of the stage-`m` iterate is row `m` of `U` restricted to the
trailing columns: eliminating the first `m` rows and columns leaves the
current pivot row unchanged. -/
theorem higham9_14_geIterate_row_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    {m : ℕ} (hm : m < n) (hpos : 0 < n - m) (c : Fin (n - m)) :
    higham9_14_geIterate L U m (Nat.le_of_lt hm) ⟨0, hpos⟩ c
      = U ⟨m, hm⟩ (higham9_14_geShift m (Nat.le_of_lt hm) c) := by
  unfold higham9_14_geIterate
  rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin (n - m))
    (fun t _ ht => by
      have htpos : 0 < t.val := Nat.pos_of_ne_zero (fun h0 => ht (Fin.ext h0))
      rw [hLU.L_upper_zero _ _
        (by simp only [higham9_14_geShift_val]; omega), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  have h0 : higham9_14_geShift m (Nat.le_of_lt hm) ⟨0, hpos⟩
      = (⟨m, hm⟩ : Fin n) := Fin.ext (by simp)
  rw [h0, hLU.L_diag, one_mul]

/-- **Equation (9.14), segment constraint from an entry bound on the
stage-`m` iterate.**  If every entry of the stage-`m` iterate is bounded in
magnitude by `M`, the product of the `j` consecutive pivots
`U_{m,m}, …, U_{m+j-1,m+j-1}` is bounded by `√(j^j) · M^j`. -/
theorem higham9_14_completePivot_segment_pivot_bound {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    {m : ℕ} (hm : m ≤ n) {j : ℕ} (hj1 : 0 < j) (hjn : j ≤ n - m)
    {M : ℝ}
    (hM : ∀ i c : Fin (n - m), |higham9_14_geIterate L U m hm i c| ≤ M) :
    |∏ t : Fin j, U (higham9_14_geShift m hm (Fin.castLE hjn t))
        (higham9_14_geShift m hm (Fin.castLE hjn t))|
      ≤ Real.sqrt ((j : ℝ) ^ j) * M ^ j := by
  have hspec := higham9_14_geIterate_LUFactSpec hLU m hm
  exact higham9_14_abs_prod_leadingPivots_le_of_entries_le hspec hjn hj1
    (fun i c => hM _ _)

/-- **Equation (9.14), Wilkinson's complete-pivoting growth-factor upper
bound** (Wilkinson [1229, 1961]; Higham §9.4 states the bound without proof).

For an exact LU certificate `A = L·U` with nonzero pivots whose
Gaussian-elimination iterates satisfy the complete-pivoting invariant — every
entry of the stage-`m` reduced matrix `S_m = L₂₂U₂₂` is bounded in magnitude
by the stage-`m` pivot `|U_{m,m}|` (the defining property of complete
pivoting: the pivot is chosen as a largest-magnitude entry of the reduced
matrix) — the max-entry growth factor satisfies Wilkinson's displayed bound
`rho_n^c ≤ √n · (2 · 3^{1/2} ⋯ n^{1/(n-1)})^{1/2}`.

Proof assembly: the pivot magnitudes `p k = |U_{k-1,k-1}|` satisfy the
segment Hadamard constraints via
`higham9_14_completePivot_segment_pivot_bound` (Hadamard determinant bound on
the leading blocks of each iterate, whose entries the invariant bounds by the
stage pivot), so `higham9_14_wilkinson_pivot_le_bound_mul` bounds every pivot
by `WilkinsonBound n · p 1`; row `m` of `U` consists of row-`0` entries of the
stage-`m` iterate (`higham9_14_geIterate_row_zero`), each bounded by `p (m+1)`
via the invariant, and `p 1 = |A_{0,0}| ≤ maxEntryNorm A`, so every entry of
`U` is bounded by `WilkinsonBound n · maxEntryNorm A`. -/
theorem higham9_14_completePivot_growthFactorEntry_le_wilkinsonBound {n : ℕ}
    (hn : 0 < n) {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    (hpivnz : ∀ i : Fin n, U i i ≠ 0)
    (hCP : ∀ (m : ℕ) (hm : m < n) (i j : Fin (n - m)),
      |higham9_14_geIterate L U m (Nat.le_of_lt hm) i j|
        ≤ |U ⟨m, hm⟩ ⟨m, hm⟩|)
    (hA : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ higham9_14_completePivotWilkinsonBound n := by
  classical
  have hn1 : 1 ≤ n := hn
  have hbound_nonneg := higham9_14_completePivotWilkinsonBound_nonneg n
  -- the 1-indexed pivot-magnitude sequence
  set p : ℕ → ℝ :=
    fun k => if h : k - 1 < n then |U ⟨k - 1, h⟩ ⟨k - 1, h⟩| else 1 with hp
  have hpval : ∀ k, ∀ (h : k - 1 < n),
      p k = |U ⟨k - 1, h⟩ ⟨k - 1, h⟩| := by
    intro k h
    simp [hp, dif_pos h]
  have hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < p k := by
    intro k hk1 hkn
    rw [hpval k (by omega)]
    exact abs_pos.mpr (hpivnz _)
  -- segment Hadamard constraint for the pivot sequence
  have hpiv : ∀ m k, 1 ≤ m → m ≤ k → k ≤ n →
      ∏ i ∈ Finset.Icc m k, p i
        ≤ Real.sqrt (((k - m + 1 : ℕ) : ℝ) ^ (k - m + 1))
            * p m ^ (k - m + 1) := by
    intro m k hm1 hmk hkn
    have hstage : m - 1 < n := by omega
    have hstage_le : m - 1 ≤ n := Nat.le_of_lt hstage
    have hj1 : 0 < k - m + 1 := by omega
    have hjn : k - m + 1 ≤ n - (m - 1) := by omega
    have hMdef : ∀ i c : Fin (n - (m - 1)),
        |higham9_14_geIterate L U (m - 1) hstage_le i c| ≤ p m := by
      intro i c
      rw [hpval m (by omega)]
      exact hCP (m - 1) hstage i c
    have hseg := higham9_14_completePivot_segment_pivot_bound hLU hstage_le
      hj1 hjn hMdef
    -- convert the Icc product to the Fin product
    have h1 : ∏ i ∈ Finset.Icc m k, p i
        = ∏ i ∈ Finset.range (k - m + 1), p (m + i) := by
      rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
        Finset.prod_Ico_eq_prod_range,
        show k + 1 - m = k - m + 1 from by omega]
    have h2 : ∏ i ∈ Finset.range (k - m + 1), p (m + i)
        = ∏ t : Fin (k - m + 1), p (m + t.val) :=
      (Fin.prod_univ_eq_prod_range (fun i => p (m + i)) (k - m + 1)).symm
    have h3 : ∀ t : Fin (k - m + 1), p (m + t.val)
        = |U (higham9_14_geShift (m - 1) hstage_le (Fin.castLE hjn t))
            (higham9_14_geShift (m - 1) hstage_le (Fin.castLE hjn t))| := by
      intro t
      have hlt : m + t.val - 1 < n := by have := t.isLt; omega
      rw [hpval (m + t.val) hlt]
      have hidx : (⟨m + t.val - 1, hlt⟩ : Fin n)
          = higham9_14_geShift (m - 1) hstage_le (Fin.castLE hjn t) := by
        apply Fin.ext
        simp only [higham9_14_geShift_val, Fin.val_castLE]
        omega
      rw [hidx]
    have h4 : ∏ t : Fin (k - m + 1), p (m + t.val)
        = |∏ t : Fin (k - m + 1),
            U (higham9_14_geShift (m - 1) hstage_le (Fin.castLE hjn t))
              (higham9_14_geShift (m - 1) hstage_le (Fin.castLE hjn t))| := by
      rw [Finset.abs_prod]
      exact Finset.prod_congr rfl (fun t _ => h3 t)
    rw [h1, h2, h4]
    exact hseg
  -- the first pivot is an entry of `A`
  have hA00 : A ⟨0, hn⟩ ⟨0, hn⟩ = U ⟨0, hn⟩ ⟨0, hn⟩ := by
    rw [← hLU.product_eq ⟨0, hn⟩ ⟨0, hn⟩]
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)
      (fun t _ ht => by
        have htpos : 0 < t.val := Nat.pos_of_ne_zero (fun h0 => ht (Fin.ext h0))
        rw [hLU.L_upper_zero _ _ htpos, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [hLU.L_diag, one_mul]
  have hp1_le : p 1 ≤ maxEntryNorm hn A := by
    rw [hpval 1 (by omega)]
    show |U ⟨0, hn⟩ ⟨0, hn⟩| ≤ maxEntryNorm hn A
    rw [← hA00]
    exact entry_le_maxEntryNorm hn A _ _
  -- every entry of `U` is bounded by the Wilkinson bound times `maxEntryNorm A`
  have hentry : ∀ i j : Fin n,
      |U i j| ≤ higham9_14_completePivotWilkinsonBound n * maxEntryNorm hn A := by
    intro i j
    rcases lt_or_ge j.val i.val with hlt | hge
    · rw [hLU.U_lower_zero i j hlt, abs_zero]
      exact mul_nonneg hbound_nonneg (le_of_lt hA)
    · have hstage : i.val < n := i.isLt
      have hposnm : 0 < n - i.val := by omega
      have hc_lt : j.val - i.val < n - i.val := by have := j.isLt; omega
      set c : Fin (n - i.val) := ⟨j.val - i.val, hc_lt⟩ with hc
      have hshift : higham9_14_geShift i.val (Nat.le_of_lt hstage) c = j := by
        apply Fin.ext
        simp only [higham9_14_geShift_val, hc]
        omega
      have hrow := higham9_14_geIterate_row_zero hLU hstage hposnm c
      rw [hshift] at hrow
      have hUij : |U i j| ≤ |U ⟨i.val, hstage⟩ ⟨i.val, hstage⟩| := by
        have hUeq : U i j = U ⟨i.val, hstage⟩ j := rfl
        rw [hUeq, ← hrow]
        exact hCP i.val hstage ⟨0, hposnm⟩ c
      have hpk : p (i.val + 1) = |U ⟨i.val, hstage⟩ ⟨i.val, hstage⟩| := by
        rw [hpval (i.val + 1) (by omega)]
        rfl
      have hUii_le : |U ⟨i.val, hstage⟩ ⟨i.val, hstage⟩|
          ≤ higham9_14_completePivotWilkinsonBound n * p 1 := by
        rw [← hpk]
        exact higham9_14_wilkinson_pivot_le_bound_mul hn1 p hpos hpiv
          (by omega) (by have := i.isLt; omega)
      calc |U i j| ≤ |U ⟨i.val, hstage⟩ ⟨i.val, hstage⟩| := hUij
        _ ≤ higham9_14_completePivotWilkinsonBound n * p 1 := hUii_le
        _ ≤ higham9_14_completePivotWilkinsonBound n * maxEntryNorm hn A :=
            mul_le_mul_of_nonneg_left hp1_le hbound_nonneg
  exact growthFactorEntry_le_of_entry_bound_factor hn A U _ hA hentry

/-- **Equation (9.14), all-iterates form of Wilkinson's complete-pivoting
growth bound.**  Higham's growth factor (Definition 9.6) maximizes over the
entries of every intermediate reduced matrix, not only the final `U`; under
the complete-pivoting invariant, every entry of every stage-`m` iterate is
bounded by `WilkinsonBound n · maxEntryNorm A`, so the all-iterates growth
factor satisfies the same displayed bound as the `U`-entry version. -/
theorem higham9_14_completePivot_iterate_entry_le_wilkinsonBound_mul {n : ℕ}
    (hn : 0 < n) {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    (hpivnz : ∀ i : Fin n, U i i ≠ 0)
    (hCP : ∀ (m : ℕ) (hm : m < n) (i j : Fin (n - m)),
      |higham9_14_geIterate L U m (Nat.le_of_lt hm) i j|
        ≤ |U ⟨m, hm⟩ ⟨m, hm⟩|)
    (hA : 0 < maxEntryNorm hn A)
    {m : ℕ} (hm : m < n) (i j : Fin (n - m)) :
    |higham9_14_geIterate L U m (Nat.le_of_lt hm) i j|
      ≤ higham9_14_completePivotWilkinsonBound n * maxEntryNorm hn A := by
  have hmain := higham9_14_completePivot_growthFactorEntry_le_wilkinsonBound
    hn hLU hpivnz hCP hA
  have hUmax : maxEntryNorm hn U
      ≤ higham9_14_completePivotWilkinsonBound n * maxEntryNorm hn A := by
    unfold growthFactorEntry at hmain
    rwa [div_le_iff₀ hA] at hmain
  calc |higham9_14_geIterate L U m (Nat.le_of_lt hm) i j|
      ≤ |U ⟨m, hm⟩ ⟨m, hm⟩| := hCP m hm i j
    _ ≤ maxEntryNorm hn U := entry_le_maxEntryNorm hn U _ _
    _ ≤ higham9_14_completePivotWilkinsonBound n * maxEntryNorm hn A := hUmax

/-- **Problem 9.11 / equation (9.15)**, the source growth-function set
underlying `g(n) = sup_A rho_n^c(A)`, parameterized by the still-separate
complete-pivoting growth map `rhoC`. -/
def higham9_completePivotGrowthSet (n : ℕ)
    (rhoC : (Fin n → Fin n → ℝ) → ℝ) : Set ℝ :=
  Set.range rhoC

/-- **Problem 9.11 / equation (9.15)**, the source growth-function supremum
`g(n)`, parameterized by a complete-pivoting growth map `rhoC`.  This definition
records the supremum step only; it does not claim that the complete-pivoting
algorithmic trace for `rho_n^c` has been formalized. -/
noncomputable def higham9_completePivotGrowthSup (n : ℕ)
    (rhoC : (Fin n → Fin n → ℝ) → ℝ) : ℝ :=
  sSup (higham9_completePivotGrowthSet n rhoC)

/-- **Problem 9.11 / equation (9.15)**, every concrete complete-pivoting growth
value is bounded by the supremum `g(n)` when the source growth family is bounded
above. -/
theorem higham9_completePivotGrowth_le_sup (n : ℕ)
    (rhoC : (Fin n → Fin n → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet n rhoC))
    (A : Fin n → Fin n → ℝ) :
    rhoC A ≤ higham9_completePivotGrowthSup n rhoC := by
  exact le_csSup hBdd ⟨A, rfl⟩

/-- **Problem 9.11**, source lower-bound step with `g(2n)` instantiated as the
supremum of complete-pivoting growth values.  The remaining open source work is
to formalize the actual complete-pivoting trace `rhoC` and the sine-matrix
witness that supplies `2 * theta(S_n) = n + 1`. -/
theorem higham9_11_complete_pivoting_lower_bound_from_witness (n : ℕ)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (B : Fin (2 * n) → Fin (2 * n) → ℝ)
    (thetaSn : ℝ)
    (hrho : 2 * thetaSn ≤ rhoC B)
    (hSn : 2 * thetaSn = (n : ℝ) + 1) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC := by
  have hg : rhoC B ≤ higham9_completePivotGrowthSup (2 * n) rhoC :=
    higham9_completePivotGrowth_le_sup (2 * n) rhoC hBdd B
  exact higham9_11_complete_pivoting_lower_bound_consequence n
    (higham9_completePivotGrowthSup (2 * n) rhoC) (rhoC B) thetaSn hg hrho hSn

/-- **Problem 9.11**, inequality-form source lower-bound step with `g(2n)`
instantiated as the supremum of complete-pivoting growth values.

This is the form aligned with the sine-matrix witness proved in this file,
which supplies `(n : ℝ) + 1 ≤ 2 * theta(S_n)`.  The complete-pivoting trace
itself remains an explicit hypothesis through `rhoC` and `hrho`. -/
theorem higham9_11_complete_pivoting_lower_bound_from_witness_le (n : ℕ)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (B : Fin (2 * n) → Fin (2 * n) → ℝ)
    (thetaSn : ℝ)
    (hrho : 2 * thetaSn ≤ rhoC B)
    (hSn : (n : ℝ) + 1 ≤ 2 * thetaSn) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC := by
  have hg : rhoC B ≤ higham9_completePivotGrowthSup (2 * n) rhoC :=
    higham9_completePivotGrowth_le_sup (2 * n) rhoC hBdd B
  exact higham9_11_complete_pivoting_lower_bound_consequence_le n
    (higham9_completePivotGrowthSup (2 * n) rhoC) (rhoC B) thetaSn hg hrho hSn

/-- **Problem 9.11**, flattened sine-block witness for the source
`g(2n) = sup_A rho_n^c(A)` surface.

The theorem instantiates the bounded-family supremum with the flattened
`[[S_n,S_n],[S_n,-S_n]]` matrix.  The complete-pivoting growth lower bound for
that concrete flattened matrix remains the explicit hypothesis `hrho`. -/
theorem higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block
    {n : ℕ} (hn : 0 < n)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (hrho :
      1 /
        (blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n)) *
          blockMaxNorm (by norm_num : 0 < 2) hn
            (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n))) ≤
        rhoC
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))) ) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC := by
  have hg :
      rhoC
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))) ≤
        higham9_completePivotGrowthSup (2 * n) rhoC :=
    higham9_completePivotGrowth_le_sup (2 * n) rhoC hBdd
      (higham9_11_flattenTwoBlock hn (higham9_11_blockMatrix (higham9_12_sineMatrix n)))
  exact higham9_11_complete_pivoting_lower_bound_from_sine_block_theta hn
    (higham9_completePivotGrowthSup (2 * n) rhoC)
    (rhoC
      (higham9_11_flattenTwoBlock hn (higham9_11_blockMatrix (higham9_12_sineMatrix n))))
    hg hrho

/-- **Problem 9.11**, fully flattened max-entry-norm form of the sine-block
bounded-supremum witness.

This is the same bridge as
`higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block`, but the
visible growth hypothesis uses ordinary max-entry norms on the flattened
`Fin (2n)` matrix and flattened inverse candidate. -/
theorem higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block_maxEntry
    {n : ℕ} (hn : 0 < n)
    (rhoC : (Fin (2 * n) → Fin (2 * n) → ℝ) → ℝ)
    (hBdd : BddAbove (higham9_completePivotGrowthSet (2 * n) rhoC))
    (hrho :
      1 /
        (maxEntryNorm (by omega : 0 < 2 * n)
            (higham9_11_flattenTwoBlock hn
              (higham9_11_blockMatrix (higham9_12_sineMatrix n))) *
          maxEntryNorm (by omega : 0 < 2 * n)
            (higham9_11_flattenTwoBlock hn
              (higham9_11_blockInverseCandidate (higham9_12_sineMatrix n)))) ≤
        rhoC
          (higham9_11_flattenTwoBlock hn
            (higham9_11_blockMatrix (higham9_12_sineMatrix n))) ) :
    (n : ℝ) + 1 ≤ higham9_completePivotGrowthSup (2 * n) rhoC :=
  higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block hn rhoC hBdd
    (by
      simpa [higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm] using hrho)

/-- **Equation (9.16)**, Foster's scalar rook-pivoting growth upper-bound RHS
`1.5 * n^(3/4 * log n)`.

This is only the source scalar surface. The actual rook-pivoting growth theorem
and recursive trace remain open Split-2 work. -/
noncomputable def higham9_16_rookPivotFosterBound (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) * (n : ℝ) ^ ((3 / 4 : ℝ) * Real.log (n : ℝ))

lemma higham9_16_rookPivotFosterBound_nonneg (n : ℕ) :
    0 ≤ higham9_16_rookPivotFosterBound n := by
  unfold higham9_16_rookPivotFosterBound
  exact mul_nonneg (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg n) ((3 / 4 : ℝ) * Real.log (n : ℝ)))

lemma higham9_16_rookPivotFosterBound_pos {n : ℕ} (hn : 0 < n) :
    0 < higham9_16_rookPivotFosterBound n := by
  unfold higham9_16_rookPivotFosterBound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos (by norm_num)
    (Real.rpow_pos_of_pos hnR ((3 / 4 : ℝ) * Real.log (n : ℝ)))

/-- **Equation (9.16)**, exponential log-square form of Foster's scalar
rook-pivoting RHS.

This is the scalar form needed by the remaining Foster product proof, where
products of stage factors are compared after taking logarithms. -/
lemma higham9_16_rookPivotFosterBound_eq_three_halves_mul_exp_log_sq
    {n : ℕ} (hn : 0 < n) :
    higham9_16_rookPivotFosterBound n =
      (3 / 2 : ℝ) *
        Real.exp ((3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
  unfold higham9_16_rookPivotFosterBound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnR]
  congr 1
  congr 1
  ring

/-- **Equation (9.16)**, logarithmic form of Foster's scalar rook-pivoting
RHS. -/
lemma higham9_16_rookPivotFosterBound_log {n : ℕ} (hn : 0 < n) :
    Real.log (higham9_16_rookPivotFosterBound n) =
      Real.log (3 / 2 : ℝ) +
        (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  unfold higham9_16_rookPivotFosterBound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcoef : (3 / 2 : ℝ) ≠ 0 := by norm_num
  have hrpow_ne :
      (n : ℝ) ^ ((3 / 4 : ℝ) * Real.log (n : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnR ((3 / 4 : ℝ) * Real.log (n : ℝ)))
  rw [Real.log_mul hcoef hrpow_ne]
  rw [Real.log_rpow hnR]
  ring

/-- **Equation (9.16)**, adjacent logarithmic increment for Foster's scalar
rook-pivoting RHS. -/
lemma higham9_16_rookPivotFosterBound_log_succ_sub {n : ℕ} (hn : 0 < n) :
    Real.log (higham9_16_rookPivotFosterBound (n + 1)) -
      Real.log (higham9_16_rookPivotFosterBound n) =
        (3 / 4 : ℝ) *
          ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
            (Real.log (n : ℝ)) ^ 2) := by
  have hsucc : 0 < n + 1 := by omega
  rw [higham9_16_rookPivotFosterBound_log hsucc,
    higham9_16_rookPivotFosterBound_log hn]
  ring

/-- **Equation (9.16)**, adjacent ratio form of Foster's scalar rook-pivoting
RHS. -/
lemma higham9_16_rookPivotFosterBound_succ_div {n : ℕ} (hn : 0 < n) :
    higham9_16_rookPivotFosterBound (n + 1) /
      higham9_16_rookPivotFosterBound n =
        Real.exp
          ((3 / 4 : ℝ) *
            ((Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 -
              (Real.log (n : ℝ)) ^ 2)) := by
  have hsucc : 0 < n + 1 := by omega
  rw [higham9_16_rookPivotFosterBound_eq_three_halves_mul_exp_log_sq hsucc,
    higham9_16_rookPivotFosterBound_eq_three_halves_mul_exp_log_sq hn]
  rw [mul_div_mul_left _ _ (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  rw [← Real.exp_sub]
  congr 1
  ring

/-- **Equation (9.16)**, Foster RHS lower bound in positive dimensions.

For `n >= 1`, the scalar factor `n^(3/4 log n)` is at least one, so Foster's
displayed rook-pivoting RHS is at least `3/2`. -/
lemma higham9_16_rookPivotFosterBound_ge_three_halves {n : ℕ} (hn : 0 < n) :
    (3 / 2 : ℝ) ≤ higham9_16_rookPivotFosterBound n := by
  unfold higham9_16_rookPivotFosterBound
  have hn_ge_one_nat : 1 ≤ n := Nat.succ_le_of_lt hn
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one_nat
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_ge_one
  have hexp_nonneg : 0 ≤ (3 / 4 : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (by norm_num) hlog_nonneg
  have hrpow_ge_one :
      1 ≤ (n : ℝ) ^ ((3 / 4 : ℝ) * Real.log (n : ℝ)) :=
    Real.one_le_rpow hn_ge_one hexp_nonneg
  calc
    (3 / 2 : ℝ) =
        (3 / 2 : ℝ) * 1 := by ring
    _ ≤ (3 / 2 : ℝ) *
        (n : ℝ) ^ ((3 / 4 : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrpow_ge_one (by norm_num)

/-- **Equation (9.16)**, Foster's displayed rook-pivoting RHS is at least one
in every positive dimension. -/
lemma higham9_16_rookPivotFosterBound_ge_one {n : ℕ} (hn : 0 < n) :
    1 ≤ higham9_16_rookPivotFosterBound n :=
  le_trans (by norm_num : (1 : ℝ) ≤ 3 / 2)
    (higham9_16_rookPivotFosterBound_ge_three_halves hn)

/-- **Equation (9.16)**, base value of Foster's displayed rook-pivoting RHS in
dimension one. -/
lemma higham9_16_rookPivotFosterBound_one :
    higham9_16_rookPivotFosterBound 1 = 3 / 2 := by
  norm_num [higham9_16_rookPivotFosterBound]

/-- **Equation (9.16)**, in dimension two Foster's displayed rook-pivoting RHS
dominates the elementary recursive trace bound value `2`.

The proof uses Mathlib's certified decimal lower bound for `log 2` and the
basic inequality `1 + x <= exp x`. -/
lemma higham9_16_rookPivotFosterBound_two_ge_two :
    (2 : ℝ) ≤ higham9_16_rookPivotFosterBound 2 := by
  unfold higham9_16_rookPivotFosterBound
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by
    exact le_of_lt
      (lt_of_lt_of_le (by norm_num : (2 / 3 : ℝ) < 0.6931471803)
        Real.log_two_gt_d9.le)
  have hbase : (4 / 3 : ℝ) ≤ (2 : ℝ) ^ ((3 / 4 : ℝ) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harg : (1 / 3 : ℝ) ≤ Real.log 2 * ((3 / 4 : ℝ) * Real.log 2) := by
      nlinarith [hlog]
    have h13 : (4 / 3 : ℝ) ≤ Real.exp (1 / 3 : ℝ) := by
      calc
        (4 / 3 : ℝ) = 1 + (1 / 3 : ℝ) := by norm_num
        _ ≤ Real.exp (1 / 3 : ℝ) := by
          simpa [add_comm] using Real.add_one_le_exp (1 / 3 : ℝ)
    exact le_trans h13 (Real.exp_le_exp.mpr harg)
  calc
    (2 : ℝ) = (3 / 2 : ℝ) * (4 / 3 : ℝ) := by norm_num
    _ ≤ (3 / 2 : ℝ) * (2 : ℝ) ^ ((3 / 4 : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)

/-- **Equation (9.16)**, in dimension one Foster's displayed rook-pivoting RHS
dominates the elementary recursive trace bound `2^(n-1)`. -/
lemma higham9_16_pow_two_le_rookPivotFosterBound_of_eq_one {n : ℕ}
    (hn : n = 1) :
    (2 : ℝ) ^ (n - 1) ≤ higham9_16_rookPivotFosterBound n := by
  subst n
  simpa [higham9_16_rookPivotFosterBound_one] using
    (by norm_num : (1 : ℝ) ≤ 3 / 2)

/-- **Equation (9.16)**, in dimensions one and two Foster's displayed
rook-pivoting RHS dominates the elementary recursive trace bound `2^(n-1)`. -/
lemma higham9_16_pow_two_le_rookPivotFosterBound_of_le_two {n : ℕ}
    (hn : 0 < n) (hle : n ≤ 2) :
    (2 : ℝ) ^ (n - 1) ≤ higham9_16_rookPivotFosterBound n := by
  have hcases : n = 1 ∨ n = 2 := by omega
  rcases hcases with hone | htwo
  · exact higham9_16_pow_two_le_rookPivotFosterBound_of_eq_one hone
  · subst n
    simpa using higham9_16_rookPivotFosterBound_two_ge_two

/-- **Equation (9.16)**, monotonicity of Foster's logarithmic scalar factor on
positive dimensions. -/
lemma higham9_16_rookPivotFosterFactor_le_of_le {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n ≤ m) :
    (n : ℝ) ^ ((3 / 4 : ℝ) * Real.log (n : ℝ)) ≤
      (m : ℝ) ^ ((3 / 4 : ℝ) * Real.log (m : ℝ)) := by
  have hn_pos_nat : 0 < n := by omega
  have hm_pos_nat : 0 < m := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_ge_one
  have hlog_le : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hn_pos hnmR
  have hlog_sq :
      Real.log (n : ℝ) * Real.log (n : ℝ) ≤
        Real.log (m : ℝ) * Real.log (m : ℝ) :=
    mul_self_le_mul_self hlog_nonneg hlog_le
  have hcoef_nonneg : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hexp_le :
      (3 / 4 : ℝ) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        (3 / 4 : ℝ) * (Real.log (m : ℝ) * Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_sq hcoef_nonneg
  rw [Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hm_pos]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- **Equation (9.16)**, order form of monotonicity for Foster's scalar
rook-pivoting RHS. -/
theorem higham9_16_rookPivotFosterBound_le_of_le {n m : ℕ} (hnm : n ≤ m) :
    higham9_16_rookPivotFosterBound n ≤
      higham9_16_rookPivotFosterBound m := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          exact le_rfl
      | succ k =>
          have hzero : higham9_16_rookPivotFosterBound 0 = (3 / 2 : ℝ) := by
            norm_num [higham9_16_rookPivotFosterBound]
          have hmpos : 0 < k + 1 := by omega
          calc
            higham9_16_rookPivotFosterBound 0 = (3 / 2 : ℝ) := hzero
            _ ≤ higham9_16_rookPivotFosterBound (k + 1) :=
              higham9_16_rookPivotFosterBound_ge_three_halves hmpos
  | succ k =>
      unfold higham9_16_rookPivotFosterBound
      have hn : 1 ≤ k + 1 := by omega
      have hfactor :
          ((k + 1 : ℕ) : ℝ) ^
              ((3 / 4 : ℝ) * Real.log ((k + 1 : ℕ) : ℝ)) ≤
            (m : ℝ) ^ ((3 / 4 : ℝ) * Real.log (m : ℝ)) :=
        higham9_16_rookPivotFosterFactor_le_of_le hn hnm
      exact mul_le_mul_of_nonneg_left hfactor (by norm_num)

/-- **Equation (9.16)**, successor-ratio form of Foster displayed-bound
monotonicity. -/
lemma higham9_16_rookPivotFosterBound_succ_div_ge_one {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) ≤
      higham9_16_rookPivotFosterBound (n + 1) /
        higham9_16_rookPivotFosterBound n := by
  have hpos := higham9_16_rookPivotFosterBound_pos hn
  rw [le_div_iff₀ hpos]
  simpa [one_mul] using
    higham9_16_rookPivotFosterBound_le_of_le (Nat.le_succ n)

/-- **Equation (9.16)**, Foster's scalar rook-pivoting RHS is at least two in
every dimension at least two. -/
lemma higham9_16_rookPivotFosterBound_ge_two_of_ge_two {n : ℕ}
    (hn : 2 ≤ n) :
    (2 : ℝ) ≤ higham9_16_rookPivotFosterBound n :=
  le_trans higham9_16_rookPivotFosterBound_two_ge_two
    (higham9_16_rookPivotFosterBound_le_of_le hn)

/-- **Equation (9.16)**, Foster's scalar rook-pivoting RHS is monotone in the
matrix order parameter. -/
theorem higham9_16_rookPivotFosterBound_monotone :
    Monotone higham9_16_rookPivotFosterBound := by
  intro n m hnm
  exact higham9_16_rookPivotFosterBound_le_of_le hnm

/-- **Problem 9.13**, the per-modification threshold-pivoting factor
`1 + tau^{-1}`. -/
noncomputable def higham9_13_thresholdFactor (τ : ℝ) : ℝ :=
  1 + τ⁻¹

lemma higham9_13_thresholdFactor_ge_one (τ : ℝ) (hτ : 0 < τ) :
    1 ≤ higham9_13_thresholdFactor τ := by
  unfold higham9_13_thresholdFactor
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ)
  linarith

lemma higham9_13_thresholdFactor_nonneg (τ : ℝ) (hτ : 0 < τ) :
    0 ≤ higham9_13_thresholdFactor τ :=
  le_trans (by norm_num : (0 : ℝ) ≤ 1)
    (higham9_13_thresholdFactor_ge_one τ hτ)

/-- **Problem 9.13**, unit threshold pivoting gives per-modification factor at
most two. -/
lemma higham9_13_thresholdFactor_le_two_of_one_le {τ : ℝ} (hτ : 1 ≤ τ) :
    higham9_13_thresholdFactor τ ≤ 2 := by
  have hinv_le_one : τ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hτ
  unfold higham9_13_thresholdFactor
  linarith

/-- **Problem 9.13**, the threshold-pivoting modification factor is bounded by
`2^mu` when `tau >= 1`. -/
lemma higham9_13_thresholdFactor_pow_le_two_pow_of_one_le {τ : ℝ}
    (hτ : 1 ≤ τ) (μ : ℕ) :
    higham9_13_thresholdFactor τ ^ μ ≤ (2 : ℝ) ^ μ :=
  pow_le_pow_left₀
    (higham9_13_thresholdFactor_nonneg τ (lt_of_lt_of_le zero_lt_one hτ))
    (higham9_13_thresholdFactor_le_two_of_one_le hτ) μ

/-- **Problem 9.13**, one scalar threshold-pivoting update.

If the old entry and the pivot-row entry are both bounded by the current
column maximum and the multiplier is bounded by `tau^{-1}`, then the updated
entry is bounded by `(1 + tau^{-1})` times the old column maximum. -/
theorem higham9_13_threshold_update_abs_bound (τ maxOld old pivot multiplier : ℝ)
    (hτ : 0 < τ)
    (hold : |old| ≤ maxOld)
    (hpivot : |pivot| ≤ maxOld)
    (hmult : |multiplier| ≤ τ⁻¹) :
    |old - multiplier * pivot| ≤
      higham9_13_thresholdFactor τ * maxOld := by
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ)
  have hmul : |multiplier * pivot| ≤ τ⁻¹ * maxOld := by
    rw [abs_mul]
    exact mul_le_mul hmult hpivot (abs_nonneg pivot) hτinv
  have htri : |old - multiplier * pivot| ≤ |old| + |multiplier * pivot| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le old (-(multiplier * pivot))
  calc
    |old - multiplier * pivot|
        ≤ |old| + |multiplier * pivot| := htri
    _ ≤ maxOld + τ⁻¹ * maxOld := add_le_add hold hmul
    _ = higham9_13_thresholdFactor τ * maxOld := by
        unfold higham9_13_thresholdFactor
        ring

/-- **Problem 9.13**, iteration over the number of modifications to a sparse
column.  If each modification of column `j` multiplies its running maximum by
at most `1 + tau^{-1}`, then after `mu` modifications the source bound follows. -/
theorem higham9_13_column_growth_by_modification_count (τ : ℝ) (hτ : 0 < τ)
    (colMax : ℕ → ℝ) :
    ∀ μ : ℕ,
      (∀ t : ℕ, t < μ →
        colMax (t + 1) ≤ higham9_13_thresholdFactor τ * colMax t) →
      colMax μ ≤ higham9_13_thresholdFactor τ ^ μ * colMax 0 := by
  intro μ
  induction μ with
  | zero =>
      intro _hstep
      simp
  | succ μ ih =>
      intro hstep
      have hstep_prev : ∀ t : ℕ, t < μ →
          colMax (t + 1) ≤ higham9_13_thresholdFactor τ * colMax t := by
        intro t ht
        exact hstep t (Nat.lt_trans ht (Nat.lt_succ_self μ))
      have hih := ih hstep_prev
      have hlast :
          colMax (μ + 1) ≤ higham9_13_thresholdFactor τ * colMax μ :=
        hstep μ (Nat.lt_succ_self μ)
      have hfactor_nonneg : 0 ≤ higham9_13_thresholdFactor τ :=
        higham9_13_thresholdFactor_nonneg τ hτ
      calc
        colMax (Nat.succ μ)
            = colMax (μ + 1) := rfl
        _ ≤ higham9_13_thresholdFactor τ * colMax μ := hlast
        _ ≤ higham9_13_thresholdFactor τ *
              (higham9_13_thresholdFactor τ ^ μ * colMax 0) :=
            mul_le_mul_of_nonneg_left hih hfactor_nonneg
        _ = higham9_13_thresholdFactor τ ^ Nat.succ μ * colMax 0 := by
            rw [pow_succ]
            ring

/-- A max-entry norm is bounded by any uniform entrywise absolute-value bound. -/
theorem higham9_13_maxEntryNorm_bound_of_entry_bound {n : ℕ} (hn : 0 < n)
    (U : Fin n → Fin n → ℝ) (B : ℝ)
    (hB : ∀ i j : Fin n, |U i j| ≤ B) :
    maxEntryNorm hn U ≤ B := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact hB i j

/-- **Problem 9.13**, source-facing growth-factor consequence.

If every entry of the final `U` is bounded by
`(1 + tau^{-1})^muMax * max_i,j |a_ij|`, then Higham's max-entry growth factor
satisfies `rho_n <= (1 + tau^{-1})^muMax`. -/
theorem higham9_13_growthFactorEntry_bound_of_sparse_columns {n : ℕ}
    (hn : 0 < n) (τ : ℝ) (_hτ : 0 < τ)
    (μmax : ℕ) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hEntry : ∀ i j : Fin n,
      |U i j| ≤ higham9_13_thresholdFactor τ ^ μmax * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ higham9_13_thresholdFactor τ ^ μmax := by
  have hU :
      maxEntryNorm hn U ≤
        higham9_13_thresholdFactor τ ^ μmax * maxEntryNorm hn A :=
    higham9_13_maxEntryNorm_bound_of_entry_bound hn U
      (higham9_13_thresholdFactor τ ^ μmax * maxEntryNorm hn A) hEntry
  unfold growthFactorEntry
  rw [div_le_iff₀ hA]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hU

/-- **Problem 9.13**, column-count form.

This packages the appendix argument that `mu_j`, the number of nonzeros in
column `j` of `U`, bounds the number of modifications to entries in that
column.  Once the per-column entry bounds are known, taking
`muMax >= max_j mu_j` gives `rho_n <= (1 + tau^{-1})^muMax`. -/
theorem higham9_13_growthFactorEntry_bound_of_column_counts {n : ℕ}
    (hn : 0 < n) (τ : ℝ) (hτ : 0 < τ)
    (μ : Fin n → ℕ) (μmax : ℕ)
    (hμ : ∀ j : Fin n, μ j ≤ μmax)
    (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hEntry : ∀ i j : Fin n,
      |U i j| ≤ higham9_13_thresholdFactor τ ^ μ j * maxEntryNorm hn A) :
    growthFactorEntry hn A U hA ≤ higham9_13_thresholdFactor τ ^ μmax := by
  apply higham9_13_growthFactorEntry_bound_of_sparse_columns hn τ hτ μmax A U hA
  intro i j
  have hpow :
      higham9_13_thresholdFactor τ ^ μ j ≤
        higham9_13_thresholdFactor τ ^ μmax :=
    pow_le_pow_right₀ (higham9_13_thresholdFactor_ge_one τ hτ) (hμ j)
  exact le_trans (hEntry i j)
    (mul_le_mul_of_nonneg_right hpow (le_of_lt hA))

/-- **Problem 9.13**, end-to-end sparse-column modification-count bound.

For each column `j`, `colMax j t` is the running maximum after `t`
modifications to that column.  If threshold pivoting gives the per-modification
factor `1 + tau^{-1}`, the initial column maxima are bounded by
`max_i,j |a_ij|`, and `muMax` bounds the column modification counts `mu_j`,
then Higham's max-entry growth factor satisfies
`rho_n <= (1 + tau^{-1})^muMax`. -/
theorem higham9_13_growthFactorEntry_bound_from_column_modifications {n : ℕ}
    (hn : 0 < n) (τ : ℝ) (hτ : 0 < τ)
    (μ : Fin n → ℕ) (μmax : ℕ)
    (hμ : ∀ j : Fin n, μ j ≤ μmax)
    (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (colMax : Fin n → ℕ → ℝ)
    (hstep : ∀ j : Fin n, ∀ t : ℕ, t < μ j →
      colMax j (t + 1) ≤ higham9_13_thresholdFactor τ * colMax j t)
    (hinitial : ∀ j : Fin n, colMax j 0 ≤ maxEntryNorm hn A)
    (hfinal : ∀ i j : Fin n, |U i j| ≤ colMax j (μ j)) :
    growthFactorEntry hn A U hA ≤ higham9_13_thresholdFactor τ ^ μmax := by
  apply higham9_13_growthFactorEntry_bound_of_column_counts hn τ hτ μ μmax hμ A U hA
  intro i j
  have hiter :
      colMax j (μ j) ≤
        higham9_13_thresholdFactor τ ^ μ j * colMax j 0 :=
    higham9_13_column_growth_by_modification_count τ hτ (colMax j) (μ j) (hstep j)
  have hfactor_pow_nonneg :
      0 ≤ higham9_13_thresholdFactor τ ^ μ j :=
    pow_nonneg (higham9_13_thresholdFactor_nonneg τ hτ) (μ j)
  calc
    |U i j| ≤ colMax j (μ j) := hfinal i j
    _ ≤ higham9_13_thresholdFactor τ ^ μ j * colMax j 0 := hiter
    _ ≤ higham9_13_thresholdFactor τ ^ μ j * maxEntryNorm hn A :=
        mul_le_mul_of_nonneg_left (hinitial j) hfactor_pow_nonneg

/-- **Problem 9.13**, unit-threshold sparse-column growth corollary.

When the threshold parameter satisfies `tau >= 1`, the source bound
`(1 + tau^{-1})^muMax` is at most the simpler `2^muMax`. -/
theorem higham9_13_growthFactorEntry_bound_from_column_modifications_two_pow
    {n : ℕ}
    (hn : 0 < n) (τ : ℝ) (hτ : 1 ≤ τ)
    (μ : Fin n → ℕ) (μmax : ℕ)
    (hμ : ∀ j : Fin n, μ j ≤ μmax)
    (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (colMax : Fin n → ℕ → ℝ)
    (hstep : ∀ j : Fin n, ∀ t : ℕ, t < μ j →
      colMax j (t + 1) ≤ higham9_13_thresholdFactor τ * colMax j t)
    (hinitial : ∀ j : Fin n, colMax j 0 ≤ maxEntryNorm hn A)
    (hfinal : ∀ i j : Fin n, |U i j| ≤ colMax j (μ j)) :
    growthFactorEntry hn A U hA ≤ (2 : ℝ) ^ μmax := by
  have hbase :=
    higham9_13_growthFactorEntry_bound_from_column_modifications hn τ
      (lt_of_lt_of_le zero_lt_one hτ) μ μmax hμ A U hA colMax
      hstep hinitial hfinal
  exact hbase.trans
    (higham9_13_thresholdFactor_pow_le_two_pow_of_one_le hτ μmax)

/-- **Problem 9.14**, source-facing predicate for an input that is
pre-pivoted for GEPP: recursive partial pivoting can always choose the leading
row, so no row interchanges are required. -/
abbrev higham_problem9_14_PrePivotedGEPP {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Prop :=
  higham9_7_PartialPivotNoInterchangeTrace 0 n A

/-- **Problem 9.14 / GEPP side**, a no-interchange partial-pivoting trace
constructs an exact no-pivot LU certificate by the standard Schur-complement
induction.  This proves the pre-pivoted GEPP factorization side without
assuming the still-open row-reversal or pairwise-pivoting trace equivalence. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec :
    ∀ {t n : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotNoInterchangeTrace t n A →
        ∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U := by
  intro t n A htrace
  induction htrace with
  | done =>
      refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_⟩
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step _hchoice hpivot _hnext ih =>
      obtain ⟨L₁, U₁, hLU₁⟩ := ih
      exact
        ⟨luFirstStepL _ L₁, luFirstStepU _ U₁,
          LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁⟩

/-- **Problem 9.14 / GEPP side**, a no-interchange partial-pivoting trace
constructs exact LU factors whose diagonal pivots are all nonzero.  This is the
nondegeneracy bridge needed before using ordinary exact-LU uniqueness for the
"same LU factorization" clause in Problem 9.14. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec_pivots_ne_zero :
    ∀ {t n : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotNoInterchangeTrace t n A →
        ∃ L U : Fin n → Fin n → ℝ,
          LUFactSpec n A L U ∧ ∀ i : Fin n, U i i ≠ 0 := by
  intro t n A htrace
  induction htrace with
  | done =>
      refine ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_, ?_⟩
      · refine
          { L_diag := ?_
            L_upper_zero := ?_
            U_lower_zero := ?_
            product_eq := ?_ }
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step _hchoice hpivot _hnext ih =>
      obtain ⟨L₁, U₁, hLU₁, hU₁diag⟩ := ih
      refine
        ⟨luFirstStepL _ L₁, luFirstStepU _ U₁,
          LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁, ?_⟩
      intro i
      by_cases hi : i = 0
      · subst i
        simpa [luFirstStepU] using hpivot
      · have hdiag := hU₁diag (i.pred hi)
        simpa [luFirstStepU, hi] using hdiag

/-- **Problem 9.14 / GEPP side**, a no-interchange partial-pivoting trace is
nonsingular.  The proof uses the locally constructed exact LU factors with
nonzero pivots, not a separate determinant assumption. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero
    {t n : ℕ} {A : Fin n → Fin n → ℝ}
    (htrace : higham9_7_PartialPivotNoInterchangeTrace t n A) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  obtain ⟨L, U, hLU, hUdiag⟩ :=
    higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec_pivots_ne_zero
      htrace
  exact (higham9_1_det_ne_zero_iff_pivots_ne_zero hLU).mpr hUdiag

/-- **Problem 9.14**, source-facing consequence: if `A` is pre-pivoted for
GEPP, then the no-interchange exact LU factorization exists.  The equality with
the §9.9 row-reversal method and pairwise pivoting remains a separate open
trace-equivalence target. -/
theorem higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∃ L U : Fin n → Fin n → ℝ, LUFactSpec n A L U :=
  higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec hpre

/-- **Problem 9.14 / GEPP side**, pre-pivoted GEPP supplies a nonsingular
exact no-pivot LU side.  This is a source-facing specialization of the
trace-level nonzero-pivot construction. -/
theorem higham_problem9_14_PrePivotedGEPP_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
  higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero hpre

/-- **Problem 9.14 / same-LU bridge**, for a pre-pivoted input the exact LU
factorization of `A` is unique.  Hence any later source-faithful §9.9 or
pairwise-pivoting trace that is proved to return an exact `LUFactSpec` for the
same `A` must compute the same `L` and `U` as GEPP.  This theorem does not
assert that those row-reversal traces have already been constructed. -/
theorem higham_problem9_14_PrePivotedGEPP_lu_unique {n : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hLU₁ : LUFactSpec n A L₁ U₁)
    (hLU₂ : LUFactSpec n A L₂ U₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  have hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    higham_problem9_14_PrePivotedGEPP_det_ne_zero hpre
  exact higham9_1_lu_unique_of_pivots_ne_zero hLU₁ hLU₂
    ((higham9_1_det_ne_zero_iff_pivots_ne_zero hLU₁).mp hdet)

/-- **Problem 9.14 / same-LU bridge**, packaged source-facing form: a
pre-pivoted GEPP trace produces exact LU factors, and every other exact LU
certificate for `A` has exactly those factors.  This is the reusable final
bridge for the §9.9 and pairwise-pivoting trace-equivalence targets. -/
theorem higham_problem9_14_PrePivotedGEPP_exists_unique_LUFactSpec {n : ℕ}
    {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        ∀ {L' U' : Fin n → Fin n → ℝ},
          LUFactSpec n A L' U' → L' = L ∧ U' = U := by
  obtain ⟨L, U, hLU⟩ :=
    higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec hpre
  refine ⟨L, U, hLU, ?_⟩
  intro L' U' hLU'
  exact higham_problem9_14_PrePivotedGEPP_lu_unique hpre hLU' hLU

/-- **Theorem 9.7 / trace bookkeeping**, the explicit stage counter in a
no-interchange partial-pivoting trace is only an index of the surrounding
algorithmic stage.  The same active-matrix trace can be reindexed to any
starting counter. -/
theorem higham9_7_PartialPivotNoInterchangeTrace_reindex_time :
    ∀ {t s n : ℕ} {A : Fin n → Fin n → ℝ},
      higham9_7_PartialPivotNoInterchangeTrace t n A →
        higham9_7_PartialPivotNoInterchangeTrace s n A := by
  intro t s n
  induction n generalizing t s with
  | zero =>
      intro A _htrace
      exact higham9_7_PartialPivotNoInterchangeTrace.done
  | succ m ih =>
      intro A htrace
      cases htrace with
      | step hchoice hpivot hnext =>
          exact higham9_7_PartialPivotNoInterchangeTrace.step
            hchoice hpivot (ih (s := s + 1) hnext)

/-- **Problem 9.14 / recursive handoff**, a nonempty pre-pivoted GEPP trace
passes the same no-interchange property to the first Schur complement.  This
is the recursion gate used by the row-reversal/pairwise-pivoting bridge. -/
theorem higham_problem9_14_PrePivotedGEPP_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    higham_problem9_14_PrePivotedGEPP (luFirstSchurComplement A) := by
  cases hpre with
  | step _hchoice _hpivot hnext =>
      exact higham9_7_PartialPivotNoInterchangeTrace_reindex_time hnext

/-- **Problem 9.14**, the row-reversal permutation `i ↦ n-1-i` used in the
source matrix `Π A`, where `Π = I(n:-1:1,:)`. -/
def higham_problem9_14_rowReversal {n : ℕ} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hle : n - 1 - i.val ≤ n - 1 := Nat.sub_le (n - 1) i.val
    have hlt : n - 1 < n := Nat.sub_lt hn (by decide : 0 < 1)
    exact lt_of_le_of_lt hle hlt⟩

/-- **Problem 9.14**, row reversal is an involution. -/
theorem higham_problem9_14_rowReversal_involutive {n : ℕ} (i : Fin n) :
    higham_problem9_14_rowReversal (higham_problem9_14_rowReversal i) = i := by
  ext
  simp [higham_problem9_14_rowReversal]
  omega

/-- **Problem 9.14**, the row reversal is a permutation of the row index type. -/
theorem higham_problem9_14_rowReversal_isPermutation {n : ℕ} :
    Function.Bijective (higham_problem9_14_rowReversal (n := n)) := by
  constructor
  · intro x y hxy
    have h := congrArg (higham_problem9_14_rowReversal (n := n)) hxy
    simpa [higham_problem9_14_rowReversal_involutive x,
      higham_problem9_14_rowReversal_involutive y] using h
  · intro y
    exact ⟨higham_problem9_14_rowReversal y,
      higham_problem9_14_rowReversal_involutive y⟩

/-- **Problem 9.14**, row reversal sends the first row to the last row. -/
theorem higham_problem9_14_rowReversal_zero_eq_last {n : ℕ} (hn : 0 < n) :
    higham_problem9_14_rowReversal (⟨0, hn⟩ : Fin n) =
      ⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩ := by
  ext
  simp [higham_problem9_14_rowReversal]

/-- **Problem 9.14**, row reversal sends the last row to the first row. -/
theorem higham_problem9_14_rowReversal_last_eq_zero {n : ℕ} (hn : 0 < n) :
    higham_problem9_14_rowReversal
        (⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩ : Fin n) =
      ⟨0, hn⟩ := by
  ext
  simp [higham_problem9_14_rowReversal]

/-- **Problem 9.14**, the source row-reversed matrix `Π A`. -/
def higham_problem9_14_rowReversedMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  higham9_2_rowPermutedMatrix A higham_problem9_14_rowReversal

/-- **Problem 9.14**, applying the source row reversal twice returns the
original matrix. -/
theorem higham_problem9_14_rowReversedMatrix_involutive {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    higham_problem9_14_rowReversedMatrix
        (higham_problem9_14_rowReversedMatrix A) = A := by
  funext i j
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_rowReversal_involutive]

/-- **Problem 9.14**, row reversal preserves nonsingularity of the source
matrix.  This is the determinant side condition needed before running the
§9.9 row-reversal or pairwise-pivoting traces on `Π A`. -/
theorem higham_problem9_14_rowReversedMatrix_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_rowReversedMatrix A) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  let e : Equiv.Perm (Fin n) :=
    Equiv.ofBijective higham_problem9_14_rowReversal
      higham_problem9_14_rowReversal_isPermutation
  have hdet_eq :
      Matrix.det
        (Matrix.of (higham_problem9_14_rowReversedMatrix A) :
          Matrix (Fin n) (Fin n) ℝ) =
        ((Equiv.Perm.sign e : ℤ) : ℝ) *
          Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
    have hperm :=
      Matrix.det_permute (R := ℝ) e
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
    simpa [e, higham_problem9_14_rowReversedMatrix,
      higham9_2_rowPermutedMatrix, Matrix.of_apply] using hperm
  rw [hdet_eq]
  have hsign : ((Equiv.Perm.sign e : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs]
  exact mul_ne_zero hsign hdet

/-- **Problem 9.14**, if the original first row is a valid first partial pivot,
then the last row of the row-reversed matrix is a valid first partial pivot.
This is the first-column pivot fact needed by the §9.9 row-reversal and
pairwise-pivoting routes applied to `Π A`. -/
theorem higham_problem9_14_rowReversedMatrix_firstColumn_partialPivotChoice_last
    {n : ℕ} (hn : 0 < n) {A : Fin n → Fin n → ℝ}
    (hchoice :
      higham9_1_partialPivotChoice A (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)) :
    higham9_1_partialPivotChoice
      (higham_problem9_14_rowReversedMatrix A) (⟨0, hn⟩ : Fin n)
      (⟨n - 1, Nat.sub_lt hn (by decide : 0 < 1)⟩ : Fin n) := by
  constructor
  · exact Nat.zero_le _
  · intro i _hi
    have hbase := hchoice.2 (higham_problem9_14_rowReversal i) (Nat.zero_le _)
    simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_rowReversal_last_eq_zero hn] using hbase

/-- **Problem 9.14**, source-facing first-column consequence of pre-pivoting:
for a nonempty pre-pivoted input `A`, the row-reversed matrix `Π A` has its
first-column partial-pivot maximum in the last row, and that pivot is nonzero.
This does not prove the still-open §9.9 or pairwise-pivoting trace equivalence;
it records the first pivot fact those traces need. -/
theorem higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    higham9_1_partialPivotChoice
        (higham_problem9_14_rowReversedMatrix A) 0
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∧
      higham_problem9_14_rowReversedMatrix A
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0 ≠ 0 := by
  cases hpre with
  | step hchoice hpivot _hnext =>
      have hchoice₀ :
          higham9_1_partialPivotChoice A
            (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))
            (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) := by
        simpa using hchoice
      constructor
      · simpa using
          higham_problem9_14_rowReversedMatrix_firstColumn_partialPivotChoice_last
            (n := m + 1) (Nat.succ_pos m) (A := A) hchoice₀
      · have hlast :
            higham_problem9_14_rowReversal
                (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
              (0 : Fin (m + 1)) := by
          ext
          simp [higham_problem9_14_rowReversal]
        simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
          hlast] using hpivot

/-- **Problem 9.14 / pairwise pivoting**, two rows are adjacent when their
zero-based row indices differ by one.  This records the source restriction that
pairwise elimination uses only adjacent-row interchanges and operations. -/
def higham_problem9_14_adjacentRows {n : ℕ} (p q : Fin n) : Prop :=
  p.val + 1 = q.val ∨ q.val + 1 = p.val

/-- **Problem 9.14 / pairwise pivoting**, the adjacent-row schedule used to
bubble the final row of `ΠA` upward: at step `t`, the carried pivot row is at
zero-based row index `m - t` in an `(m+1)`-by-`(m+1)` matrix.  The definition
is total by saturating at row zero for `t > m`; the source trace uses only
steps `t < m`. -/
def higham_problem9_14_pairwiseBubbleRow {m : ℕ} (t : ℕ) : Fin (m + 1) :=
  ⟨m - t, Nat.lt_succ_of_le (Nat.sub_le m t)⟩

/-- **Problem 9.14 / pairwise pivoting**, the bubble schedule starts at the
last row of the row-reversed matrix. -/
@[simp] theorem higham_problem9_14_pairwiseBubbleRow_zero {m : ℕ} :
    higham_problem9_14_pairwiseBubbleRow (m := m) 0 =
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
  ext
  simp [higham_problem9_14_pairwiseBubbleRow]

/-- **Problem 9.14 / pairwise pivoting**, consecutive source bubble rows are
adjacent for every genuine step `t < m`. -/
theorem higham_problem9_14_pairwiseBubbleRows_adjacent {m t : ℕ}
    (ht : t < m) :
    higham_problem9_14_adjacentRows
      (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
      (higham_problem9_14_pairwiseBubbleRow (m := m) t) := by
  left
  simp [higham_problem9_14_pairwiseBubbleRow]
  omega

/-- **Problem 9.14 / pairwise pivoting**, consecutive source bubble rows are
distinct for every genuine step `t < m`. -/
theorem higham_problem9_14_pairwiseBubbleRows_distinct {m t : ℕ}
    (ht : t < m) :
    higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1) ≠
      higham_problem9_14_pairwiseBubbleRow (m := m) t := by
  intro h
  have hval := congrArg Fin.val h
  simp [higham_problem9_14_pairwiseBubbleRow] at hval
  omega

/-- **Problem 9.14 / pairwise pivoting**, consecutive source bubble rows move
strictly upward through the row-reversed matrix for every genuine step. -/
theorem higham_problem9_14_pairwiseBubbleRow_succ_val_lt {m t : ℕ}
    (ht : t < m) :
    (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1)).val <
      (higham_problem9_14_pairwiseBubbleRow (m := m) t).val := by
  simp [higham_problem9_14_pairwiseBubbleRow]
  omega

/-- **Problem 9.14 / pairwise pivoting**, after the scheduled bubble has run
for `m` genuine steps in an `(m+1)`-by-`(m+1)` matrix, the carried row index is
row zero. -/
@[simp] theorem higham_problem9_14_pairwiseBubbleRow_self {m : ℕ} :
    higham_problem9_14_pairwiseBubbleRow (m := m) m = (0 : Fin (m + 1)) := by
  ext
  simp [higham_problem9_14_pairwiseBubbleRow]

/-- **Problem 9.14 / pairwise pivoting**, source row represented by an
already-eliminated row in the adjacent bubble.  Row `r = 1` stores the Schur
update of the original last row, row `r = 2` stores the next one, and so on.
The row-zero value is a harmless totalization; the theorem using this map only
applies it to rows strictly below the carried pivot. -/
def higham_problem9_14_pairwiseBubbleSourceRow {m : ℕ}
    (r : Fin (m + 1)) : Fin (m + 1) :=
  ⟨m - (r.val - 1), Nat.lt_succ_of_le (Nat.sub_le m (r.val - 1))⟩

/-- **Problem 9.14 / pairwise pivoting**, on a trailing row `i.succ`, the
source-row map agrees with row reversal of the first Schur-complement index. -/
theorem higham_problem9_14_pairwiseBubbleSourceRow_succ {m : ℕ}
    (i : Fin m) :
    higham_problem9_14_pairwiseBubbleSourceRow (m := m) i.succ =
      Fin.succ (higham_problem9_14_rowReversal i) := by
  ext
  simp [higham_problem9_14_pairwiseBubbleSourceRow,
    higham_problem9_14_rowReversal]
  omega

/-- **Problem 9.14 / pairwise pivoting**, the row interchange between the two
rows of a pair.  The source pairwise method restricts such swaps to adjacent
rows, recorded separately by `higham_problem9_14_adjacentRows`. -/
def higham_problem9_14_pairRowSwap {n : ℕ} (p q : Fin n) : Fin n → Fin n :=
  Equiv.swap p q

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap sends the left
row of the pair to the right row. -/
theorem higham_problem9_14_pairRowSwap_left {n : ℕ} (p q : Fin n) :
    higham_problem9_14_pairRowSwap p q p = q := by
  simp [higham_problem9_14_pairRowSwap]

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap sends the right
row of the pair to the left row. -/
theorem higham_problem9_14_pairRowSwap_right {n : ℕ} (p q : Fin n) :
    higham_problem9_14_pairRowSwap p q q = p := by
  simp [higham_problem9_14_pairRowSwap]

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap is an involution. -/
theorem higham_problem9_14_pairRowSwap_involutive {n : ℕ} (p q : Fin n) :
    Function.Involutive (higham_problem9_14_pairRowSwap p q) := by
  intro i
  simp [higham_problem9_14_pairRowSwap]

/-- **Problem 9.14 / pairwise pivoting**, the pair row swap is a permutation of
the row index type. -/
theorem higham_problem9_14_pairRowSwap_isPermutation {n : ℕ} (p q : Fin n) :
    Function.Bijective (higham_problem9_14_pairRowSwap p q) :=
  (Equiv.swap p q).bijective

/-- **Problem 9.14 / pairwise pivoting**, a pair row swap preserves
nonsingularity.  This is the determinant side condition needed for adjacent
row interchanges in a pairwise-pivoting trace. -/
theorem higham_problem9_14_pairRowSwap_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p q : Fin n)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_2_rowPermutedMatrix A
        (higham_problem9_14_pairRowSwap p q)) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  classical
  let e : Equiv.Perm (Fin n) := Equiv.swap p q
  have hdet_eq :
      Matrix.det
        (Matrix.of (higham9_2_rowPermutedMatrix A
          (higham_problem9_14_pairRowSwap p q)) :
          Matrix (Fin n) (Fin n) ℝ) =
        ((Equiv.Perm.sign e : ℤ) : ℝ) *
          Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
    have hperm :=
      Matrix.det_permute (R := ℝ) e
        (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
    simpa [e, higham_problem9_14_pairRowSwap, higham9_2_rowPermutedMatrix,
      Matrix.of_apply] using hperm
  rw [hdet_eq]
  have hsign : ((Equiv.Perm.sign e : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs]
  exact mul_ne_zero hsign hdet

/-- **Problem 9.14 / pairwise pivoting**, the natural two-row pivoting choice:
from rows `p` and `q`, choose one of them whose active-column entry has maximal
absolute value among the pair. -/
def higham_problem9_14_pairPivotChoice {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q r : Fin n) : Prop :=
  (r = p ∨ r = q) ∧ |A p k| ≤ |A r k| ∧ |A q k| ≤ |A r k|

/-- **Problem 9.14 / pairwise pivoting**, the natural two-row pivot choice
exists for every pair of candidate rows. -/
theorem higham_problem9_14_exists_pairPivotChoice {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    ∃ r : Fin n, higham_problem9_14_pairPivotChoice A k p q r := by
  by_cases hpq : |A p k| ≤ |A q k|
  · exact ⟨q, Or.inr rfl, hpq, le_rfl⟩
  · have hqp : |A q k| ≤ |A p k| := le_of_lt (lt_of_not_ge hpq)
    exact ⟨p, Or.inl rfl, le_rfl, hqp⟩

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector: choose `q` if its active-column entry is at least as large as
that of `p`, and choose `p` otherwise. -/
noncomputable def higham_problem9_14_pairPivotRow {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) : Fin n :=
  if |A p k| ≤ |A q k| then q else p

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector satisfies the pairwise pivot-choice predicate. -/
theorem higham_problem9_14_pairPivotRow_choice {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    higham_problem9_14_pairPivotChoice A k p q
      (higham_problem9_14_pairPivotRow A k p q) := by
  unfold higham_problem9_14_pairPivotRow
  by_cases hpq : |A p k| ≤ |A q k|
  · simp [hpq, higham_problem9_14_pairPivotChoice]
  · have hqp : |A q k| ≤ |A p k| := le_of_lt (lt_of_not_ge hpq)
    simp [hpq, hqp, higham_problem9_14_pairPivotChoice]

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector chooses the right row when its active-column entry is at least
as large as the left row's entry. -/
theorem higham_problem9_14_pairPivotRow_eq_right_of_abs_le {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (h : |A p k| ≤ |A q k|) :
    higham_problem9_14_pairPivotRow A k p q = q := by
  simp [higham_problem9_14_pairPivotRow, h]

/-- **Problem 9.14 / pairwise pivoting**, the deterministic natural two-row
pivot selector chooses the left row when its active-column entry is strictly
larger than the right row's entry. -/
theorem higham_problem9_14_pairPivotRow_eq_left_of_abs_gt {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (h : |A q k| < |A p k|) :
    higham_problem9_14_pairPivotRow A k p q = p := by
  have hpq : ¬ |A p k| ≤ |A q k| := not_le.mpr h
  simp [higham_problem9_14_pairPivotRow, hpq]

/-- **Problem 9.14 / pairwise pivoting**, when the right row is a first-column
partial-pivot maximum, the deterministic natural pairwise rule selects it
against any left row.  The right-favoring tie break matches the local
source-facing convention used for the §9.9 row-reversal route. -/
theorem higham_problem9_14_pairPivotRow_eq_right_of_firstColumn_partialPivotChoice
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    {p q : Fin (m + 1)}
    (hchoice : higham9_1_partialPivotChoice A 0 q) :
    higham_problem9_14_pairPivotRow A 0 p q = q := by
  exact higham_problem9_14_pairPivotRow_eq_right_of_abs_le A
    (hchoice.2 p (Nat.zero_le _))

/-- **Problem 9.14**, for a pre-pivoted input `A`, the first-column natural
pairwise rule on the row-reversed matrix `Π A` selects the last row whenever
that last row is the right member of the compared pair.  This is a local
deterministic-selector dependency for the still-open §9.9/pairwise trace
equivalence. -/
theorem higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (p : Fin (m + 1)) :
    higham_problem9_14_pairPivotRow
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
  exact
    higham_problem9_14_pairPivotRow_eq_right_of_firstColumn_partialPivotChoice
      (higham_problem9_14_rowReversedMatrix A)
      (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
        hpre).1

/-- **Problem 9.14 / pairwise pivoting**, row permutation that moves the
deterministically chosen pair pivot into the left member `p` of the pair.  If
the left row is already chosen, it is the identity; otherwise it swaps the two
pair rows. -/
noncomputable def higham_problem9_14_pairPivotToLeftSwap {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) : Fin n → Fin n :=
  if higham_problem9_14_pairPivotRow A k p q = p then id
  else higham_problem9_14_pairRowSwap p q

/-- **Problem 9.14 / pairwise pivoting**, after the pair pivot-to-left swap,
the left row maps to the deterministic pair pivot row. -/
theorem higham_problem9_14_pairPivotToLeftSwap_left {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    higham_problem9_14_pairPivotToLeftSwap A k p q p =
    higham_problem9_14_pairPivotRow A k p q := by
  unfold higham_problem9_14_pairPivotToLeftSwap
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · simp [hp]
  · have hq : higham_problem9_14_pairPivotRow A k p q = q := by
      rcases (higham_problem9_14_pairPivotRow_choice A k p q).1 with hleft | hright
      · exact (hp hleft).elim
      · exact hright
    by_cases hqp : q = p
    · exact (hp (hq.trans hqp)).elim
    · simp [hq, hqp, higham_problem9_14_pairRowSwap_left]

/-- **Problem 9.14 / pairwise pivoting**, the pivot-to-left row map is a
permutation of the row index type. -/
theorem higham_problem9_14_pairPivotToLeftSwap_isPermutation {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    Function.Bijective
      (higham_problem9_14_pairPivotToLeftSwap A k p q) := by
  unfold higham_problem9_14_pairPivotToLeftSwap
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · simp [hp]
  · simpa [hp] using higham_problem9_14_pairRowSwap_isPermutation p q

/-- **Problem 9.14 / pairwise pivoting**, the pair-pivoted two-row matrix:
rows are permuted so that the deterministic pivot of the pair occupies the
left row. -/
noncomputable def higham_problem9_14_pairPivotToLeftMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    Fin n → Fin n → ℝ :=
  higham9_2_rowPermutedMatrix A
    (higham_problem9_14_pairPivotToLeftSwap A k p q)

/-- **Problem 9.14 / pairwise pivoting**, in the pair-pivoted matrix, the left
row is exactly the deterministically chosen pair pivot row of the original
matrix. -/
theorem higham_problem9_14_pairPivotToLeftMatrix_left {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q j : Fin n) :
    higham_problem9_14_pairPivotToLeftMatrix A k p q p j =
      A (higham_problem9_14_pairPivotRow A k p q) j := by
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap_left]

/-- **Problem 9.14 / pairwise pivoting**, pair pivot-to-left row permutation
preserves nonsingularity. -/
theorem higham_problem9_14_pairPivotToLeftMatrix_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_pairPivotToLeftMatrix A k p q) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  unfold higham_problem9_14_pairPivotToLeftMatrix
  unfold higham_problem9_14_pairPivotToLeftSwap
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · simpa [hp, higham9_2_rowPermutedMatrix] using hdet
  · simpa [hp] using higham_problem9_14_pairRowSwap_det_ne_zero A p q hdet

/-- **Problem 9.14 / pairwise pivoting**, the natural two-row pivot rule bounds
the multiplier for either row in the pair by one, provided the chosen pivot is
nonzero. -/
theorem higham_problem9_14_pairPivotChoice_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q r i : Fin n}
    (hchoice : higham_problem9_14_pairPivotChoice A k p q r)
    (hpivot : A r k ≠ 0) (hi : i = p ∨ i = q) :
    |A i k / A r k| ≤ 1 := by
  have hbound : |A i k| ≤ |A r k| := by
    rcases hi with rfl | rfl
    · exact hchoice.2.1
    · exact hchoice.2.2
  have hpiv_abs_pos : 0 < |A r k| := abs_pos.mpr hpivot
  rw [abs_div]
  rw [div_le_iff₀ hpiv_abs_pos]
  simpa using hbound

/-- **Problem 9.14 / pairwise pivoting**, left-row multiplier bound for the
natural two-row pivot rule. -/
theorem higham_problem9_14_pairPivotChoice_left_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q r : Fin n}
    (hchoice : higham_problem9_14_pairPivotChoice A k p q r)
    (hpivot : A r k ≠ 0) :
    |A p k / A r k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_multiplier_abs_le_one hchoice hpivot
    (Or.inl rfl)

/-- **Problem 9.14 / pairwise pivoting**, right-row multiplier bound for the
natural two-row pivot rule. -/
theorem higham_problem9_14_pairPivotChoice_right_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q r : Fin n}
    (hchoice : higham_problem9_14_pairPivotChoice A k p q r)
    (hpivot : A r k ≠ 0) :
    |A q k / A r k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_multiplier_abs_le_one hchoice hpivot
    (Or.inr rfl)

/-- **Problem 9.14 / pairwise pivoting**, left-row multiplier bound for the
deterministic natural two-row pivot selector. -/
theorem higham_problem9_14_pairPivotRow_left_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q : Fin n}
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    |A p k / A (higham_problem9_14_pairPivotRow A k p q) k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_left_multiplier_abs_le_one
    (higham_problem9_14_pairPivotRow_choice A k p q) hpivot

/-- **Problem 9.14 / pairwise pivoting**, right-row multiplier bound for the
deterministic natural two-row pivot selector. -/
theorem higham_problem9_14_pairPivotRow_right_multiplier_abs_le_one {n : ℕ}
    {A : Fin n → Fin n → ℝ} {k p q : Fin n}
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    |A q k / A (higham_problem9_14_pairPivotRow A k p q) k| ≤ 1 :=
  higham_problem9_14_pairPivotChoice_right_multiplier_abs_le_one
    (higham_problem9_14_pairPivotRow_choice A k p q) hpivot

/-- **Problem 9.14 / pairwise pivoting**, the exact row operation that zeros
the active-column entry of `target` using `pivot`.  This is the local
element-zeroing primitive for pairwise elimination; the pair/adjacency and
pivot-choice hypotheses are supplied by the trace that uses it. -/
noncomputable def higham_problem9_14_pairEliminateRow {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot target : Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = target then
      A target j - (A target k / A pivot k) * A pivot j
    else
      A i j

/-- **Problem 9.14 / pairwise pivoting**, the eliminated target row has the
expected row-operation formula. -/
theorem higham_problem9_14_pairEliminateRow_target {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot target j : Fin n) :
    higham_problem9_14_pairEliminateRow A k pivot target target j =
      A target j - (A target k / A pivot k) * A pivot j := by
  simp [higham_problem9_14_pairEliminateRow]

/-- **Problem 9.14 / pairwise pivoting**, rows other than the eliminated target
are unchanged by the pairwise row operation. -/
theorem higham_problem9_14_pairEliminateRow_of_ne {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target i j : Fin n}
    (hi : i ≠ target) :
    higham_problem9_14_pairEliminateRow A k pivot target i j = A i j := by
  simp [higham_problem9_14_pairEliminateRow, hi]

/-- **Problem 9.14 / pairwise pivoting**, the pivot row is unchanged when it is
distinct from the target row. -/
theorem higham_problem9_14_pairEliminateRow_pivot {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target j : Fin n}
    (hpt : pivot ≠ target) :
    higham_problem9_14_pairEliminateRow A k pivot target pivot j =
      A pivot j :=
  higham_problem9_14_pairEliminateRow_of_ne A hpt

/-- **Problem 9.14 / pairwise pivoting**, the pairwise row operation zeros the
target's active-column entry when the chosen pivot is nonzero. -/
theorem higham_problem9_14_pairEliminateRow_target_active_eq_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target : Fin n}
    (hpivot : A pivot k ≠ 0) :
    higham_problem9_14_pairEliminateRow A k pivot target target k = 0 := by
  simp [higham_problem9_14_pairEliminateRow]
  field_simp [hpivot]
  ring

/-- **Problem 9.14 / pairwise pivoting**, the pairwise row operation is the
standard determinant-preserving row update: replace `target` by itself plus a
multiple of the distinct pivot row. -/
theorem higham_problem9_14_pairEliminateRow_eq_updateRow_add_smul {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot target : Fin n) :
    (Matrix.of (higham_problem9_14_pairEliminateRow A k pivot target) :
        Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).updateRow target
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ) target +
          (-(A target k / A pivot k)) •
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) pivot) := by
  ext i j
  by_cases hi : i = target
  · subst hi
    simp [higham_problem9_14_pairEliminateRow, sub_eq_add_neg]
  · simp [higham_problem9_14_pairEliminateRow, Matrix.updateRow_apply, hi]

/-- **Problem 9.14 / pairwise pivoting**, the exact pairwise elimination row
operation preserves the determinant when pivot and target rows are distinct. -/
theorem higham_problem9_14_pairEliminateRow_det_eq {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target : Fin n}
    (hpt : target ≠ pivot) :
    Matrix.det
        (Matrix.of (higham_problem9_14_pairEliminateRow A k pivot target) :
          Matrix (Fin n) (Fin n) ℝ) =
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  rw [higham_problem9_14_pairEliminateRow_eq_updateRow_add_smul]
  exact Matrix.det_updateRow_add_smul_self
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) hpt
    (-(A target k / A pivot k))

/-- **Problem 9.14 / pairwise pivoting**, a pairwise elimination row operation
preserves nonsingularity when pivot and target rows are distinct. -/
theorem higham_problem9_14_pairEliminateRow_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k pivot target : Fin n}
    (hpt : target ≠ pivot)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
        (Matrix.of (higham_problem9_14_pairEliminateRow A k pivot target) :
          Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  simpa [higham_problem9_14_pairEliminateRow_det_eq A hpt] using hdet

/-- **Problem 9.14 / first §9.9 method**, the zero-based target row for the
first method in §9.9.  At first-stage step `t`, the source method zeros row
`t+1`, corresponding to book rows `2,3,...,n`.  The definition is totalized
with `min` outside the meaningful range `t < m`. -/
def higham_problem9_14_firstMethodTarget {m : ℕ} (t : ℕ) : Fin (m + 1) :=
  ⟨min (t + 1) m, Nat.lt_succ_of_le (Nat.min_le_right (t + 1) m)⟩

/-- **Problem 9.14 / first §9.9 method**, target-row value in the meaningful
range of the first-stage source schedule. -/
@[simp] theorem higham_problem9_14_firstMethodTarget_val {m t : ℕ}
    (ht : t < m) :
    (higham_problem9_14_firstMethodTarget (m := m) t).val = t + 1 := by
  have hle : t + 1 ≤ m := Nat.succ_le_iff.mpr ht
  simp [higham_problem9_14_firstMethodTarget, Nat.min_eq_left hle]

/-- **Problem 9.14 / first §9.9 method**, a genuine first-method target row is
not the pivot row. -/
theorem higham_problem9_14_firstMethodTarget_ne_zero {m t : ℕ}
    (ht : t < m) :
    higham_problem9_14_firstMethodTarget (m := m) t ≠
      (0 : Fin (m + 1)) := by
  intro h
  have hval := congrArg Fin.val h
  rw [higham_problem9_14_firstMethodTarget_val ht] at hval
  simp at hval

/-- **Problem 9.14 / first §9.9 method**, recursive exact first-stage matrix
state for the first method described in §9.9, applied to the original
pre-pivoted matrix `A`.  Step `t+1` zeros the first-column entry in row `t+1`
using row zero.  Under the pre-pivoted hypothesis, no row interchange is
needed, and the multiplier bound is proved below. -/
noncomputable def higham_problem9_14_firstMethodMatrix {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → Fin (m + 1) → Fin (m + 1) → ℝ
  | 0 => A
  | t + 1 =>
      higham_problem9_14_pairEliminateRow
        (higham_problem9_14_firstMethodMatrix A t) 0 0
        (higham_problem9_14_firstMethodTarget (m := m) t)

/-- **Problem 9.14 / first §9.9 method**, the first-method matrix starts from
the original matrix `A`. -/
@[simp] theorem higham_problem9_14_firstMethodMatrix_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_firstMethodMatrix A 0 = A := rfl

/-- **Problem 9.14 / first §9.9 method**, unfolding one scheduled first-method
row-zeroing step. -/
theorem higham_problem9_14_firstMethodMatrix_succ {m t : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_firstMethodMatrix A (t + 1) =
      higham_problem9_14_pairEliminateRow
        (higham_problem9_14_firstMethodMatrix A t) 0 0
        (higham_problem9_14_firstMethodTarget (m := m) t) := rfl

/-- **Problem 9.14 / first §9.9 method**, source-facing trace predicate for
the first §9.9 method.  The initial state is `A`; each genuine first-stage
step zeros the next row `2,3,...,n` using row zero.  The multiplier-bounded
property for pre-pivoted inputs is proved separately instead of being assumed
as a trace field. -/
inductive higham_problem9_14_FirstMethodTrace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → (Fin (m + 1) → Fin (m + 1) → ℝ) → Prop
  | init :
      higham_problem9_14_FirstMethodTrace A 0 A
  | step {t : ℕ} {B : Fin (m + 1) → Fin (m + 1) → ℝ}
      (ht : t < m)
      (htrace : higham_problem9_14_FirstMethodTrace A t B) :
      higham_problem9_14_FirstMethodTrace A (t + 1)
        (higham_problem9_14_pairEliminateRow B 0 0
          (higham_problem9_14_firstMethodTarget (m := m) t))

/-- **Problem 9.14 / first §9.9 method**, the recursive first-method matrix is
a valid source-facing trace at every prefix `t <= m`. -/
theorem higham_problem9_14_firstMethodMatrix_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∀ t : ℕ, t ≤ m →
      higham_problem9_14_FirstMethodTrace A t
        (higham_problem9_14_firstMethodMatrix A t) := by
  intro t
  induction t with
  | zero =>
      intro _ht
      exact higham_problem9_14_FirstMethodTrace.init
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      simpa [higham_problem9_14_firstMethodMatrix_succ] using
        higham_problem9_14_FirstMethodTrace.step ht (ih ht_le)

/-- **Problem 9.14 / first §9.9 method**, terminal trace for the first-stage
schedule. -/
theorem higham_problem9_14_firstMethodMatrix_terminal_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_FirstMethodTrace A m
      (higham_problem9_14_firstMethodMatrix A m) :=
  higham_problem9_14_firstMethodMatrix_trace A m le_rfl

/-- **Problem 9.14 / first §9.9 method**, every scheduled first-method prefix
preserves nonsingularity. -/
theorem higham_problem9_14_firstMethodMatrix_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet : Matrix.det
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∀ t : ℕ, t ≤ m →
      Matrix.det
        (Matrix.of (higham_problem9_14_firstMethodMatrix A t) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  intro t
  induction t with
  | zero =>
      intro _ht
      simpa [higham_problem9_14_firstMethodMatrix_zero] using hdet
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      have htarget :
          higham_problem9_14_firstMethodTarget (m := m) t ≠
            (0 : Fin (m + 1)) :=
        higham_problem9_14_firstMethodTarget_ne_zero (m := m) (t := t) ht
      simpa [higham_problem9_14_firstMethodMatrix_succ] using
        higham_problem9_14_pairEliminateRow_det_ne_zero
          (A := higham_problem9_14_firstMethodMatrix A t)
          (k := 0) (pivot := (0 : Fin (m + 1)))
          (target := higham_problem9_14_firstMethodTarget (m := m) t)
          htarget (ih ht_le)

/-- **Problem 9.14 / first §9.9 method**, prefix invariant for a pre-pivoted
input.  After `t` first-method steps, row zero is still the original first row
of `A`; rows `1..t` are exactly their first-column Schur updates by row zero;
rows below the prefix are unchanged and remain dominated by row zero in the
active column. -/
theorem higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      (∀ j : Fin (m + 1),
        higham_problem9_14_firstMethodMatrix A t 0 j = A 0 j) ∧
      higham_problem9_14_firstMethodMatrix A t 0 0 ≠ 0 ∧
      (∀ r : Fin (m + 1), 0 < r.val → r.val ≤ t →
        ∀ j : Fin (m + 1),
          higham_problem9_14_firstMethodMatrix A t r j =
            A r j - (A r 0 / A 0 0) * A 0 j) ∧
      (∀ r : Fin (m + 1), t < r.val →
        ∀ j : Fin (m + 1),
          higham_problem9_14_firstMethodMatrix A t r j = A r j) ∧
      (∀ r : Fin (m + 1), t < r.val →
        |higham_problem9_14_firstMethodMatrix A t r 0| ≤
          |higham_problem9_14_firstMethodMatrix A t 0 0|) := by
  have hchoiceA : higham9_1_partialPivotChoice A 0 0 := by
    cases hpre with
    | step hchoice _hpivot _hnext =>
        simpa using hchoice
  have hpivA : A 0 0 ≠ 0 := by
    cases hpre with
    | step _hchoice hpivot _hnext =>
        exact hpivot
  intro t
  induction t with
  | zero =>
      intro _ht
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        simp [higham_problem9_14_firstMethodMatrix_zero]
      · simpa [higham_problem9_14_firstMethodMatrix_zero] using hpivA
      · intro r _hrpos hrle _j
        omega
      · intro r _hr j
        simp [higham_problem9_14_firstMethodMatrix_zero]
      · intro r _hr
        simpa [higham_problem9_14_firstMethodMatrix_zero] using
          hchoiceA.2 r (Nat.zero_le _)
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      rcases ih ht_le with
        ⟨hpivotRow, hpivot_ne, helim, hunchanged, _hdom⟩
      let q : Fin (m + 1) :=
        higham_problem9_14_firstMethodTarget (m := m) t
      have hqval : q.val = t + 1 := by
        simpa [q] using
          higham_problem9_14_firstMethodTarget_val (m := m) (t := t) ht
      have hq_ne_zero : q ≠ (0 : Fin (m + 1)) := by
        simpa [q] using
          higham_problem9_14_firstMethodTarget_ne_zero (m := m) (t := t) ht
      have hzero_ne_q : (0 : Fin (m + 1)) ≠ q := Ne.symm hq_ne_zero
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        rw [higham_problem9_14_firstMethodMatrix_succ]
        have hrow :=
          higham_problem9_14_pairEliminateRow_pivot
            (A := higham_problem9_14_firstMethodMatrix A t)
            (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
            (j := j) hzero_ne_q
        simpa [q] using hrow.trans (hpivotRow j)
      · rw [higham_problem9_14_firstMethodMatrix_succ]
        have hrow :=
          higham_problem9_14_pairEliminateRow_pivot
            (A := higham_problem9_14_firstMethodMatrix A t)
            (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
            (j := (0 : Fin (m + 1))) hzero_ne_q
        simpa [q, hrow] using hpivot_ne
      · intro r hrpos hrle j
        by_cases hrq : r = q
        · subst r
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have htarget :=
            higham_problem9_14_pairEliminateRow_target
              (higham_problem9_14_firstMethodMatrix A t)
              (0 : Fin (m + 1)) (0 : Fin (m + 1)) q j
          rw [htarget]
          have hq_old :
              higham_problem9_14_firstMethodMatrix A t q j = A q j :=
            hunchanged q (by omega) j
          have hq_active :
              higham_problem9_14_firstMethodMatrix A t q 0 = A q 0 :=
            hunchanged q (by omega) 0
          rw [hq_old, hq_active, hpivotRow j, hpivotRow (0 : Fin (m + 1))]
        · have hr_val_ne : r.val ≠ t + 1 := by
            intro hv
            exact hrq (Fin.ext (by rw [hv, hqval]))
          have hrle_t : r.val ≤ t := by omega
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have hsame :=
            higham_problem9_14_pairEliminateRow_of_ne
              (A := higham_problem9_14_firstMethodMatrix A t)
              (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
              (i := r) (j := j) hrq
          rw [hsame]
          exact helim r hrpos hrle_t j
      · intro r hr j
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          omega
        rw [higham_problem9_14_firstMethodMatrix_succ]
        have hsame :=
          higham_problem9_14_pairEliminateRow_of_ne
            (A := higham_problem9_14_firstMethodMatrix A t)
            (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
            (i := r) (j := j) hrq
        rw [hsame]
        exact hunchanged r (by omega) j
      · intro r hr
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          omega
        have hr_step :
            higham_problem9_14_firstMethodMatrix A (t + 1) r
                (0 : Fin (m + 1)) =
              A r 0 := by
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have hsame :=
            higham_problem9_14_pairEliminateRow_of_ne
              (A := higham_problem9_14_firstMethodMatrix A t)
              (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
              (i := r) (j := (0 : Fin (m + 1))) hrq
          rw [hsame]
          exact hunchanged r (by omega) 0
        have hp_step :
            higham_problem9_14_firstMethodMatrix A (t + 1) 0
                (0 : Fin (m + 1)) =
              A 0 0 := by
          rw [higham_problem9_14_firstMethodMatrix_succ]
          have hrow :=
            higham_problem9_14_pairEliminateRow_pivot
              (A := higham_problem9_14_firstMethodMatrix A t)
              (k := 0) (pivot := (0 : Fin (m + 1))) (target := q)
              (j := (0 : Fin (m + 1))) hzero_ne_q
          simpa [q] using hrow.trans (hpivotRow (0 : Fin (m + 1)))
        calc
          |higham_problem9_14_firstMethodMatrix A (t + 1) r
              (0 : Fin (m + 1))|
              = |A r 0| := by rw [hr_step]
          _ ≤ |A 0 0| := hchoiceA.2 r (Nat.zero_le _)
          _ = |higham_problem9_14_firstMethodMatrix A (t + 1) 0
              (0 : Fin (m + 1))| := by rw [hp_step]

/-- **Problem 9.14 / first §9.9 method**, the multipliers used by the first
method on a pre-pivoted input are bounded by one at every first-stage step. -/
theorem higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_multiplier_abs_le_one
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) {t : ℕ} (ht : t < m) :
    |higham_problem9_14_firstMethodMatrix A t
        (higham_problem9_14_firstMethodTarget (m := m) t) 0 /
      higham_problem9_14_firstMethodMatrix A t 0 0| ≤ 1 := by
  have hinv :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
      (A := A) hpre t (Nat.le_of_lt ht)
  have hqval :
      (higham_problem9_14_firstMethodTarget (m := m) t).val = t + 1 :=
    higham_problem9_14_firstMethodTarget_val (m := m) (t := t) ht
  have hdom :=
    hinv.2.2.2.2
      (higham_problem9_14_firstMethodTarget (m := m) t)
      (by omega)
  have hpiv_abs : 0 < |higham_problem9_14_firstMethodMatrix A t 0 0| :=
    abs_pos.mpr hinv.2.1
  rw [abs_div]
  rw [div_le_iff₀ hpiv_abs]
  simpa [mul_one] using hdom

/-- **Problem 9.14 / first §9.9 method**, terminal trailing block of the
first-method first stage is exactly the first Schur complement of `A`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_trailing_eq_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (i j : Fin m) :
    higham_problem9_14_firstMethodMatrix A m i.succ j.succ =
      luFirstSchurComplement A i j := by
  have hinv :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
      (A := A) hpre m le_rfl
  have hpos : 0 < (i.succ : Fin (m + 1)).val := by simp
  have hle : (i.succ : Fin (m + 1)).val ≤ m := by
    exact Nat.succ_le_iff.mpr i.isLt
  have hrow := hinv.2.2.1 i.succ hpos hle j.succ
  simpa [luFirstSchurComplement, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using hrow

/-- **Problem 9.14 / first §9.9 method**, terminal Schur-complement form:
after the first §9.9 method completes its first-stage row-zeroing schedule,
the first Schur complement of the terminal matrix is the first Schur
complement of the original pre-pivoted input. -/
theorem
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    luFirstSchurComplement (higham_problem9_14_firstMethodMatrix A m) =
      luFirstSchurComplement A := by
  funext i j
  unfold luFirstSchurComplement
  have htrail :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_trailing_eq_firstSchurComplement
      (A := A) hpre i j
  have hinv :=
    higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant
      (A := A) hpre m le_rfl
  have hpos : 0 < (i.succ : Fin (m + 1)).val := by simp
  have hle : (i.succ : Fin (m + 1)).val ≤ m := by
    exact Nat.succ_le_iff.mpr i.isLt
  have hzero_row := hinv.2.2.1 i.succ hpos hle (0 : Fin (m + 1))
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _hchoice hpivot _hnext =>
        exact hpivot
  have hzero :
      higham_problem9_14_firstMethodMatrix A m i.succ (0 : Fin (m + 1)) = 0 := by
    rw [hzero_row]
    field_simp [hpiv]
    ring
  rw [htrail, hzero]
  simp [luFirstSchurComplement, div_eq_mul_inv, mul_assoc]

/-- **Problem 9.14 / first §9.9 method**, recursive trace certificate for the
first method.  At each nonempty stage, the method runs the source first-stage
row-zeroing schedule on the current active matrix and recurses on the usual
first Schur complement. -/
inductive higham_problem9_14_RecursiveFirstMethodTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | done {A : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursiveFirstMethodTrace 0 A
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      (hstage :
        higham_problem9_14_FirstMethodTrace A m
          (higham_problem9_14_firstMethodMatrix A m))
      (hmult :
        ∀ t : ℕ, t < m →
          |higham_problem9_14_firstMethodMatrix A t
              (higham_problem9_14_firstMethodTarget (m := m) t) 0 /
            higham_problem9_14_firstMethodMatrix A t 0 0| ≤ 1)
      (hschur :
        luFirstSchurComplement (higham_problem9_14_firstMethodMatrix A m) =
          luFirstSchurComplement A)
      (hnext :
        higham_problem9_14_RecursiveFirstMethodTrace m
          (luFirstSchurComplement A)) :
      higham_problem9_14_RecursiveFirstMethodTrace (m + 1) A

/-- **Problem 9.14 / first §9.9 method**, every pre-pivoted GEPP input admits
the recursive first-method trace certificate. -/
theorem higham_problem9_14_RecursiveFirstMethodTrace_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        higham_problem9_14_RecursiveFirstMethodTrace n A := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact higham_problem9_14_RecursiveFirstMethodTrace.done
  | succ m ih =>
      intro A hpre
      exact higham_problem9_14_RecursiveFirstMethodTrace.step
        (higham_problem9_14_firstMethodMatrix_terminal_trace A)
        (fun t ht =>
          higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_multiplier_abs_le_one
            (A := A) hpre ht)
        (higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_firstSchurComplement
          (A := A) hpre)
        (ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre))

/-- **Problem 9.14 / first §9.9 method**, recursive LU certificate for the
first method.  The certificate records the first-stage trace, the proved
multiplier bounds, the terminal Schur-complement bridge, and the recursively
constructed factors for the next active matrix. -/
inductive higham_problem9_14_RecursiveFirstMethodLUFactSpec :
    (n : ℕ) → (Fin n → Fin n → ℝ) →
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A L U : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursiveFirstMethodLUFactSpec 0 A L U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {Lnext Unext : Fin m → Fin m → ℝ}
      (hpivot : A 0 0 ≠ 0)
      (hstage :
        higham_problem9_14_FirstMethodTrace A m
          (higham_problem9_14_firstMethodMatrix A m))
      (hmult :
        ∀ t : ℕ, t < m →
          |higham_problem9_14_firstMethodMatrix A t
              (higham_problem9_14_firstMethodTarget (m := m) t) 0 /
            higham_problem9_14_firstMethodMatrix A t 0 0| ≤ 1)
      (hschur :
        luFirstSchurComplement (higham_problem9_14_firstMethodMatrix A m) =
          luFirstSchurComplement A)
      (hnext :
        higham_problem9_14_RecursiveFirstMethodLUFactSpec m
          (luFirstSchurComplement A) Lnext Unext) :
      higham_problem9_14_RecursiveFirstMethodLUFactSpec (m + 1) A
        (luFirstStepL A Lnext) (luFirstStepU A Unext)

/-- **Problem 9.14 / first §9.9 method**, every recursive first-method LU
certificate is an ordinary exact LU certificate for the source matrix. -/
theorem higham_problem9_14_RecursiveFirstMethodLUFactSpec_to_LUFactSpec :
    ∀ {n : ℕ} {A L U : Fin n → Fin n → ℝ},
      higham_problem9_14_RecursiveFirstMethodLUFactSpec n A L U →
        LUFactSpec n A L U := by
  intro n A L U htrace
  induction htrace with
  | done =>
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step hpivot _hstage _hmult _hschur _hnext ih =>
      exact LUFactSpec.of_firstSchurComplement_explicit hpivot ih

/-- **Problem 9.14 / first §9.9 method**, existence of recursive first-method
LU factors for every pre-pivoted GEPP input. -/
theorem higham_problem9_14_exists_RecursiveFirstMethodLUFactSpec_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        ∃ L U : Fin n → Fin n → ℝ,
          higham_problem9_14_RecursiveFirstMethodLUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
        higham_problem9_14_RecursiveFirstMethodLUFactSpec.done⟩
  | succ m ih =>
      intro A hpre
      obtain ⟨Lnext, Unext, hnextLU⟩ :=
        ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre)
      have hpivot : A 0 0 ≠ 0 := by
        cases hpre with
        | step _hchoice hpivot _hnext =>
            exact hpivot
      exact
        ⟨luFirstStepL A Lnext, luFirstStepU A Unext,
          higham_problem9_14_RecursiveFirstMethodLUFactSpec.step
            hpivot
            (higham_problem9_14_firstMethodMatrix_terminal_trace A)
            (fun t ht =>
              higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_multiplier_abs_le_one
                (A := A) hpre ht)
            (higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_firstSchurComplement
              (A := A) hpre)
            hnextLU⟩

/-- **Problem 9.14 / same-LU bridge**, any recursive first-method LU
certificate for a pre-pivoted input has the same exact factors as any
GEPP/no-interchange exact LU certificate for that input. -/
theorem higham_problem9_14_RecursiveFirstMethodLUFactSpec_same_as_PrePivotedGEPP
    {n : ℕ} {A Lf Uf Lg Ug : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hfirst : higham_problem9_14_RecursiveFirstMethodLUFactSpec n A Lf Uf)
    (hgepp : LUFactSpec n A Lg Ug) :
    Lf = Lg ∧ Uf = Ug := by
  exact higham_problem9_14_PrePivotedGEPP_lu_unique hpre
    (higham_problem9_14_RecursiveFirstMethodLUFactSpec_to_LUFactSpec hfirst)
    hgepp

/-- **Problem 9.14 / pairwise pivoting**, one exact pairwise
pivot-and-eliminate step: move the deterministic pair pivot into the left row
`p`, then eliminate the active-column entry in the right row `q`. -/
noncomputable def higham_problem9_14_pairPivotEliminateToLeft {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q : Fin n) :
    Fin n → Fin n → ℝ :=
  higham_problem9_14_pairEliminateRow
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) k p q

/-- **Problem 9.14 / pairwise pivoting**, target-row formula for one
pairwise pivot-and-eliminate step after the deterministic pair pivot has been
moved to the left row. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k p q j : Fin n) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q j =
      higham_problem9_14_pairPivotToLeftMatrix A k p q q j -
        (higham_problem9_14_pairPivotToLeftMatrix A k p q q k /
          higham_problem9_14_pairPivotToLeftMatrix A k p q p k) *
        higham_problem9_14_pairPivotToLeftMatrix A k p q p j := by
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact higham_problem9_14_pairEliminateRow_target
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) k p q j

/-- **Problem 9.14 / pairwise pivoting**, rows other than the right-row target
are unchanged by one pairwise pivot-and-eliminate step after the pivot-to-left
permutation. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_of_ne {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q i j : Fin n}
    (hi : i ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q i j =
      higham_problem9_14_pairPivotToLeftMatrix A k p q i j := by
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact higham_problem9_14_pairEliminateRow_of_ne
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) hi

/-- **Problem 9.14 / pairwise pivoting**, the left pivot row is unchanged by
one pairwise pivot-and-eliminate step when the two pair rows are distinct. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_pivot {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q j : Fin n}
    (hpq : p ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q p j =
      higham_problem9_14_pairPivotToLeftMatrix A k p q p j :=
  higham_problem9_14_pairPivotEliminateToLeft_of_ne A hpq

/-- **Problem 9.14 / pairwise pivoting**, the multiplier used by one
pairwise pivot-and-eliminate step has magnitude at most one: after the
deterministic pair pivot has been moved to the left row `p`, the right-row
entry divided by the left pivot is bounded by the source pairwise pivot rule. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_multiplier_abs_le_one
    {n : ℕ} {A : Fin n → Fin n → ℝ} {k p q : Fin n}
    (hpq : p ≠ q)
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    |(higham_problem9_14_pairPivotToLeftMatrix A k p q q k /
        higham_problem9_14_pairPivotToLeftMatrix A k p q p k)| ≤ 1 := by
  rw [higham_problem9_14_pairPivotToLeftMatrix_left A k p q k]
  by_cases hp : higham_problem9_14_pairPivotRow A k p q = p
  · have hbound := higham_problem9_14_pairPivotRow_right_multiplier_abs_le_one
      (A := A) (k := k) (p := p) (q := q) hpivot
    simpa [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_pairPivotToLeftSwap, hp] using hbound
  · have hrow : higham_problem9_14_pairPivotRow A k p q = q := by
      rcases (higham_problem9_14_pairPivotRow_choice A k p q).1 with hleft | hright
      · exact (hp hleft).elim
      · exact hright
    have hbound := higham_problem9_14_pairPivotRow_left_multiplier_abs_le_one
      (A := A) (k := k) (p := p) (q := q) hpivot
    simpa [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_pairPivotToLeftSwap, higham_problem9_14_pairRowSwap_right,
      hp, hrow, hpq, Ne.symm hpq] using hbound

/-- **Problem 9.14 / pairwise pivoting**, after a pairwise pivot-and-eliminate
step, the left row remains the deterministically chosen pair pivot row of the
original matrix. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_left {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q j : Fin n}
    (hpq : p ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q p j =
      A (higham_problem9_14_pairPivotRow A k p q) j := by
  unfold higham_problem9_14_pairPivotEliminateToLeft
  rw [higham_problem9_14_pairEliminateRow_pivot
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) hpq]
  exact higham_problem9_14_pairPivotToLeftMatrix_left A k p q j

/-- **Problem 9.14 / pairwise pivoting**, the pairwise pivot-and-eliminate
step zeros the right row's active-column entry when the chosen pair pivot is
nonzero. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpivot : A (higham_problem9_14_pairPivotRow A k p q) k ≠ 0) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q k = 0 := by
  have hpivot_left :
      higham_problem9_14_pairPivotToLeftMatrix A k p q p k ≠ 0 := by
    simpa [higham_problem9_14_pairPivotToLeftMatrix_left A k p q k] using hpivot
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact
    higham_problem9_14_pairEliminateRow_target_active_eq_zero
      (higham_problem9_14_pairPivotToLeftMatrix A k p q) hpivot_left

/-- **Problem 9.14 / pairwise pivoting**, one exact pairwise
pivot-and-eliminate step preserves nonsingularity when the pair rows are
distinct. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_pairPivotEliminateToLeft A k p q) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  have hdet_left :=
    higham_problem9_14_pairPivotToLeftMatrix_det_ne_zero A k p q hdet
  unfold higham_problem9_14_pairPivotEliminateToLeft
  exact higham_problem9_14_pairEliminateRow_det_ne_zero
    (higham_problem9_14_pairPivotToLeftMatrix A k p q) (Ne.symm hpq)
    hdet_left

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
if the right row has active-column entry at least as large as the left row's
entry, then one pair pivot-and-eliminate step moves the right row into the left
pivot slot.  This is the local row-motion lemma used to build the row-reversal
"bubble" trace for pairwise pivoting. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|) (j : Fin n) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q p j = A q j := by
  rw [higham_problem9_14_pairPivotEliminateToLeft_left A hpq]
  rw [higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs]

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
after the right row is selected as the pivot, the old right-row slot contains
the exact elimination update of the old left row by that pivot row. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|) (j : Fin n) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q j =
      A p j - (A p k / A q k) * A q j := by
  have hsel : higham_problem9_14_pairPivotRow A k p q = q :=
    higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs
  have hqp : q ≠ p := Ne.symm hpq
  rw [higham_problem9_14_pairPivotEliminateToLeft_target]
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, higham_problem9_14_pairRowSwap,
    hsel, hqp]

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
the selected right pivot zeros the old right-row slot in the active column. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (habs : |A p k| ≤ |A q k|) (hpivot : A q k ≠ 0) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q q k = 0 := by
  have hsel : higham_problem9_14_pairPivotRow A k p q = q :=
    higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs
  exact higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero A
    (by simpa [hsel] using hpivot)

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
the exact target row after one adjacent-pair elimination is bounded by twice a
row-entry budget when both input rows obey that budget.  This is the local
growth estimate needed for the cumulative pairwise row-reversal trace. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_target_abs_le_two_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n} {M : ℝ}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|)
    (hpivot : A q k ≠ 0)
    (hp_bound : ∀ j : Fin n, |A p j| ≤ M)
    (hq_bound : ∀ j : Fin n, |A q j| ≤ M)
    (_hM : 0 ≤ M) (j : Fin n) :
    |higham_problem9_14_pairPivotEliminateToLeft A k p q q j| ≤
      2 * M := by
  have hformula :=
    higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right
      A hpq habs j
  have hden_pos : 0 < |A q k| := abs_pos.mpr hpivot
  have hratio : |A p k / A q k| ≤ 1 := by
    calc
      |A p k / A q k| = |A p k| / |A q k| := by rw [abs_div]
      _ ≤ |A q k| / |A q k| :=
          div_le_div_of_nonneg_right habs (abs_nonneg _)
      _ = 1 := by field_simp [ne_of_gt hden_pos]
  have hterm : |(A p k / A q k) * A q j| ≤ M := by
    calc
      |(A p k / A q k) * A q j|
          = |A p k / A q k| * |A q j| := by rw [abs_mul]
      _ ≤ 1 * |A q j| :=
          mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ ≤ 1 * M :=
          mul_le_mul_of_nonneg_left (hq_bound j) zero_le_one
      _ = M := by ring
  rw [hformula]
  calc
    |A p j - (A p k / A q k) * A q j|
        ≤ |A p j| + |(A p k / A q k) * A q j| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (A p j) (-((A p k / A q k) * A q j))
    _ ≤ M + M := add_le_add (hp_bound j) hterm
    _ = 2 * M := by ring

/-- **Problem 9.14 / pairwise pivoting**, generic right-dominant pair step:
all rows outside the compared pair are unchanged.  This is the row-shape
invariant needed when iterating adjacent pair steps to bubble the pre-pivoted
row upward through the row-reversed matrix. -/
theorem higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q i j : Fin n}
    (hpq : p ≠ q) (habs : |A p k| ≤ |A q k|)
    (hip : i ≠ p) (hiq : i ≠ q) :
    higham_problem9_14_pairPivotEliminateToLeft A k p q i j = A i j := by
  rw [higham_problem9_14_pairPivotEliminateToLeft_of_ne A hiq]
  have hsel : higham_problem9_14_pairPivotRow A k p q = q :=
    higham_problem9_14_pairPivotRow_eq_right_of_abs_le A habs
  have hnot : higham_problem9_14_pairPivotRow A k p q ≠ p := by
    intro h
    exact hpq (h.symm.trans hsel)
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, higham_problem9_14_pairRowSwap,
    hnot]
  exact congrArg (fun r => A r j) (Equiv.swap_apply_of_ne_of_ne hip hiq)

/-- **Problem 9.14**, running one pair pivot-and-eliminate step on the
row-reversed matrix `ΠA` preserves nonsingularity whenever the source matrix is
nonsingular and the compared pair rows are distinct. -/
theorem higham_problem9_14_rowReversedMatrix_pairPivotEliminateToLeft_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ) {k p q : Fin n}
    (hpq : p ≠ q)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) k p q) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  have hdet_rev := higham_problem9_14_rowReversedMatrix_det_ne_zero A hdet
  exact higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero
    (higham_problem9_14_rowReversedMatrix A) hpq hdet_rev

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: when the
row-reversed matrix `ΠA` compares any distinct left row with the last row in
the first column, one pair pivot-and-eliminate step moves the original first
row of `A` into the left pivot slot. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p j =
      A 0 j := by
  have hsel :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
      hpre p
  rw [higham_problem9_14_pairPivotEliminateToLeft_left
    (higham_problem9_14_rowReversedMatrix A) hp]
  rw [hsel]
  have hlast :
      higham_problem9_14_rowReversal
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
        (0 : Fin (m + 1)) := by
    ext
    simp [higham_problem9_14_rowReversal]
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    hlast]

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: one
first-column pair pivot-and-eliminate step leaves every row outside the
compared pair unchanged.  This is the local row-shape invariant for the
still-open cumulative row-reversal/pairwise-pivoting trace equivalence. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) i j =
      higham_problem9_14_rowReversedMatrix A i j := by
  have hpivot :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  have habs :
      |higham_problem9_14_rowReversedMatrix A p 0| ≤
        |higham_problem9_14_rowReversedMatrix A
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0| :=
    hpivot.2 p (Nat.zero_le _)
  exact
    higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
      (higham_problem9_14_rowReversedMatrix A) hp habs hip hilast

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
first-column pair pivot-and-eliminate step, the moved pivot row still has a
nonzero active entry.  This is the local nonzero-pivot invariant for the
cumulative adjacent-pair bubble trace. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_active_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p 0 ≠ 0 := by
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  have hpivrow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      hpre hp (0 : Fin (m + 1))
  simpa [hpivrow] using hpiv

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
first-column bubble step, every unchanged row remains dominated in the active
column by the moved pivot row.  This is the selector invariant needed to
continue bubbling the same source pivot row through adjacent pair steps. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) i 0| ≤
      |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p 0| := by
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hirow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair
      hpre hp hip hilast (0 : Fin (m + 1))
  have hprow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      hpre hp (0 : Fin (m + 1))
  have hlast :
      higham_problem9_14_rowReversedMatrix A last 0 = A 0 0 := by
    have hlastmap : higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
      subst last
      ext
      simp [higham_problem9_14_rowReversal]
    simp [last, higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      hlastmap]
  have hchoice :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  have hdom :
      |higham_problem9_14_rowReversedMatrix A i 0| ≤
        |higham_problem9_14_rowReversedMatrix A last 0| :=
    hchoice.2 i (Nat.zero_le _)
  rw [hirow, hprow]
  simpa [hlast] using hdom

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
first-column bubble step, the natural pairwise selector chooses the moved
pivot row as the right member against any unchanged row. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_next_pairPivotRow
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    higham_problem9_14_pairPivotRow
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p = p := by
  exact higham_problem9_14_pairPivotRow_eq_right_of_abs_le
    (higham_problem9_14_pairPivotEliminateToLeft
      (higham_problem9_14_rowReversedMatrix A) 0 p
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot
      hpre hp hip hilast)

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after one
bubble step has moved the source pivot row into position `p`, a second
right-dominant pair step against an unchanged row `i` moves that same source
pivot row into position `i`.  This is the two-step local trace shape needed by
the cumulative adjacent-pair bubble construction. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p i j =
      A 0 j := by
  rw [higham_problem9_14_pairPivotEliminateToLeft_left
    (higham_problem9_14_pairPivotEliminateToLeft
      (higham_problem9_14_rowReversedMatrix A) 0 p
      (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) hip]
  rw [
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_next_pairPivotRow
      hpre hp hip hilast]
  exact
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      hpre hp j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after two
right-dominant adjacent pair steps, every row outside the three touched row
positions is still the corresponding row of `ΠA`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_of_ne_triple
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i r : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hri : r ≠ i)
    (hrp : r ≠ p)
    (hrlast : r ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p r j =
      higham_problem9_14_rowReversedMatrix A r j := by
  have habs :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot
      hpre hp hip hilast
  have hsecond :=
    higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
      (A := higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
      (k := 0) (p := i) (q := p) (i := r) (j := j)
      hip habs hri hrp
  rw [hsecond]
  exact
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair
      hpre hp hrp hrlast j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after two
adjacent pair steps, the twice-moved source pivot row still has a nonzero
active entry. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_active_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p i 0 ≠ 0 := by
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  have hrow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
      hpre hp hip hilast (0 : Fin (m + 1))
  simpa [hrow] using hpiv

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: after two
adjacent pair steps, every row outside the three touched row positions remains
dominated in the active column by the twice-moved pivot row. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_unchanged_abs_le_pivot
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p i r : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hip : i ≠ p)
    (hilast : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hri : r ≠ i)
    (hrp : r ≠ p)
    (hrlast : r ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p r 0| ≤
      |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairPivotEliminateToLeft
          (higham_problem9_14_rowReversedMatrix A) 0 p
          (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) 0 i p i 0| := by
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hrrow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_of_ne_triple
      hpre hp hip hilast hri hrp hrlast (0 : Fin (m + 1))
  have hirow :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
      hpre hp hip hilast (0 : Fin (m + 1))
  have hlast :
      higham_problem9_14_rowReversedMatrix A last 0 = A 0 0 := by
    have hlastmap : higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
      subst last
      ext
      simp [higham_problem9_14_rowReversal]
    simp [last, higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      hlastmap]
  have hchoice :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  have hdom :
      |higham_problem9_14_rowReversedMatrix A r 0| ≤
        |higham_problem9_14_rowReversedMatrix A last 0| :=
    hchoice.2 r (Nat.zero_le _)
  rw [hrrow, hirow]
  simpa [hlast] using hdom

/-- **Problem 9.14 / pairwise pivoting**, recursive exact first-column
pairwise-bubble matrix for the source row-reversal route.  Step `t + 1`
compares rows `m-(t+1)` and `m-t`, so each genuine step is an adjacent
pairwise pivot-and-eliminate operation. -/
noncomputable def higham_problem9_14_pairwiseBubbleMatrix {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → Fin (m + 1) → Fin (m + 1) → ℝ
  | 0 => higham_problem9_14_rowReversedMatrix A
  | t + 1 =>
      higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairwiseBubbleMatrix A t) 0
        (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
        (higham_problem9_14_pairwiseBubbleRow (m := m) t)

/-- **Problem 9.14 / pairwise pivoting**, the recursive bubble matrix starts
from the source row-reversed matrix `ΠA`. -/
@[simp] theorem higham_problem9_14_pairwiseBubbleMatrix_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_pairwiseBubbleMatrix A 0 =
      higham_problem9_14_rowReversedMatrix A := rfl

/-- **Problem 9.14 / pairwise pivoting**, unfolding one scheduled adjacent
pairwise bubble step. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_succ {m t : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_pairwiseBubbleMatrix A (t + 1) =
      higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_pairwiseBubbleMatrix A t) 0
        (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
        (higham_problem9_14_pairwiseBubbleRow (m := m) t) := rfl

/-- **Problem 9.14 / pairwise pivoting**, source-facing trace predicate for
the adjacent row-reversal bubble.  The initial state is `ΠA`; each genuine
step compares the scheduled adjacent rows `m-(t+1)` and `m-t` in column zero
and performs one exact pairwise pivot-and-eliminate operation. -/
inductive higham_problem9_14_PairwiseBubbleTrace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ℕ → (Fin (m + 1) → Fin (m + 1) → ℝ) → Prop
  | init :
      higham_problem9_14_PairwiseBubbleTrace A 0
        (higham_problem9_14_rowReversedMatrix A)
  | step {t : ℕ} {B : Fin (m + 1) → Fin (m + 1) → ℝ}
      (ht : t < m)
      (htrace : higham_problem9_14_PairwiseBubbleTrace A t B) :
      higham_problem9_14_PairwiseBubbleTrace A (t + 1)
        (higham_problem9_14_pairPivotEliminateToLeft B 0
          (higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
          (higham_problem9_14_pairwiseBubbleRow (m := m) t))

/-- **Problem 9.14 / pairwise pivoting**, the recursive scheduled matrix is a
valid adjacent row-reversal bubble trace at every prefix `t <= m`. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ∀ t : ℕ, t ≤ m →
      higham_problem9_14_PairwiseBubbleTrace A t
        (higham_problem9_14_pairwiseBubbleMatrix A t) := by
  intro t
  induction t with
  | zero =>
      intro _ht
      exact higham_problem9_14_PairwiseBubbleTrace.init
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      simpa [higham_problem9_14_pairwiseBubbleMatrix_succ] using
        higham_problem9_14_PairwiseBubbleTrace.step ht (ih ht_le)

/-- **Problem 9.14 / pairwise pivoting**, terminal source-facing trace for the
scheduled adjacent row-reversal bubble. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_terminal_trace {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) :
    higham_problem9_14_PairwiseBubbleTrace A m
      (higham_problem9_14_pairwiseBubbleMatrix A m) :=
  higham_problem9_14_pairwiseBubbleMatrix_trace A m le_rfl

/-- **Problem 9.14 / pairwise pivoting**, every scheduled adjacent
row-reversal bubble prefix preserves nonsingularity.  The base step uses
nonsingularity of `ΠA`; each later step is one determinant-preserving pairwise
pivot-and-eliminate operation on distinct adjacent rows. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet : Matrix.det
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∀ t : ℕ, t ≤ m →
      Matrix.det
        (Matrix.of (higham_problem9_14_pairwiseBubbleMatrix A t) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 := by
  intro t
  induction t with
  | zero =>
      intro _ht
      simpa [higham_problem9_14_pairwiseBubbleMatrix_zero] using
        higham_problem9_14_rowReversedMatrix_det_ne_zero A hdet
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      have hpq :
          higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1) ≠
            higham_problem9_14_pairwiseBubbleRow (m := m) t :=
        higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      simpa [higham_problem9_14_pairwiseBubbleMatrix_succ] using
        higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero
          (A := higham_problem9_14_pairwiseBubbleMatrix A t)
          (k := 0)
          (p := higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1))
          (q := higham_problem9_14_pairwiseBubbleRow (m := m) t)
          hpq (ih ht_le)

/-- **Problem 9.14 / pairwise pivoting**, terminal nonsingularity for the
scheduled row-reversal bubble. -/
theorem higham_problem9_14_pairwiseBubbleMatrix_terminal_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet : Matrix.det
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham_problem9_14_pairwiseBubbleMatrix A m) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0 :=
  higham_problem9_14_pairwiseBubbleMatrix_det_ne_zero A hdet m le_rfl

/-- **Problem 9.14 / pairwise pivoting**, general prefix invariant for the
scheduled row-reversal bubble.  After `t` genuine adjacent pairwise steps, the
carried pivot row contains the original first row of `A`, that active pivot is
nonzero, every still-untouched row above it is still the corresponding row of
`ΠA`, and those untouched active-column entries are dominated by the carried
pivot.  This is the local induction surface needed before proving the terminal
pairwise trace equivalence in full Problem 9.14. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      (∀ j : Fin (m + 1),
        higham_problem9_14_pairwiseBubbleMatrix A t
          (higham_problem9_14_pairwiseBubbleRow (m := m) t) j = A 0 j) ∧
      higham_problem9_14_pairwiseBubbleMatrix A t
        (higham_problem9_14_pairwiseBubbleRow (m := m) t) 0 ≠ 0 ∧
      (∀ r : Fin (m + 1),
        r.val < (higham_problem9_14_pairwiseBubbleRow (m := m) t).val →
          ∀ j : Fin (m + 1),
            higham_problem9_14_pairwiseBubbleMatrix A t r j =
              higham_problem9_14_rowReversedMatrix A r j) ∧
      (∀ r : Fin (m + 1),
        r.val < (higham_problem9_14_pairwiseBubbleRow (m := m) t).val →
          |higham_problem9_14_pairwiseBubbleMatrix A t r 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t
              (higham_problem9_14_pairwiseBubbleRow (m := m) t) 0|) := by
  let row : ℕ → Fin (m + 1) :=
    fun t => higham_problem9_14_pairwiseBubbleRow (m := m) t
  have hrow0 : ∀ j : Fin (m + 1),
      higham_problem9_14_rowReversedMatrix A (row 0) j = A 0 j := by
    intro j
    have hmap : higham_problem9_14_rowReversal (row 0) = (0 : Fin (m + 1)) := by
      ext
      simp [row, higham_problem9_14_pairwiseBubbleRow,
        higham_problem9_14_rowReversal]
    rw [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
    change A (higham_problem9_14_rowReversal (row 0)) j = A 0 j
    rw [hmap]
  have hpivA : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  have hchoice :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).1
  intro t
  induction t with
  | zero =>
      intro _ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j
        simpa [row, higham_problem9_14_pairwiseBubbleMatrix_zero] using
          hrow0 j
      · rw [higham_problem9_14_pairwiseBubbleMatrix_zero,
          hrow0 (0 : Fin (m + 1))]
        exact hpivA
      · intro r _hr j
        simp [higham_problem9_14_pairwiseBubbleMatrix_zero]
      · intro r _hr
        have hdom :
            |higham_problem9_14_rowReversedMatrix A r 0| ≤
              |higham_problem9_14_rowReversedMatrix A (row 0) 0| :=
          by
            simpa [row] using hchoice.2 r (Nat.zero_le _)
        simpa [row, higham_problem9_14_pairwiseBubbleMatrix_zero] using hdom
  | succ t ih =>
      intro hsucc
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      rcases ih ht_le with ⟨hpivotRow, hpivot_ne, hunchanged, hdom⟩
      let p : Fin (m + 1) := row (t + 1)
      let q : Fin (m + 1) := row t
      have hpq : p ≠ q := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      have hpq_val : p.val < q.val := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRow_succ_val_lt (m := m) (t := t) ht
      have habs :
          |higham_problem9_14_pairwiseBubbleMatrix A t p 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t q 0| := by
        simpa [p, q, row] using hdom p hpq_val
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hleft :=
          higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) hpq habs j
        rw [hleft]
        simpa [q, row] using hpivotRow j
      · rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hleft :=
          higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) hpq habs (0 : Fin (m + 1))
        rw [hleft]
        simpa [q, row] using hpivot_ne
      · intro r hr j
        have hrp_lt : r.val < p.val := by
          simpa [p] using hr
        have hrq_lt : r.val < q.val := lt_trans hrp_lt hpq_val
        have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = q.val := hval
          omega
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hsame :=
          higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) (i := r) (j := j)
            hpq habs hrp hrq
        rw [hsame]
        exact hunchanged r hrq_lt j
      · intro r hr
        have hrp_lt : r.val < p.val := by
          simpa [p] using hr
        have hrq_lt : r.val < q.val := lt_trans hrp_lt hpq_val
        have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        have hrq : r ≠ q := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = q.val := hval
          omega
        have hr_step :
            higham_problem9_14_pairwiseBubbleMatrix A (t + 1) r
                (0 : Fin (m + 1)) =
              higham_problem9_14_rowReversedMatrix A r 0 := by
          rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
          have hsame :=
            higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
              (A := higham_problem9_14_pairwiseBubbleMatrix A t)
              (k := 0) (p := p) (q := q) (i := r)
              (j := (0 : Fin (m + 1))) hpq habs hrp hrq
          rw [hsame]
          exact hunchanged r hrq_lt 0
        have hp_step :
            higham_problem9_14_pairwiseBubbleMatrix A (t + 1) p
                (0 : Fin (m + 1)) = A 0 0 := by
          rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
          have hleft :=
            higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le
              (A := higham_problem9_14_pairwiseBubbleMatrix A t)
              (k := 0) (p := p) (q := q) hpq habs (0 : Fin (m + 1))
          rw [hleft]
          simpa [q, row] using hpivotRow (0 : Fin (m + 1))
        have horig :
            |higham_problem9_14_rowReversedMatrix A r 0| ≤
              |higham_problem9_14_rowReversedMatrix A (row 0) 0| :=
          by
            simpa [row] using hchoice.2 r (Nat.zero_le _)
        calc
          |higham_problem9_14_pairwiseBubbleMatrix A (t + 1) r
              (0 : Fin (m + 1))|
              = |higham_problem9_14_rowReversedMatrix A r 0| := by
                rw [hr_step]
          _ ≤ |higham_problem9_14_rowReversedMatrix A (row 0) 0| := horig
          _ = |higham_problem9_14_pairwiseBubbleMatrix A (t + 1) p
              (0 : Fin (m + 1))| := by
                rw [hrow0 (0 : Fin (m + 1)), hp_step]

/-- **Problem 9.14 / pairwise pivoting**, terminal row-motion consequence of
the scheduled prefix invariant: after the adjacent bubble has run from the last
row of `ΠA` to row zero, row zero contains the original first row of `A`. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (j : Fin (m + 1)) :
    higham_problem9_14_pairwiseBubbleMatrix A m 0 j = A 0 j := by
  have h :=
    (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
      hpre m le_rfl).1 j
  simpa using h

/-- **Problem 9.14 / pairwise pivoting**, terminal nonzero-pivot consequence
of the scheduled prefix invariant. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_active_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    higham_problem9_14_pairwiseBubbleMatrix A m 0 0 ≠ 0 := by
  have h :=
    (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
      hpre m le_rfl).2.1
  simpa using h

/-- **Problem 9.14 / pairwise pivoting**, eliminated-column prefix invariant
for the scheduled row-reversal bubble.  After `t` scheduled adjacent pairwise
steps, every row below the carried pivot has zero active-column entry. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_active_eq_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      ∀ r : Fin (m + 1),
        (higham_problem9_14_pairwiseBubbleRow (m := m) t).val < r.val →
          higham_problem9_14_pairwiseBubbleMatrix A t r 0 = 0 := by
  intro t
  induction t with
  | zero =>
      intro _ht r hr
      have hlt := r.isLt
      simp [higham_problem9_14_pairwiseBubbleRow] at hr
      omega
  | succ t ih =>
      intro hsucc r hr
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      let p : Fin (m + 1) :=
        higham_problem9_14_pairwiseBubbleRow (m := m) (t + 1)
      let q : Fin (m + 1) :=
        higham_problem9_14_pairwiseBubbleRow (m := m) t
      have hpq : p ≠ q := by
        simpa [p, q] using
          higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      have hpq_val : p.val < q.val := by
        simpa [p, q] using
          higham_problem9_14_pairwiseBubbleRow_succ_val_lt (m := m) (t := t) ht
      have hq_eq : p.val + 1 = q.val := by
        have hadj :=
          higham_problem9_14_pairwiseBubbleRows_adjacent (m := m) (t := t) ht
        rcases hadj with hforward | hback
        · simpa [p, q] using hforward
        · have hbad : q.val + 1 = p.val := by
            simpa [p, q] using hback
          omega
      have hinv :=
        higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
          (A := A) hpre t ht_le
      have habs :
          |higham_problem9_14_pairwiseBubbleMatrix A t p 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t q 0| := by
        simpa [p, q] using hinv.2.2.2 p hpq_val
      have hpivot : higham_problem9_14_pairwiseBubbleMatrix A t q 0 ≠ 0 := by
        simpa [q] using hinv.2.1
      by_cases hrq : r = q
      · subst r
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        exact
          higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) habs hpivot
      · have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hsame :=
          higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) (i := r)
            (j := (0 : Fin (m + 1))) hpq habs hrp hrq
        rw [hsame]
        have hr_val_ne_q : r.val ≠ q.val := by
          intro hval
          exact hrq (Fin.ext hval)
        have hq_lt_r : q.val < r.val := by
          have hp_lt_r : p.val < r.val := by
            simpa [p] using hr
          omega
        exact ih ht_le r hq_lt_r

/-- **Problem 9.14 / pairwise pivoting**, terminal eliminated-column
consequence: after the scheduled bubble reaches row zero, every nonzero row
has active-column entry zero. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_active_eq_zero_of_ne_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {i : Fin (m + 1)} (hi : i ≠ 0) :
    higham_problem9_14_pairwiseBubbleMatrix A m i 0 = 0 := by
  have hival_ne : i.val ≠ 0 := by
    intro hval
    exact hi (Fin.ext hval)
  have hpos : 0 < i.val := Nat.pos_of_ne_zero hival_ne
  exact
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_active_eq_zero
      (A := A) hpre m le_rfl i (by
        simpa [higham_problem9_14_pairwiseBubbleRow_self] using hpos)

/-- **Problem 9.14 / pairwise pivoting**, prefix row formula for rows already
eliminated by the scheduled adjacent bubble.  Every row below the carried pivot
is the exact first-column Schur update of the corresponding source row by the
original first row of `A`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∀ t : ℕ, t ≤ m →
      ∀ r : Fin (m + 1),
        (higham_problem9_14_pairwiseBubbleRow (m := m) t).val < r.val →
          ∀ j : Fin (m + 1),
            higham_problem9_14_pairwiseBubbleMatrix A t r j =
              A (higham_problem9_14_pairwiseBubbleSourceRow (m := m) r) j -
                (A (higham_problem9_14_pairwiseBubbleSourceRow (m := m) r) 0 /
                    A 0 0) * A 0 j := by
  let row : ℕ → Fin (m + 1) :=
    fun t => higham_problem9_14_pairwiseBubbleRow (m := m) t
  have hrow0 : ∀ j : Fin (m + 1),
      higham_problem9_14_rowReversedMatrix A (row 0) j = A 0 j := by
    intro j
    have hmap : higham_problem9_14_rowReversal (row 0) = (0 : Fin (m + 1)) := by
      ext
      simp [row, higham_problem9_14_pairwiseBubbleRow,
        higham_problem9_14_rowReversal]
    rw [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
    change A (higham_problem9_14_rowReversal (row 0)) j = A 0 j
    rw [hmap]
  intro t
  induction t with
  | zero =>
      intro _ht r hr j
      have hlt := r.isLt
      simp [higham_problem9_14_pairwiseBubbleRow] at hr
      omega
  | succ t ih =>
      intro hsucc r hr j
      have ht : t < m := Nat.lt_of_succ_le hsucc
      have ht_le : t ≤ m := Nat.le_of_lt ht
      let p : Fin (m + 1) := row (t + 1)
      let q : Fin (m + 1) := row t
      have hpq : p ≠ q := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := t) ht
      have hpq_val : p.val < q.val := by
        simpa [p, q, row] using
          higham_problem9_14_pairwiseBubbleRow_succ_val_lt (m := m) (t := t) ht
      have hq_eq : p.val + 1 = q.val := by
        have hadj :=
          higham_problem9_14_pairwiseBubbleRows_adjacent (m := m) (t := t) ht
        rcases hadj with hforward | hback
        · simpa [p, q, row] using hforward
        · have hbad : q.val + 1 = p.val := by
            simpa [p, q, row] using hback
          omega
      have hinv :=
        higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant
          (A := A) hpre t ht_le
      have hpivotRow := hinv.1
      have hunchanged := hinv.2.2.1
      have hdom := hinv.2.2.2
      have habs :
          |higham_problem9_14_pairwiseBubbleMatrix A t p 0| ≤
            |higham_problem9_14_pairwiseBubbleMatrix A t q 0| := by
        simpa [p, q, row] using hdom p hpq_val
      by_cases hrq : r = q
      · subst r
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have htarget :=
          higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) hpq habs j
        rw [htarget]
        have hp_row :
            higham_problem9_14_pairwiseBubbleMatrix A t p j =
              higham_problem9_14_rowReversedMatrix A p j :=
          hunchanged p hpq_val j
        have hp_active :
            higham_problem9_14_pairwiseBubbleMatrix A t p 0 =
              higham_problem9_14_rowReversedMatrix A p 0 :=
          hunchanged p hpq_val 0
        have hq_row :
            higham_problem9_14_pairwiseBubbleMatrix A t q j = A 0 j := by
          simpa [q, row] using hpivotRow j
        have hq_active :
            higham_problem9_14_pairwiseBubbleMatrix A t q 0 = A 0 0 := by
          simpa [q, row] using hpivotRow (0 : Fin (m + 1))
        have hsrc :
            higham_problem9_14_pairwiseBubbleSourceRow (m := m) q =
              higham_problem9_14_rowReversal p := by
          ext
          simp [higham_problem9_14_pairwiseBubbleSourceRow,
            higham_problem9_14_rowReversal, p, q, row,
            higham_problem9_14_pairwiseBubbleRow]
          omega
        rw [hp_row, hp_active, hq_row, hq_active]
        simp only [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
        rw [← hsrc]
      · have hp_lt_r : p.val < r.val := by
          simpa [p, row] using hr
        have hrp : r ≠ p := by
          intro h
          have hval := congrArg Fin.val h
          have : r.val = p.val := hval
          omega
        have hq_lt_r : q.val < r.val := by
          have hr_val_ne_q : r.val ≠ q.val := by
            intro hval
            exact hrq (Fin.ext hval)
          omega
        rw [higham_problem9_14_pairwiseBubbleMatrix_succ]
        have hsame :=
          higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le
            (A := higham_problem9_14_pairwiseBubbleMatrix A t)
            (k := 0) (p := p) (q := q) (i := r) (j := j)
            hpq habs hrp hrq
        rw [hsame]
        exact ih ht_le r hq_lt_r j

/-- **Problem 9.14 / pairwise pivoting**, terminal first-Schur bridge.  The
trailing block of the scheduled adjacent row-reversal bubble is exactly the
row reversal of the first Schur complement of `A`.  Together with the terminal
row-zero/column-zero facts, this is the local bridge from the source pairwise
trace toward the recursive no-interchange LU route. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_trailing_eq_rowReversed_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (i j : Fin m) :
    higham_problem9_14_pairwiseBubbleMatrix A m i.succ j.succ =
      higham_problem9_14_rowReversedMatrix (luFirstSchurComplement A) i j := by
  have hrow :=
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_row
      (A := A) hpre m le_rfl i.succ (by
        simp [higham_problem9_14_pairwiseBubbleRow_self]) j.succ
  rw [hrow]
  rw [higham_problem9_14_pairwiseBubbleSourceRow_succ]
  have hpiv : A 0 0 ≠ 0 := by
    cases hpre with
    | step _ hpivot _ => simpa using hpivot
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    luFirstSchurComplement]
  field_simp [hpiv]

/-- **Problem 9.14 / pairwise pivoting**, terminal Schur-complement form.
After the scheduled adjacent row-reversal bubble reaches row zero, the first
Schur complement of the terminal full matrix is exactly the row reversal of
the first Schur complement of the original pre-pivoted input. -/
theorem
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    luFirstSchurComplement (higham_problem9_14_pairwiseBubbleMatrix A m) =
      higham_problem9_14_rowReversedMatrix (luFirstSchurComplement A) := by
  funext i j
  unfold luFirstSchurComplement
  have htrail :=
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_trailing_eq_rowReversed_firstSchurComplement
      (A := A) hpre i j
  have hzero :
      higham_problem9_14_pairwiseBubbleMatrix A m i.succ (0 : Fin (m + 1)) = 0 :=
    higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_active_eq_zero_of_ne_zero
      (A := A) hpre i.succ_ne_zero
  rw [htrail, hzero]
  simp [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
    luFirstSchurComplement, div_eq_mul_inv]

/-- **Problem 9.14 / pairwise pivoting**, recursive source-facing trace
certificate.  At each nonempty stage, the row-reversed active matrix runs the
scheduled adjacent pairwise bubble, whose first Schur complement is the
row-reversal of the next no-interchange Schur complement; the certificate then
recurses on that next source Schur complement. -/
inductive higham_problem9_14_RecursivePairwiseBubbleTrace :
    (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | done {A : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursivePairwiseBubbleTrace 0 A
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      (hbubble :
        higham_problem9_14_PairwiseBubbleTrace A m
          (higham_problem9_14_pairwiseBubbleMatrix A m))
      (hschur :
        luFirstSchurComplement
            (higham_problem9_14_pairwiseBubbleMatrix A m) =
          higham_problem9_14_rowReversedMatrix
            (luFirstSchurComplement A))
      (hnext :
        higham_problem9_14_RecursivePairwiseBubbleTrace m
          (luFirstSchurComplement A)) :
      higham_problem9_14_RecursivePairwiseBubbleTrace (m + 1) A

/-- **Problem 9.14 / pairwise pivoting**, a pre-pivoted GEPP input admits the
recursive row-reversal pairwise-bubble trace certificate.  This packages the
terminal first-Schur bridge with the no-interchange Schur-complement handoff;
it is still an intermediate trace-existence result, not the final same-LU
factorization theorem. -/
theorem higham_problem9_14_RecursivePairwiseBubbleTrace_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        higham_problem9_14_RecursivePairwiseBubbleTrace n A := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact higham_problem9_14_RecursivePairwiseBubbleTrace.done
  | succ m ih =>
      intro A hpre
      exact higham_problem9_14_RecursivePairwiseBubbleTrace.step
        (higham_problem9_14_pairwiseBubbleMatrix_terminal_trace A)
        (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement
          (A := A) hpre)
        (ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre))

/-- **Problem 9.14 / pairwise pivoting**, recursive pairwise LU certificate.
The certificate records, at each nonempty stage, the source-facing scheduled
pairwise bubble on the row-reversed active matrix, the terminal Schur bridge,
and the recursively constructed factors for the no-interchange Schur
complement. -/
inductive higham_problem9_14_RecursivePairwiseLUFactSpec :
    (n : ℕ) → (Fin n → Fin n → ℝ) →
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Prop
  | done {A L U : Fin 0 → Fin 0 → ℝ} :
      higham_problem9_14_RecursivePairwiseLUFactSpec 0 A L U
  | step {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
      {L₁ U₁ : Fin m → Fin m → ℝ}
      (hpivot : A 0 0 ≠ 0)
      (hbubble :
        higham_problem9_14_PairwiseBubbleTrace A m
          (higham_problem9_14_pairwiseBubbleMatrix A m))
      (hschur :
        luFirstSchurComplement
            (higham_problem9_14_pairwiseBubbleMatrix A m) =
          higham_problem9_14_rowReversedMatrix
            (luFirstSchurComplement A))
      (hnext :
        higham_problem9_14_RecursivePairwiseLUFactSpec m
          (luFirstSchurComplement A) L₁ U₁) :
      higham_problem9_14_RecursivePairwiseLUFactSpec (m + 1) A
        (luFirstStepL A L₁) (luFirstStepU A U₁)

/-- **Problem 9.14 / pairwise pivoting**, every recursive pairwise LU
certificate is an exact ordinary LU certificate for the source matrix. -/
theorem higham_problem9_14_RecursivePairwiseLUFactSpec_to_LUFactSpec :
    ∀ {n : ℕ} {A L U : Fin n → Fin n → ℝ},
      higham_problem9_14_RecursivePairwiseLUFactSpec n A L U →
        LUFactSpec n A L U := by
  intro n A L U htrace
  induction htrace with
  | done =>
      refine
        { L_diag := ?_
          L_upper_zero := ?_
          U_lower_zero := ?_
          product_eq := ?_ }
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | step hpivot _hbubble _hschur _hnext ih =>
      exact LUFactSpec.of_firstSchurComplement_explicit hpivot ih

/-- **Problem 9.14 / pairwise pivoting**, existence of recursive pairwise LU
factors for every pre-pivoted GEPP input. -/
theorem higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP :
    ∀ {n : ℕ} {A : Fin n → Fin n → ℝ},
      higham_problem9_14_PrePivotedGEPP A →
        ∃ L U : Fin n → Fin n → ℝ,
          higham_problem9_14_RecursivePairwiseLUFactSpec n A L U := by
  intro n
  induction n with
  | zero =>
      intro A _hpre
      exact ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
        higham_problem9_14_RecursivePairwiseLUFactSpec.done⟩
  | succ m ih =>
      intro A hpre
      obtain ⟨L₁, U₁, hnextLU⟩ :=
        ih (A := luFirstSchurComplement A)
          (higham_problem9_14_PrePivotedGEPP_firstSchurComplement hpre)
      have hpivot : A 0 0 ≠ 0 := by
        cases hpre with
        | step _hchoice hpivot _hnext =>
            exact hpivot
      exact
        ⟨luFirstStepL A L₁, luFirstStepU A U₁,
          higham_problem9_14_RecursivePairwiseLUFactSpec.step
            hpivot
            (higham_problem9_14_pairwiseBubbleMatrix_terminal_trace A)
            (higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement
              (A := A) hpre)
            hnextLU⟩

/-- **Problem 9.14 / same-LU bridge**, any recursive pairwise LU certificate
for a pre-pivoted input has the same exact factors as any GEPP/no-interchange
exact LU certificate for that input. -/
theorem higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP
    {n : ℕ} {A Lp Up Lg Ug : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hpair : higham_problem9_14_RecursivePairwiseLUFactSpec n A Lp Up)
    (hgepp : LUFactSpec n A Lg Ug) :
    Lp = Lg ∧ Up = Ug := by
  exact higham_problem9_14_PrePivotedGEPP_lu_unique hpre
    (higham_problem9_14_RecursivePairwiseLUFactSpec_to_LUFactSpec hpair)
    hgepp

/-- **Problem 9.14 / same-LU bridge**, source-facing first-method package:
for every pre-pivoted GEPP input, the recursive §9.9 first-method factors
exist and agree with the exact GEPP/no-interchange LU factors. -/
theorem higham_problem9_14_PrePivotedGEPP_exists_RecursiveFirstMethodLUFactSpec_same_as_GEPP
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∃ Lf Uf Lg Ug : Fin n → Fin n → ℝ,
      higham_problem9_14_RecursiveFirstMethodLUFactSpec n A Lf Uf ∧
        LUFactSpec n A Lg Ug ∧ Lf = Lg ∧ Uf = Ug := by
  obtain ⟨Lf, Uf, hfirst⟩ :=
    higham_problem9_14_exists_RecursiveFirstMethodLUFactSpec_of_PrePivotedGEPP
      hpre
  obtain ⟨Lg, Ug, hgepp⟩ :=
    higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec hpre
  have hsame :=
    higham_problem9_14_RecursiveFirstMethodLUFactSpec_same_as_PrePivotedGEPP
      hpre hfirst hgepp
  exact ⟨Lf, Uf, Lg, Ug, hfirst, hgepp, hsame.1, hsame.2⟩

/-- **Problem 9.14 / same-LU bridge**, source-facing pairwise package:
for every pre-pivoted GEPP input, the recursive adjacent-pair factors exist
and agree with the exact GEPP/no-interchange LU factors. -/
theorem higham_problem9_14_PrePivotedGEPP_exists_RecursivePairwiseLUFactSpec_same_as_GEPP
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∃ Lp Up Lg Ug : Fin n → Fin n → ℝ,
      higham_problem9_14_RecursivePairwiseLUFactSpec n A Lp Up ∧
        LUFactSpec n A Lg Ug ∧ Lp = Lg ∧ Up = Ug := by
  obtain ⟨Lp, Up, hpair⟩ :=
    higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP
      hpre
  obtain ⟨Lg, Ug, hgepp⟩ :=
    higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec hpre
  have hsame :=
    higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP
      hpre hpair hgepp
  exact ⟨Lp, Up, Lg, Ug, hpair, hgepp, hsame.1, hsame.2⟩

/-- **Problem 9.14 / same-LU bridge**, the two source routes compute the same
exact factors on every pre-pivoted GEPP input.  This combines the recursive
§9.9 first-method package with the adjacent-pair row-reversal package through
ordinary exact-LU uniqueness. -/
theorem higham_problem9_14_PrePivotedGEPP_exists_firstMethod_pairwise_same_LU
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A) :
    ∃ Lf Uf Lp Up : Fin n → Fin n → ℝ,
      higham_problem9_14_RecursiveFirstMethodLUFactSpec n A Lf Uf ∧
        higham_problem9_14_RecursivePairwiseLUFactSpec n A Lp Up ∧
          Lf = Lp ∧ Uf = Up := by
  obtain ⟨Lf, Uf, hfirst⟩ :=
    higham_problem9_14_exists_RecursiveFirstMethodLUFactSpec_of_PrePivotedGEPP
      hpre
  obtain ⟨Lp, Up, hpair⟩ :=
    higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP
      hpre
  obtain ⟨Lg, Ug, hgepp⟩ :=
    higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec hpre
  have hfirst_same :=
    higham_problem9_14_RecursiveFirstMethodLUFactSpec_same_as_PrePivotedGEPP
      hpre hfirst hgepp
  have hpair_same :=
    higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP
      hpre hpair hgepp
  exact ⟨Lf, Uf, Lp, Up, hfirst, hpair,
    hfirst_same.1.trans hpair_same.1.symm,
    hfirst_same.2.trans hpair_same.2.symm⟩

/-- **Problem 9.14 / pairwise pivoting**, the first scheduled bubble step
moves the original first row of a pre-pivoted input into row `m-1`. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_one_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hm : 0 < m) (j : Fin (m + 1)) :
    higham_problem9_14_pairwiseBubbleMatrix A 1
        (higham_problem9_14_pairwiseBubbleRow (m := m) 1) j =
      A 0 j := by
  have hp :
      higham_problem9_14_pairwiseBubbleRow (m := m) 1 ≠
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    simpa using
      higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := 0) hm
  simpa [higham_problem9_14_pairwiseBubbleMatrix_succ,
    higham_problem9_14_pairwiseBubbleMatrix_zero] using
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row
      (A := A) hpre (p := higham_problem9_14_pairwiseBubbleRow (m := m) 1)
      hp j

/-- **Problem 9.14 / pairwise pivoting**, after two scheduled adjacent bubble
steps, the original first row of a pre-pivoted input has moved into row
`m-2`.  This packages the previously proved two-step row-motion lemma in the
explicit recursive schedule. -/
theorem higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_two_pivot_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (hm : 1 < m) (j : Fin (m + 1)) :
    higham_problem9_14_pairwiseBubbleMatrix A 2
        (higham_problem9_14_pairwiseBubbleRow (m := m) 2) j =
      A 0 j := by
  let r0 : Fin (m + 1) := higham_problem9_14_pairwiseBubbleRow (m := m) 0
  let r1 : Fin (m + 1) := higham_problem9_14_pairwiseBubbleRow (m := m) 1
  let r2 : Fin (m + 1) := higham_problem9_14_pairwiseBubbleRow (m := m) 2
  have h0m : 0 < m := lt_trans Nat.zero_lt_one hm
  have hp : r1 ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    simpa [r1] using
      higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := 0) h0m
  have h21 : r2 ≠ r1 := by
    simpa [r1, r2] using
      higham_problem9_14_pairwiseBubbleRows_distinct (m := m) (t := 1) hm
  have h2last : r2 ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    intro h
    have hval := congrArg Fin.val h
    simp [r2, higham_problem9_14_pairwiseBubbleRow] at hval
    omega
  simpa [higham_problem9_14_pairwiseBubbleMatrix_succ,
    higham_problem9_14_pairwiseBubbleMatrix_zero, r0, r1, r2] using
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row
      (A := A) hpre (p := r1) (i := r2) hp h21 h2last j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: explicit
target-row update for the first-column pair pivot-and-eliminate step.  After
the last row of `ΠA` is moved into the left pivot slot, the target row carries
the original left-row data and is updated by the original first row of `A`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) j =
      higham_problem9_14_rowReversedMatrix A p j -
        (higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j := by
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hsel :
      higham_problem9_14_pairPivotRow
          (higham_problem9_14_rowReversedMatrix A) 0 p last = last := by
    simpa [last] using
      higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
        hpre p
  have hnot :
      higham_problem9_14_pairPivotRow
          (higham_problem9_14_rowReversedMatrix A) 0 p last ≠ p := by
    intro h
    exact hp (h.symm.trans hsel)
  have hnot' :
      higham_problem9_14_pairPivotRow
          (higham9_2_rowPermutedMatrix A higham_problem9_14_rowReversal)
          0 p last ≠ p := by
    simpa [higham_problem9_14_rowReversedMatrix] using hnot
  have hlast :
      higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
    subst last
    ext
    simp [higham_problem9_14_rowReversal]
  rw [higham_problem9_14_pairPivotEliminateToLeft_target]
  subst last
  simp [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, hnot',
    higham_problem9_14_pairRowSwap, higham_problem9_14_rowReversedMatrix, hlast]

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the same
first-column pair pivot-and-eliminate step zeros the compared last row's active
entry. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_active_eq_zero
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    (p : Fin (m + 1)) :
    higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0 = 0 := by
  have hsel :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
      hpre p
  have hpivot :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).2
  exact
    higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero
      (higham_problem9_14_rowReversedMatrix A)
      (by simpa [hsel] using hpivot)

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the multiplier
used by that first-column pair pivot-and-eliminate step has magnitude at most
one. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_multiplier_abs_le_one
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |(higham_problem9_14_pairPivotToLeftMatrix
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) 0 /
      higham_problem9_14_pairPivotToLeftMatrix
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) p 0)| ≤ 1 := by
  have hsel :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
      hpre p
  have hpivot :=
    (higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot
      hpre).2
  exact
    higham_problem9_14_pairPivotEliminateToLeft_multiplier_abs_le_one
      (A := higham_problem9_14_rowReversedMatrix A) (k := 0) (p := p)
      (q := (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) hp
      (by simpa [hsel] using hpivot)

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the
first-column multiplier can be read in the normalized source coordinates as
`(ΠA) p 0 / A 0 0`, and has magnitude at most one. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_normalized_multiplier_abs_le_one
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0)| ≤ 1 := by
  have hmul :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_multiplier_abs_le_one
      hpre hp
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  have hlast :
      higham_problem9_14_rowReversal last = (0 : Fin (m + 1)) := by
    subst last
    ext
    simp [higham_problem9_14_rowReversal]
  have hsel :
      higham_problem9_14_pairPivotRow
          (higham_problem9_14_rowReversedMatrix A) 0 p last = last := by
    simpa [last] using
      higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last
        hpre p
  have hnot :
      higham_problem9_14_pairPivotRow
          (higham9_2_rowPermutedMatrix A higham_problem9_14_rowReversal)
          0 p last ≠ p := by
    intro h
    exact hp
      (h.symm.trans (by
        simpa [higham_problem9_14_rowReversedMatrix] using hsel))
  subst last
  simpa [higham_problem9_14_pairPivotToLeftMatrix, higham9_2_rowPermutedMatrix,
    higham_problem9_14_pairPivotToLeftSwap, hnot,
    higham_problem9_14_pairRowSwap, higham_problem9_14_rowReversedMatrix, hlast] using
    hmul

/-- **Problem 9.14**, row reversal preserves the max-entry norm used in the
growth-factor statements. -/
theorem higham_problem9_14_rowReversedMatrix_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A) =
      maxEntryNorm hn A := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne
          (fun j => |higham_problem9_14_rowReversedMatrix A i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix]
      using entry_le_maxEntryNorm hn A (higham_problem9_14_rowReversal i) j
  · change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [higham_problem9_14_rowReversedMatrix, higham9_2_rowPermutedMatrix,
      higham_problem9_14_rowReversal_involutive] using
      entry_le_maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A)
        (higham_problem9_14_rowReversal i) j

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: one
first-column pair pivot-and-eliminate step changes the target row by at most a
factor-two max-entry bound.  This is the one-step growth estimate needed by
the row-reversal/pairwise-pivoting trace equivalence. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_abs_le_two
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (j : Fin (m + 1)) :
    |higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) j| ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  have hformula :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row
      hpre hp j
  have hentry :
      |higham_problem9_14_rowReversedMatrix A p j| ≤ M := by
    simpa [M, higham_problem9_14_rowReversedMatrix_maxEntryNorm
        (Nat.succ_pos m) A] using
      entry_le_maxEntryNorm (Nat.succ_pos m)
        (higham_problem9_14_rowReversedMatrix A) p j
  have hpivotrow : |A 0 j| ≤ M := by
    simpa [M] using entry_le_maxEntryNorm (Nat.succ_pos m) A 0 j
  have hratio :
      |higham_problem9_14_rowReversedMatrix A p 0 / A 0 0| ≤ 1 :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_normalized_multiplier_abs_le_one
      hpre hp
  have hterm :
      |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j| ≤
        M := by
    calc
      |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j|
          = |higham_problem9_14_rowReversedMatrix A p 0 / A 0 0| * |A 0 j| := by
            rw [abs_mul]
      _ ≤ 1 * |A 0 j| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ ≤ 1 * M :=
            mul_le_mul_of_nonneg_left hpivotrow zero_le_one
      _ = M := by ring
  rw [hformula]
  calc
    |higham_problem9_14_rowReversedMatrix A p j -
        (higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j| ≤
        |higham_problem9_14_rowReversedMatrix A p j| +
          |(higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (higham_problem9_14_rowReversedMatrix A p j)
              (-((higham_problem9_14_rowReversedMatrix A p 0 / A 0 0) * A 0 j))
    _ ≤ M + M := add_le_add hentry hterm
    _ = 2 * maxEntryNorm (Nat.succ_pos m) A := by simp [M, two_mul]

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the whole
matrix produced by one first-column pair pivot-and-eliminate step has max-entry
norm bounded by `2 * maxEntryNorm A`.  This packages the target-row bound with
the fact that the other rows are only row-permuted entries of `ΠA`. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_maxEntryNorm_le_two
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    maxEntryNorm (Nat.succ_pos m)
      (higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) ≤
      2 * maxEntryNorm (Nat.succ_pos m) A := by
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
  refine higham9_13_maxEntryNorm_bound_of_entry_bound (Nat.succ_pos m)
    (higham_problem9_14_pairPivotEliminateToLeft
      (higham_problem9_14_rowReversedMatrix A) 0 p last)
    (2 * maxEntryNorm (Nat.succ_pos m) A) ?_
  intro i j
  by_cases hi : i = last
  · subst i
    simpa [last] using
      higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_abs_le_two
        hpre hp j
  · have hrow :=
      higham_problem9_14_pairPivotEliminateToLeft_of_ne
        (A := higham_problem9_14_rowReversedMatrix A) (k := 0) (p := p)
        (q := last) (i := i) (j := j) hi
    rw [hrow]
    have hentry :
        |higham_problem9_14_pairPivotToLeftMatrix
            (higham_problem9_14_rowReversedMatrix A) 0 p last i j| ≤
          M := by
      unfold higham_problem9_14_pairPivotToLeftMatrix
      simpa [M, higham9_2_rowPermutedMatrix,
        higham_problem9_14_rowReversedMatrix_maxEntryNorm
          (Nat.succ_pos m) A] using
        entry_le_maxEntryNorm (Nat.succ_pos m)
          (higham_problem9_14_rowReversedMatrix A)
          (higham_problem9_14_pairPivotToLeftSwap
            (higham_problem9_14_rowReversedMatrix A) 0 p last i) j
    have hM_nonneg : 0 ≤ M := maxEntryNorm_nonneg (Nat.succ_pos m) A
    have hM_le : M ≤ 2 * maxEntryNorm (Nat.succ_pos m) A := by
      dsimp [M] at hM_nonneg ⊢
      nlinarith
    exact le_trans hentry hM_le

/-- **Problem 9.14**, pre-pivoted row-reversal specialization: the one-step
pair pivot-and-eliminate matrix has max-entry growth factor at most two
relative to the row-reversed input.  This is only the first-step quotient; the
cumulative row-reversal/pairwise trace equivalence remains separate. -/
theorem
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_growthFactorEntry_le_two
    {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hpre : higham_problem9_14_PrePivotedGEPP A)
    {p : Fin (m + 1)}
    (hp : p ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    (hAmax : 0 < maxEntryNorm (Nat.succ_pos m) A) :
    growthFactorEntry (Nat.succ_pos m)
      (higham_problem9_14_rowReversedMatrix A)
      (higham_problem9_14_pairPivotEliminateToLeft
        (higham_problem9_14_rowReversedMatrix A) 0 p
        (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
      (by
        simpa [higham_problem9_14_rowReversedMatrix_maxEntryNorm
          (Nat.succ_pos m) A] using hAmax) ≤ 2 := by
  have hmax :=
    higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_maxEntryNorm_le_two
      hpre hp
  unfold growthFactorEntry
  rw [higham_problem9_14_rowReversedMatrix_maxEntryNorm (Nat.succ_pos m) A]
  rwa [div_le_iff₀ hAmax]

/-- **Problem 9.14**, row reversal preserves positivity of the max-entry
denominator used by `growthFactorEntry`. -/
theorem higham_problem9_14_rowReversedMatrix_maxEntryNorm_pos {n : ℕ} (hn : 0 < n)
    {A : Fin n → Fin n → ℝ} (hA : 0 < maxEntryNorm hn A) :
    0 < maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A) := by
  simpa [higham_problem9_14_rowReversedMatrix_maxEntryNorm hn A] using hA

/-- **Problem 9.14**, if a row-reversed input and the original input produce
the same final upper factor, then the max-entry growth-factor quotient has the
same denominator.  This does not assert the missing pivoting trace equivalence;
it is the local norm bridge needed once that trace supplies the common `U`. -/
theorem higham_problem9_14_rowReversedMatrix_growthFactorEntry_eq {n : ℕ}
    (hn : 0 < n) (A U : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A)
    (hRev : 0 < maxEntryNorm hn (higham_problem9_14_rowReversedMatrix A)) :
    growthFactorEntry hn (higham_problem9_14_rowReversedMatrix A) U hRev =
      growthFactorEntry hn A U hA := by
  unfold growthFactorEntry
  rw [higham_problem9_14_rowReversedMatrix_maxEntryNorm hn A]

/-- Prefix dot products from Algorithm 9.2 are bounded by the corresponding
entry of `|L||U|`. -/
theorem higham9_2_rectPrefixDot_abs_le_absLUProduct {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    |higham9_2_rectPrefixDot L U i j k| ≤
      ∑ s : Fin n, |L i s| * |U s j| := by
  unfold higham9_2_rectPrefixDot
  calc
    |∑ s : Fin n, (if s.val < k.val then L i s * U s j else 0)|
        ≤ ∑ s : Fin n, |if s.val < k.val then L i s * U s j else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Fin n, |L i s| * |U s j| := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s.val < k.val
      · simp [hs, abs_mul]
      · simp [hs, mul_nonneg (abs_nonneg (L i s)) (abs_nonneg (U s j))]

/-- A reduced entry from equation (9.5) is bounded by the initial max-entry
norm plus the infinity norm of `|L||U|`. -/
theorem higham9_5_rectGEReducedEntry_abs_le_maxEntryNorm_add_absLU_infNorm
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) (step : Fin n) (i j : Fin n) :
    |higham9_5_rectGEReducedEntry A L U step.val i j| ≤
      maxEntryNorm hn A +
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hprefix :
      |higham9_2_rectPrefixDot L U i j step| ≤ W i j := by
    have hraw := higham9_2_rectPrefixDot_abs_le_absLUProduct L U i j step
    simpa [W, matMul, absMatrix] using hraw
  have hW_nonneg : ∀ p q : Fin n, 0 ≤ W p q := by
    intro p q
    unfold W matMul absMatrix
    exact Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hWij_le_inf : W i j ≤ infNorm W := by
    have hWij_le_row : W i j ≤ ∑ q : Fin n, |W i q| := by
      have hsingle :
          (fun q : Fin n => |W i q|) j ≤
            ∑ q : Fin n, (fun q : Fin n => |W i q|) q :=
        Finset.single_le_sum
          (s := Finset.univ) (f := fun q : Fin n => |W i q|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      simpa [abs_of_nonneg (hW_nonneg i j)] using hsingle
    exact le_trans hWij_le_row (row_sum_le_infNorm W i)
  rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step]
  calc
    |A i j - higham9_2_rectPrefixDot L U i j step|
        ≤ |A i j| + |higham9_2_rectPrefixDot L U i j step| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (A i j) (-(higham9_2_rectPrefixDot L U i j step))
    _ ≤ maxEntryNorm hn A + W i j :=
      add_le_add (entry_le_maxEntryNorm hn A i j) hprefix
    _ ≤ maxEntryNorm hn A + infNorm W :=
      add_le_add (le_refl _) hWij_le_inf

/-- **Equation (9.5)** after all `n` rank-one updates: the natural-number
prefix is the full `L*U` entry. -/
theorem higham9_5_rectPrefixRange_full_eq_matMul {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i j : Fin n) :
    higham9_5_rectPrefixRange L U i j n =
      ∑ k : Fin n, L i k * U k j := by
  unfold higham9_5_rectPrefixRange
  let g : ℕ → ℝ := fun r =>
    if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0
  calc
    (∑ r ∈ Finset.range n,
        if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0)
        = ∑ r ∈ Finset.range n, g r := rfl
    _ = ∑ k : Fin n, g k.val := by
        rw [← Fin.sum_univ_eq_sum_range g n]
    _ = ∑ k : Fin n, L i k * U k j := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : (⟨k.val, k.isLt⟩ : Fin n) = k := by ext; rfl
        simp [g, k.isLt, hk]

/-- **Equation (9.5)** after all `n` rectangular rank-one updates: the
natural-number prefix is the full rectangular product entry. -/
theorem higham9_5_rectPrefixRange_full_eq_rectMatMul {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectPrefixRange L U i j n =
      rectMatMul L U i j := by
  unfold higham9_5_rectPrefixRange rectMatMul
  let g : ℕ → ℝ := fun r =>
    if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0
  calc
    (∑ r ∈ Finset.range n,
        if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0)
        = ∑ r ∈ Finset.range n, g r := rfl
    _ = ∑ k : Fin n, g k.val := by
        rw [← Fin.sum_univ_eq_sum_range g n]
    _ = ∑ k : Fin n, L i k * U k j := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : (⟨k.val, k.isLt⟩ : Fin n) = k := by ext; rfl
        simp [g, k.isLt, hk]

/-- **Equation (9.5)** rectangular prefix saturation: once the natural-number
schedule has performed at least `n` rank-one updates, all later summands are
zero and the prefix is the full rectangular product entry. -/
theorem higham9_5_rectPrefixRange_eq_rectMatMul_of_ge {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) {steps : ℕ} (hsteps : n ≤ steps) :
    higham9_5_rectPrefixRange L U i j steps =
      rectMatMul L U i j := by
  unfold higham9_5_rectPrefixRange rectMatMul
  let f : ℕ → ℝ := fun r =>
    if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0
  have hsubset : Finset.range n ⊆ Finset.range steps := by
    intro r hr
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp hr) hsteps)
  have hsum :
      (∑ r ∈ Finset.range steps, f r) = ∑ r ∈ Finset.range n, f r := by
    symm
    refine Finset.sum_subset hsubset ?_
    intro r _ hrNotN
    have hnot : ¬ r < n := by
      intro hrn
      exact hrNotN (Finset.mem_range.mpr hrn)
    simp [f, hnot]
  calc
    (∑ r ∈ Finset.range steps,
        if h : r < n then L i ⟨r, h⟩ * U ⟨r, h⟩ j else 0)
        = ∑ r ∈ Finset.range steps, f r := rfl
    _ = ∑ r ∈ Finset.range n, f r := hsum
    _ = ∑ k : Fin n, f k.val := by
        rw [← Fin.sum_univ_eq_sum_range f n]
    _ = ∑ k : Fin n, L i k * U k j := by
        apply Finset.sum_congr rfl
        intro k _
        have hk : (⟨k.val, k.isLt⟩ : Fin n) = k := by ext; rfl
        simp [f, k.isLt, hk]

/-- **Equation (9.5)** square prefix saturation: once the natural-number
schedule has performed at least `n` rank-one updates, the prefix is the full
`L*U` entry. -/
theorem higham9_5_rectPrefixRange_eq_matMul_of_ge {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i j : Fin n)
    {steps : ℕ} (hsteps : n ≤ steps) :
    higham9_5_rectPrefixRange L U i j steps =
      ∑ k : Fin n, L i k * U k j := by
  simpa [rectMatMul] using
    higham9_5_rectPrefixRange_eq_rectMatMul_of_ge L U i j hsteps

/-- **Equation (9.5)** terminal rectangular residual: after all rank-one
updates, the reduced entry is exactly the residual `A - L*U`. -/
theorem higham9_5_rectGEReducedEntry_full_eq_sub_rectMatMul {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U n i j =
      A i j - rectMatMul L U i j := by
  unfold higham9_5_rectGEReducedEntry
  rw [higham9_5_rectPrefixRange_full_eq_rectMatMul]

/-- **Equation (9.5)** rectangular residual saturation: after at least `n`
rank-one updates, the reduced entry is exactly the residual `A - L*U`. -/
theorem higham9_5_rectGEReducedEntry_eq_sub_rectMatMul_of_ge {m n : ℕ}
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) {steps : ℕ} (hsteps : n ≤ steps) :
    higham9_5_rectGEReducedEntry A L U steps i j =
      A i j - rectMatMul L U i j := by
  unfold higham9_5_rectGEReducedEntry
  rw [higham9_5_rectPrefixRange_eq_rectMatMul_of_ge L U i j hsteps]

/-- **Equation (9.5)** square residual saturation: after at least `n`
rank-one updates, the reduced entry is exactly the residual `A - L*U`. -/
theorem higham9_5_rectGEReducedEntry_eq_sub_matMul_of_ge {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (i j : Fin n)
    {steps : ℕ} (hsteps : n ≤ steps) :
    higham9_5_rectGEReducedEntry A L U steps i j =
      A i j - ∑ k : Fin n, L i k * U k j := by
  simpa [rectMatMul] using
    higham9_5_rectGEReducedEntry_eq_sub_rectMatMul_of_ge
      A L U i j hsteps

/-- **Equation (9.5)** terminal rectangular residual: for an exact rectangular
product certificate, the reduced entry after all rank-one updates is zero. -/
theorem higham9_5_rectGEReducedEntry_full_eq_zero_of_rectMatMul_eq {m n : ℕ}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hprod : ∀ i j, rectMatMul L U i j = A i j)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U n i j = 0 := by
  rw [higham9_5_rectGEReducedEntry_full_eq_sub_rectMatMul A L U i j,
    hprod i j]
  ring

/-- **Equation (9.5) / Algorithm 9.2**, terminal rectangular residual from
exact Doolittle recurrences.  Exact upper/lower recurrence equations, together
with the triangular shape and nonzero computed pivots, imply that after all
rectangular rank-one updates the reduced matrix is zero. -/
theorem higham9_5_rectGEReducedEntry_full_eq_zero_of_rectDoolittle_exact_recurrences
    {m n : ℕ} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U n i j = 0 :=
  higham9_5_rectGEReducedEntry_full_eq_zero_of_rectMatMul_eq
    (higham9_2_rectDoolittle_exact_recurrences_rectMatMul_eq
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag)
    i j

/-- **Equation (9.5)** saturated rectangular residual: for an exact rectangular
product certificate, every reduced entry at a step count `>= n` is zero. -/
theorem higham9_5_rectGEReducedEntry_eq_zero_of_rectMatMul_eq_of_ge
    {m n : ℕ} {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {steps : ℕ} (hsteps : n ≤ steps)
    (hprod : ∀ i j, rectMatMul L U i j = A i j)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U steps i j = 0 := by
  rw [higham9_5_rectGEReducedEntry_eq_sub_rectMatMul_of_ge
    A L U i j hsteps, hprod i j]
  ring

/-- **Equation (9.5) / Algorithm 9.2**, saturated rectangular residual from
exact Doolittle recurrences.  Once the natural-number schedule has executed at
least `n` rank-one updates, the reduced matrix is zero under the exact
rectangular Doolittle recurrence certificate. -/
theorem higham9_5_rectGEReducedEntry_eq_zero_of_rectDoolittle_exact_recurrences_of_ge
    {m n : ℕ} {hmn : n ≤ m}
    {A L : Fin m → Fin n → ℝ} {U : Fin n → Fin n → ℝ}
    {steps : ℕ} (hsteps : n ≤ steps)
    (hL_diag : ∀ k : Fin n, L (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate hmn A L U k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0)
    (i : Fin m) (j : Fin n) :
    higham9_5_rectGEReducedEntry A L U steps i j = 0 :=
  higham9_5_rectGEReducedEntry_eq_zero_of_rectMatMul_eq_of_ge hsteps
    (higham9_2_rectDoolittle_exact_recurrences_rectMatMul_eq
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag)
    i j

/-- **Equation (9.5)** terminal residual: for an exact LU certificate, the
reduced entry after all rank-one updates is zero. -/
theorem higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) (i j : Fin n) :
    higham9_5_rectGEReducedEntry A L U n i j = 0 := by
  unfold higham9_5_rectGEReducedEntry
  rw [higham9_5_rectPrefixRange_full_eq_matMul L U i j, hLU.product_eq i j]
  ring

/-- **Equation (9.5)** saturated terminal residual: for an exact square LU
certificate, every reduced entry at a step count `>= n` is zero. -/
theorem higham9_5_rectGEReducedEntry_eq_zero_of_LUFactSpec_of_ge {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} {steps : ℕ}
    (hsteps : n ≤ steps) (hLU : LUFactSpec n A L U) (i j : Fin n) :
    higham9_5_rectGEReducedEntry A L U steps i j = 0 := by
  rw [higham9_5_rectGEReducedEntry_eq_sub_matMul_of_ge A L U i j hsteps,
    hLU.product_eq i j]
  ring

/-- **Lemma 9.6**, local rank-one stage estimate: the `k`th absolute LU
outer-product entry is bounded by the neighboring exact no-pivot reduced
matrices from equation (9.5). -/
theorem higham9_6_rankOne_abs_le_reduced_add_succ {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (k : Fin n) (i j : Fin n) :
    |L i k * U k j| ≤
      |higham9_5_rectGEReducedEntry A L U k.val i j| +
        |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j| := by
  have hrec :=
    higham9_5_rectGEReducedEntry_succ_of_lt A L U k.val k.isLt i j
  have hk : (⟨k.val, k.isLt⟩ : Fin n) = k := by ext; rfl
  rw [hk] at hrec
  have hterm :
      L i k * U k j =
        higham9_5_rectGEReducedEntry A L U k.val i j -
          higham9_5_rectGEReducedEntry A L U (k.val + 1) i j := by
    linarith
  rw [hterm]
  simpa [sub_eq_add_neg, abs_neg] using
    abs_add_le
      (higham9_5_rectGEReducedEntry A L U k.val i j)
      (-(higham9_5_rectGEReducedEntry A L U (k.val + 1) i j))

/-- **Lemma 9.6**, stage-pair row-sum bridge: once the neighboring reduced
matrix rows from equation (9.5) have the source row-sum budget, the absolute
LU product has the corresponding infinity-norm budget. -/
theorem higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (C : ℝ)
    (hrows : ∀ i : Fin n,
      ∑ k : Fin n, ∑ j : Fin n,
        (|higham9_5_rectGEReducedEntry A L U k.val i j| +
          |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) ≤ C)
    (hC : 0 ≤ C) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤ C := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    unfold W matMul absMatrix
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |W i j|
          = ∑ j : Fin n, W i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hW_nonneg i j)]
      _ = ∑ j : Fin n, ∑ k : Fin n, |L i k| * |U k j| := by
            simp [W, matMul, absMatrix]
      _ = ∑ j : Fin n, ∑ k : Fin n, |L i k * U k j| := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
      _ ≤ ∑ j : Fin n, ∑ k : Fin n,
            (|higham9_5_rectGEReducedEntry A L U k.val i j| +
              |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) := by
            apply Finset.sum_le_sum
            intro j _
            apply Finset.sum_le_sum
            intro k _
            exact higham9_6_rankOne_abs_le_reduced_add_succ A L U k i j
      _ = ∑ k : Fin n, ∑ j : Fin n,
            (|higham9_5_rectGEReducedEntry A L U k.val i j| +
              |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) := by
            rw [Finset.sum_comm]
      _ ≤ C := hrows i
  · exact hC

/-- **Lemma 9.6**, row-budget accumulation form: a uniform row-sum budget for
each exact reduced stage in equation (9.5), including the terminal stage,
implies the corresponding `|L||U|` infinity-norm budget. -/
theorem higham9_6_absLU_infNorm_le_two_card_mul_of_reduced_stage_row_bounds {n : ℕ}
    (A L U : Fin n → Fin n → ℝ) (C : ℝ)
    (hstageRows : ∀ step : ℕ, step ≤ n →
      ∀ i : Fin n,
        ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U step i j| ≤ C)
    (hC : 0 ≤ C) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      (2 * (n : ℝ)) * C := by
  apply higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows
    A L U ((2 * (n : ℝ)) * C)
  · intro i
    have hfirst :
        (∑ k : Fin n,
          ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U k.val i j|) ≤
          ∑ _k : Fin n, C := by
      apply Finset.sum_le_sum
      intro k _
      exact hstageRows k.val (le_of_lt k.isLt) i
    have hsecond :
        (∑ k : Fin n,
          ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) ≤
          ∑ _k : Fin n, C := by
      apply Finset.sum_le_sum
      intro k _
      exact hstageRows (k.val + 1) (Nat.succ_le_of_lt k.isLt) i
    calc
      ∑ k : Fin n, ∑ j : Fin n,
          (|higham9_5_rectGEReducedEntry A L U k.val i j| +
            |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|)
          = (∑ k : Fin n,
              ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U k.val i j|) +
            (∑ k : Fin n,
              ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_add_distrib]
      _ ≤ (∑ _k : Fin n, C) + ∑ _k : Fin n, C :=
            add_le_add hfirst hsecond
      _ = (2 * (n : ℝ)) * C := by
            simp [Fintype.card_fin]
            ring
  · exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hC

/-- **Lemma 9.6**, finite stage counting: summing neighboring exact reduced
stages counts the initial and terminal stages once and all intermediate stages
twice.  This is the bookkeeping step behind Higham's
`|A| + 2 ∑_{k=2}^n |A^(k)|` line. -/
theorem higham9_6_sum_stage_pair_eq_endpoints_add_two_range {n : ℕ}
    (hn : 0 < n) (row : ℕ → ℝ) :
    (∑ k : Fin n, (row k.val + row (k.val + 1))) =
      row 0 + row n + 2 * ∑ r ∈ Finset.range (n - 1), row (r + 1) := by
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  have hsum_fin :
      (∑ k : Fin n, (row k.val + row (k.val + 1))) =
        ∑ k ∈ Finset.range n, (row k + row (k + 1)) := by
    simpa using
      (Fin.sum_univ_eq_sum_range (fun k : ℕ => row k + row (k + 1)) n)
  have hfirst :
      (∑ k ∈ Finset.range n, row k) =
        row 0 + ∑ r ∈ Finset.range (n - 1), row (r + 1) := by
    conv_lhs => rw [← hn_eq]
    rw [Finset.sum_range_succ']
    ring
  have hsecond :
      (∑ k ∈ Finset.range n, row (k + 1)) =
        (∑ r ∈ Finset.range (n - 1), row (r + 1)) + row n := by
    conv_lhs => rw [← hn_eq]
    rw [Finset.sum_range_succ]
    simp [hn_eq]
  rw [hsum_fin, Finset.sum_add_distrib, hfirst, hsecond]
  ring

/-- **Lemma 9.6**, source counting budget with an explicit reduced-stage
growth hypothesis.  If every intermediate reduced stage has entries bounded by
`rho * maxEntryNorm A`, then the already proved rank-one stage estimate gives
Higham's printed infinity-norm constant. -/
theorem higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ) (rho : ℝ)
    (hLU : LUFactSpec n A L U)
    (hrho : 0 ≤ rho)
    (hstage : ∀ step : ℕ, 1 ≤ step → step < n →
      ∀ i j : Fin n,
        |higham9_5_rectGEReducedEntry A L U step i j| ≤
          rho * maxEntryNorm hn A) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      (1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho) * infNorm A := by
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hn
  have hcast_pred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hn_minus_nonneg : 0 ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn1)
  have hcoef_nonneg :
      0 ≤ 1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hquad_nonneg : 0 ≤ (n : ℝ) ^ 2 - (n : ℝ) := by
      have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
        mul_nonneg hn_nonneg hn_minus_nonneg
      nlinarith [hprod]
    have hterm : 0 ≤ 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho :=
      mul_nonneg (mul_nonneg (by norm_num) hquad_nonneg) hrho
    exact add_nonneg zero_le_one hterm
  apply higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows
    A L U ((1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho) * infNorm A)
  · intro i
    let row : ℕ → ℝ := fun step =>
      ∑ j : Fin n, |higham9_5_rectGEReducedEntry A L U step i j|
    have hpair :
        (∑ k : Fin n,
          ∑ j : Fin n,
            (|higham9_5_rectGEReducedEntry A L U k.val i j| +
              |higham9_5_rectGEReducedEntry A L U (k.val + 1) i j|)) =
          ∑ k : Fin n, (row k.val + row (k.val + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [row, Finset.sum_add_distrib]
    have hcount := higham9_6_sum_stage_pair_eq_endpoints_add_two_range hn row
    have hrow0 : row 0 = ∑ j : Fin n, |A i j| := by
      apply Finset.sum_congr rfl
      intro j _
      simp [higham9_5_rectGEReducedEntry_zero]
    have hrow0_le : row 0 ≤ infNorm A := by
      rw [hrow0]
      exact row_sum_le_infNorm A i
    have hrown : row n = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec hLU]
    have hrow_intermediate :
        ∑ r ∈ Finset.range (n - 1), row (r + 1) ≤
          ∑ _r ∈ Finset.range (n - 1), (n : ℝ) * rho * infNorm A := by
      apply Finset.sum_le_sum
      intro r hr
      have hr_lt_pred : r < n - 1 := Finset.mem_range.mp hr
      have hstep_lt : r + 1 < n := by omega
      have hrow_to_max :
          row (r + 1) ≤ ∑ _j : Fin n, rho * maxEntryNorm hn A := by
        apply Finset.sum_le_sum
        intro j _
        exact hstage (r + 1) (Nat.succ_le_succ (Nat.zero_le r)) hstep_lt i j
      have hmax_to_inf :
          (n : ℝ) * rho * maxEntryNorm hn A ≤ (n : ℝ) * rho * infNorm A := by
        exact mul_le_mul_of_nonneg_left (maxEntryNorm_le_infNorm hn A)
          (mul_nonneg (Nat.cast_nonneg n) hrho)
      calc
        row (r + 1) ≤ ∑ _j : Fin n, rho * maxEntryNorm hn A := hrow_to_max
        _ = (n : ℝ) * rho * maxEntryNorm hn A := by
            simp [Fintype.card_fin]
            ring
        _ ≤ (n : ℝ) * rho * infNorm A := hmax_to_inf
    have hsum_const :
        (∑ _r ∈ Finset.range (n - 1), (n : ℝ) * rho * infNorm A) =
          ((n - 1 : ℕ) : ℝ) * ((n : ℝ) * rho * infNorm A) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hpair, hcount]
    calc
      row 0 + row n + 2 * ∑ r ∈ Finset.range (n - 1), row (r + 1)
          ≤ infNorm A + 0 +
              2 * (((n - 1 : ℕ) : ℝ) * ((n : ℝ) * rho * infNorm A)) := by
            apply add_le_add
            · exact add_le_add hrow0_le (by rw [hrown])
            · exact mul_le_mul_of_nonneg_left
                (le_trans hrow_intermediate (le_of_eq hsum_const)) (by norm_num)
      _ = (1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) * rho) * infNorm A := by
            rw [hcast_pred]
            ring
  · exact mul_nonneg hcoef_nonneg (infNorm_nonneg A)

/-- **Problem 9.9**, the source max over exact no-pivot reduced matrices
`A^(1), ..., A^(n)`, represented as equation (9.5) stages `0, ..., n-1`. -/
noncomputable def higham_problem9_9_noPivotReducedEntryMax {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun step : Fin n =>
      maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step.val i j))

/-- **Problem 9.9**, source no-pivot growth factor over all exact reduced
matrices generated by equation (9.5). -/
noncomputable def higham_problem9_9_noPivotReducedGrowthFactor {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (_hAmax : 0 < maxEntryNorm hn A) : ℝ :=
  higham_problem9_9_noPivotReducedEntryMax hn A L U / maxEntryNorm hn A

/-- **Problem 9.6 / equation (9.5)** support: a no-pivot prefix product is
nonnegative when both exact factors are componentwise nonnegative. -/
theorem higham9_5_rectPrefixRange_nonneg_of_nonnegative_factors {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (hL_nn : ∀ i k, 0 ≤ L i k) (hU_nn : ∀ k j, 0 ≤ U k j)
    (i : Fin m) (j : Fin n) (steps : ℕ) :
    0 ≤ higham9_5_rectPrefixRange L U i j steps := by
  unfold higham9_5_rectPrefixRange
  apply Finset.sum_nonneg
  intro r _hr
  by_cases hrn : r < n
  · simpa [hrn] using mul_nonneg (hL_nn i ⟨r, hrn⟩) (hU_nn ⟨r, hrn⟩ j)
  · simp [hrn]

/-- **Problem 9.6 / equation (9.5)** support: under componentwise nonnegative
exact factors, every no-pivot prefix is bounded by the full product prefix. -/
theorem higham9_5_rectPrefixRange_le_full_of_nonnegative_factors {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (hL_nn : ∀ i k, 0 ≤ L i k) (hU_nn : ∀ k j, 0 ≤ U k j)
    (i : Fin m) (j : Fin n) {steps : ℕ} (hsteps : steps ≤ n) :
    higham9_5_rectPrefixRange L U i j steps ≤
      higham9_5_rectPrefixRange L U i j n := by
  unfold higham9_5_rectPrefixRange
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) hsteps)
  · intro r _hrn hrsteps
    by_cases hrn : r < n
    · simpa [hrn] using mul_nonneg (hL_nn i ⟨r, hrn⟩) (hU_nn ⟨r, hrn⟩ j)
    · simp [hrn]

/-- **Problem 9.6**, exact reduced-entry no-growth from a nonnegative
no-pivot LU certificate.  Each reduced entry in equation (9.5) is the
nonnegative tail of the exact product `A = L*U`, hence its absolute value is
bounded by the corresponding source entry. -/
theorem higham9_6_reducedEntry_abs_le_maxEntryNorm_of_nonnegative_LU {n : ℕ}
    (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k, 0 ≤ L i k)
    (hU_nn : ∀ k j, 0 ≤ U k j)
    (step : Fin n) (i j : Fin n) :
    |higham9_5_rectGEReducedEntry A L U step.val i j| ≤ maxEntryNorm hn A := by
  have hprefix_nonneg :
      0 ≤ higham9_5_rectPrefixRange L U i j step.val :=
    higham9_5_rectPrefixRange_nonneg_of_nonnegative_factors
      L U hL_nn hU_nn i j step.val
  have hprefix_le_full :
      higham9_5_rectPrefixRange L U i j step.val ≤
        higham9_5_rectPrefixRange L U i j n :=
    higham9_5_rectPrefixRange_le_full_of_nonnegative_factors
      L U hL_nn hU_nn i j (le_of_lt step.isLt)
  have hfull_eq :
      higham9_5_rectPrefixRange L U i j n = A i j := by
    rw [higham9_5_rectPrefixRange_full_eq_matMul L U i j, hLU.product_eq i j]
  have hA_nonneg : 0 ≤ A i j := by
    rw [← hfull_eq]
    exact higham9_5_rectPrefixRange_nonneg_of_nonnegative_factors
      L U hL_nn hU_nn i j n
  have hred_nonneg :
      0 ≤ higham9_5_rectGEReducedEntry A L U step.val i j := by
    unfold higham9_5_rectGEReducedEntry
    rw [← hfull_eq]
    exact sub_nonneg.mpr hprefix_le_full
  have hred_le_A :
      higham9_5_rectGEReducedEntry A L U step.val i j ≤ A i j := by
    unfold higham9_5_rectGEReducedEntry
    exact sub_le_self _ hprefix_nonneg
  calc
    |higham9_5_rectGEReducedEntry A L U step.val i j|
        = higham9_5_rectGEReducedEntry A L U step.val i j :=
          abs_of_nonneg hred_nonneg
    _ ≤ A i j := hred_le_A
    _ = |A i j| := (abs_of_nonneg hA_nonneg).symm
    _ ≤ maxEntryNorm hn A := entry_le_maxEntryNorm hn A i j

/-- **Problem 9.6**, source reduced-matrix growth endpoint from a nonnegative
no-pivot LU certificate: the max-entry growth factor over all exact reduced
matrices in equation (9.5) is at most one. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k, 0 ≤ L i k)
    (hU_nn : ∀ k j, 0 ≤ U k j)
    (hAmax : 0 < maxEntryNorm hn A) :
    higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 1 := by
  have hentryMax_le :
      higham_problem9_9_noPivotReducedEntryMax hn A L U ≤ maxEntryNorm hn A := by
    unfold higham_problem9_9_noPivotReducedEntryMax
    apply Finset.sup'_le
    intro step _hstep
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _hi
    apply Finset.sup'_le
    intro j _hj
    exact higham9_6_reducedEntry_abs_le_maxEntryNorm_of_nonnegative_LU
      hn hLU hL_nn hU_nn step i j
  unfold higham_problem9_9_noPivotReducedGrowthFactor
  rw [div_le_iff₀ hAmax]
  simpa using hentryMax_le

/-- A nonsingular source matrix has positive matrix infinity norm. -/
theorem higham9_infNorm_pos_of_det_ne_zero {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 < infNorm A :=
  lt_of_lt_of_le (maxEntryNorm_pos_of_det_ne_zero hn A hdet)
    (maxEntryNorm_le_infNorm hn A)

/-- **Problem 9.6 / Problem 9.9**, nonnegative no-pivot LU reduced-growth
endpoint with the positive source denominator derived from nonsingularity. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hL_nn : ∀ i k, 0 ≤ L i k)
    (hU_nn : ∀ k j, 0 ≤ U k j)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 1 := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU
        hn hLU hL_nn hU_nn hAmax⟩

/-- **Lemma 9.6**, source-constant form using the no-pivot reduced growth
factor from Problem 9.9.  This packages the explicit reduced-stage growth
hypothesis of `higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth`
with the actual max over equation (9.5) reduced matrices. -/
theorem higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor
    {n : ℕ} (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A) :
    infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
      (1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) *
        higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax) *
        infNorm A := by
  have hmax_nonneg :
      0 ≤ higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    let step0 : Fin n := ⟨0, hn⟩
    have hstage0_nonneg :
        0 ≤ maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step0.val i j) :=
      maxEntryNorm_nonneg hn _
    have hstage0_le :
        maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step0.val i j) ≤
          higham_problem9_9_noPivotReducedEntryMax hn A L U := by
      unfold higham_problem9_9_noPivotReducedEntryMax
      exact Finset.le_sup' (fun step : Fin n =>
        maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step.val i j))
        (Finset.mem_univ step0)
    exact le_trans hstage0_nonneg hstage0_le
  have hgrowth_nonneg :
      0 ≤ higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax := by
    unfold higham_problem9_9_noPivotReducedGrowthFactor
    exact div_nonneg hmax_nonneg (le_of_lt hAmax)
  apply higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth
    hn A L U (higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax)
    hLU hgrowth_nonneg
  intro step _hstep_pos hstep_lt i j
  let stepFin : Fin n := ⟨step, hstep_lt⟩
  have hentry_le_stage :
      |higham9_5_rectGEReducedEntry A L U step i j| ≤
        maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U stepFin.val i j) := by
    simpa [stepFin] using
      entry_le_maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U stepFin.val i j)
        i j
  have hstage_le_max :
      maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U stepFin.val i j) ≤
        higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    unfold higham_problem9_9_noPivotReducedEntryMax
    exact Finset.le_sup' (fun step : Fin n =>
      maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U step.val i j))
      (Finset.mem_univ stepFin)
  have hmul_eq :
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax *
          maxEntryNorm hn A =
        higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    unfold higham_problem9_9_noPivotReducedGrowthFactor
    field_simp [ne_of_gt hAmax]
  calc
    |higham9_5_rectGEReducedEntry A L U step i j|
        ≤ higham_problem9_9_noPivotReducedEntryMax hn A L U :=
          le_trans hentry_le_stage hstage_le_max
    _ = higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax *
          maxEntryNorm hn A := by
          rw [← hmul_eq]

/-- **Lemma 9.6**, source-constant form with the positive max-entry
denominator in `rho_n` derived from source nonsingularity. -/
theorem higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax
    {n : ℕ} (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      infNorm (matMul n (absMatrix n L) (absMatrix n U)) ≤
        (1 + 2 * ((n : ℝ) ^ 2 - (n : ℝ)) *
          higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax) *
          infNorm A := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor
        hn A L U hLU hAmax⟩

/-- **Problem 9.9**, stage-max form before division by the initial matrix
size: every exact no-pivot reduced matrix from equation (9.5) is bounded by
`max |A| + || |L||U| ||_∞`. -/
theorem higham_problem9_9_noPivotReducedEntryMax_le_maxEntryNorm_add_absLU_infNorm
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ) :
    higham_problem9_9_noPivotReducedEntryMax hn A L U ≤
      maxEntryNorm hn A +
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) := by
  unfold higham_problem9_9_noPivotReducedEntryMax
  apply Finset.sup'_le
  intro step _
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham9_5_rectGEReducedEntry_abs_le_maxEntryNorm_add_absLU_infNorm
    hn A L U step i j

/-- **Problem 9.9**, source-facing exact no-pivot reduced-matrix growth bound:
`rho_n <= 1 + n * || |L||U| ||_inf / ||A||_inf`.

Here `rho_n` is formalized as the maximum, over the exact reduced matrices in
equation (9.5), of the max-entry size divided by the initial max-entry size. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A)
    (hAinf : 0 < infNorm A) :
    higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤
      1 + (n : ℝ) *
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) / infNorm A := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L) (absMatrix n U)
  have hentryMax :
      higham_problem9_9_noPivotReducedEntryMax hn A L U ≤
        maxEntryNorm hn A + infNorm W := by
    simpa [W] using
      higham_problem9_9_noPivotReducedEntryMax_le_maxEntryNorm_add_absLU_infNorm
        hn A L U
  have hdivMax :
      higham_problem9_9_noPivotReducedEntryMax hn A L U / maxEntryNorm hn A ≤
        (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A :=
    div_le_div_of_nonneg_right hentryMax (le_of_lt hAmax)
  have hdivBound :
      (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A ≤
        1 + (n : ℝ) * infNorm W / infNorm A := by
    have hWnorm_nonneg : 0 ≤ infNorm W := infNorm_nonneg W
    have hmax_ne : maxEntryNorm hn A ≠ 0 := ne_of_gt hAmax
    have hW_div :
        infNorm W / maxEntryNorm hn A ≤ (n : ℝ) * infNorm W / infNorm A := by
      have hAinf_le : infNorm A ≤ (n : ℝ) * maxEntryNorm hn A :=
        infNorm_le_card_mul_maxEntryNorm hn A
      have hmul :
          infNorm W * infNorm A ≤
            infNorm W * ((n : ℝ) * maxEntryNorm hn A) :=
        mul_le_mul_of_nonneg_left hAinf_le hWnorm_nonneg
      have hcross :
          infNorm W * infNorm A ≤
            (n : ℝ) * infNorm W * maxEntryNorm hn A := by
        calc
          infNorm W * infNorm A
              ≤ infNorm W * ((n : ℝ) * maxEntryNorm hn A) := hmul
          _ = (n : ℝ) * infNorm W * maxEntryNorm hn A := by ring
      exact (div_le_div_iff₀ hAmax hAinf).mpr hcross
    calc
      (maxEntryNorm hn A + infNorm W) / maxEntryNorm hn A
          = 1 + infNorm W / maxEntryNorm hn A := by
        field_simp [hmax_ne]
      _ ≤ 1 + (n : ℝ) * infNorm W / infNorm A :=
        by simpa [add_comm] using add_le_add_left hW_div 1
  unfold higham_problem9_9_noPivotReducedGrowthFactor
  exact le_trans hdivMax hdivBound

/-- **Problem 9.9**, source-facing exact no-pivot reduced-matrix growth bound
with denominator positivity derived from nonsingularity. -/
theorem higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤
        1 + (n : ℝ) *
          infNorm (matMul n (absMatrix n L) (absMatrix n U)) / infNorm A := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  have hAinf : 0 < infNorm A :=
    higham9_infNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div
        hn A L U hAmax hAinf⟩

/-- **Problem 9.9**, source-facing max-entry growth bound for exact no-pivot
LU factors: `rho_n <= 1 + n * || |L||U| ||_inf / ||A||_inf`.

The remaining algorithmic part of the source problem is the separate proof that
the factors supplied here are exactly those generated by GE without pivoting. -/
theorem higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A)
    (hAinf : 0 < infNorm A) :
    growthFactorEntry hn A U hAmax ≤
      1 + (n : ℝ) *
        infNorm (matMul n (absMatrix n L) (absMatrix n U)) / infNorm A :=
  growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div hn hLU hAmax hAinf

/-- **Problem 9.9**, source-facing exact no-pivot final-`U` growth bound with
denominator positivity derived from nonsingularity. -/
theorem higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hdetA : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      growthFactorEntry hn A U hAmax ≤
        1 + (n : ℝ) *
          infNorm (matMul n (absMatrix n L) (absMatrix n U)) / infNorm A := by
  have hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdetA
  have hAinf : 0 < infNorm A :=
    higham9_infNorm_pos_of_det_ne_zero hn A hdetA
  exact
    ⟨hAmax,
      higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div
        hn hLU hAmax hAinf⟩

/-- **Problem 9.10**, the rank-one matrix `e_i e_j^T` used to model a
single multiplier error as a rank-one perturbation. -/
noncomputable def higham_problem9_10_rankOneBasis {n : ℕ} (i j : Fin n) :
    Fin n → Fin n → ℝ :=
  fun r c => finiteBasisVec i r * finiteBasisVec j c

/-- **Problem 9.10**, the scalar perturbation coefficient
`α = ε * \hat l_ij * \hat u_jj`. -/
noncomputable def higham_problem9_10_multiplierBlunderAlpha
    (epsilon lhatij uhatjj : ℝ) : ℝ :=
  epsilon * lhatij * uhatjj

/-- **Problem 9.10**, matrix-vector action of the rank-one basis
`e_i e_j^T`. -/
theorem higham_problem9_10_rankOneBasis_mulVec {n : ℕ}
    (i j : Fin n) (v : Fin n → ℝ) :
    matMulVec n (higham_problem9_10_rankOneBasis i j) v =
      fun r => finiteBasisVec i r * v j := by
  ext r
  unfold matMulVec higham_problem9_10_rankOneBasis
  have hbasis : (∑ c : Fin n, finiteBasisVec j c * v c) = v j := by
    unfold finiteBasisVec
    rw [Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  calc
    ∑ c : Fin n, (finiteBasisVec i r * finiteBasisVec j c) * v c
        = finiteBasisVec i r * (∑ c : Fin n, finiteBasisVec j c * v c) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ = finiteBasisVec i r * v j := by rw [hbasis]

/-- **Problem 9.10**, matrix-vector action of the perturbed matrix
`A - α e_i e_j^T`. -/
theorem higham_problem9_10_rankOnePerturbed_mulVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (v : Fin n → ℝ) :
    matMulVec n
        (fun r c => A r c - alpha * higham_problem9_10_rankOneBasis i j r c) v =
      fun r => matMulVec n A v r - alpha * finiteBasisVec i r * v j := by
  ext r
  have hrank := congrFun (higham_problem9_10_rankOneBasis_mulVec i j v) r
  have hrank_sum :
      (∑ c : Fin n, higham_problem9_10_rankOneBasis i j r c * v c) =
        finiteBasisVec i r * v j := by
    simpa [matMulVec] using hrank
  unfold matMulVec
  calc
    ∑ c : Fin n,
        (A r c - alpha * higham_problem9_10_rankOneBasis i j r c) * v c
        = (∑ c : Fin n, A r c * v c) -
            ∑ c : Fin n,
              alpha * (higham_problem9_10_rankOneBasis i j r c * v c) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ = (∑ c : Fin n, A r c * v c) -
          alpha *
            (∑ c : Fin n, higham_problem9_10_rankOneBasis i j r c * v c) := by
            rw [Finset.mul_sum]
    _ = (∑ c : Fin n, A r c * v c) -
          alpha * (finiteBasisVec i r * v j) := by
            rw [hrank_sum]
    _ = (∑ c : Fin n, A r c * v c) - alpha * finiteBasisVec i r * v j := by
            ring

/-- **Problem 9.10**, applying an available left inverse to a matrix-vector
equation. -/
theorem higham_problem9_10_apply_left_inverse_of_matMulVec_eq {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (d rhs : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hd : matMulVec n A d = rhs) :
    d = matMulVec n A_inv rhs := by
  have hprod : matMul n A_inv A = idMatrix n := by
    ext r c
    simpa [matMul] using hInv r c
  ext r
  calc
    d r = matMulVec n (idMatrix n) d r := by
      rw [matMulVec_id]
    _ = matMulVec n (matMul n A_inv A) d r := by
      rw [hprod]
    _ = matMulVec n A_inv (matMulVec n A d) r :=
      matMulVec_matMul n A_inv A d r
    _ = matMulVec n A_inv rhs r := by rw [hd]

/-- **Problem 9.10**, multiplying by a vector supported at one standard-basis
coordinate. -/
theorem higham_problem9_10_matMulVec_scaledBasis {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (i : Fin n) (alpha xj : ℝ) :
    matMulVec n A_inv (fun r => alpha * finiteBasisVec i r * xj) =
      fun r => alpha * A_inv r i * xj := by
  ext r
  unfold matMulVec
  rw [Finset.sum_eq_single i]
  · simp [finiteBasisVec]
    ring
  · intro c _ hc
    simp [finiteBasisVec, hc]
  · simp

/-- **Problem 9.10**, source rank-one blunder solution formula.  If the exact
solution satisfies `A x = b` and the computed solution satisfies
`(A - α e_i e_j^T) xhat = b`, then `xhat` is the Sherman-Morrison update
obtained by direct left-inverse algebra. -/
theorem higham_problem9_10_rankOne_blunder_solution {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (b x xhat : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hx : matMulVec n A x = b)
    (hxhat :
      matMulVec n
          (fun r c => A r c - alpha * higham_problem9_10_rankOneBasis i j r c)
          xhat = b)
    (hden : 1 - alpha * A_inv j i ≠ 0) :
    xhat =
      fun r => x r + (alpha * x j / (1 - alpha * A_inv j i)) * A_inv r i := by
  have hxhat_exp := hxhat
  rw [higham_problem9_10_rankOnePerturbed_mulVec] at hxhat_exp
  have hdA :
      matMulVec n A (fun q => xhat q - x q) =
        fun r => alpha * finiteBasisVec i r * xhat j := by
    ext r
    have hxhat_r := congrFun hxhat_exp r
    have hx_r := congrFun hx r
    unfold matMulVec at hxhat_r hx_r ⊢
    calc
      ∑ c : Fin n, A r c * (xhat c - x c)
          = (∑ c : Fin n, A r c * xhat c) -
              (∑ c : Fin n, A r c * x c) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro c _
              ring
      _ = alpha * finiteBasisVec i r * xhat j := by
              nlinarith
  have hd_eq :
      (fun q => xhat q - x q) =
        matMulVec n A_inv (fun r => alpha * finiteBasisVec i r * xhat j) :=
    higham_problem9_10_apply_left_inverse_of_matMulVec_eq A A_inv
      (fun q => xhat q - x q)
      (fun r => alpha * finiteBasisVec i r * xhat j) hInv hdA
  have hscaled := higham_problem9_10_matMulVec_scaledBasis A_inv i alpha (xhat j)
  have hd_entry : ∀ r : Fin n, xhat r - x r = alpha * A_inv r i * xhat j := by
    intro r
    have hr := congrFun hd_eq r
    rw [hscaled] at hr
    exact hr
  have hsolve : xhat j = x j / (1 - alpha * A_inv j i) := by
    have hj := hd_entry j
    field_simp [hden]
    nlinarith
  ext r
  have hr := hd_entry r
  calc
    xhat r = x r + alpha * A_inv r i * xhat j := by
      nlinarith
    _ = x r + alpha * A_inv r i * (x j / (1 - alpha * A_inv j i)) := by
      rw [hsolve]
    _ = x r + (alpha * x j / (1 - alpha * A_inv j i)) * A_inv r i := by
      field_simp [hden]

/-- **Problem 9.10**, source error formula for a rank-one multiplier blunder:
`x - xhat = -α x_j /(1 - α A^{-1}_{j i}) A^{-1}(:,i)`. -/
theorem higham_problem9_10_rankOne_blunder_error {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (b x xhat : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hx : matMulVec n A x = b)
    (hxhat :
      matMulVec n
          (fun r c => A r c - alpha * higham_problem9_10_rankOneBasis i j r c)
          xhat = b)
    (hden : 1 - alpha * A_inv j i ≠ 0)
    (r : Fin n) :
    x r - xhat r =
      - (alpha * x j / (1 - alpha * A_inv j i)) * A_inv r i := by
  have hsol :=
    higham_problem9_10_rankOne_blunder_solution A A_inv i j alpha b x xhat
      hInv hx hxhat hden
  have hr := congrFun hsol r
  rw [hr]
  ring

/-- **Problem 9.10**, source-facing multiplier-error formula with
`α = ε * \hat l_ij * \hat u_jj`. -/
theorem higham_problem9_10_multiplier_blunder_error {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n)
    (epsilon lhatij uhatjj : ℝ) (b x xhat : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hx : matMulVec n A x = b)
    (hxhat :
      matMulVec n
          (fun r c =>
            A r c -
              higham_problem9_10_multiplierBlunderAlpha epsilon lhatij uhatjj *
                higham_problem9_10_rankOneBasis i j r c)
          xhat = b)
    (hden :
      1 - higham_problem9_10_multiplierBlunderAlpha epsilon lhatij uhatjj *
            A_inv j i ≠ 0)
    (r : Fin n) :
    x r - xhat r =
      - (epsilon * lhatij * uhatjj * x j /
          (1 - epsilon * lhatij * uhatjj * A_inv j i)) * A_inv r i := by
  have h :=
    higham_problem9_10_rankOne_blunder_error A A_inv i j
      (higham_problem9_10_multiplierBlunderAlpha epsilon lhatij uhatjj)
      b x xhat hInv hx hxhat hden r
  simpa [higham_problem9_10_multiplierBlunderAlpha, mul_assoc] using h

/-- **Theorem 9.9**, column/row diagonal-dominance bound packaged as a
componentwise solve error once the `ρ ≤ 2` growth hypothesis is available. -/
theorem higham9_9_diagDom_lu_solve_backward_stable_tight (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ 2 * |A i j|) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ 2 * gamma fp (3 * n) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  diagDom_lu_solve_backward_stable_tight fp n A L_hat U_hat b
    hL_diag hU_diag hLU hn hn3 hGrowth

end NumStability
