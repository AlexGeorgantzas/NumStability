import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Algorithm03

/-!
# Source.Higham.Chapter13.Equation22

This module formalizes the source-facing Chapter 13 statements for
`Equation22`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    recursive ambient-budget certificate for block LU factors.

    The predicate records the exact structural data needed to recurse through
    Schur complements under fixed ambient lower/upper budgets `C_L` and `C_U`:
    the one-block base case, and each successor step's pivot inverse, first
    lower-column budget, first-row upper budget, and strict-tail certificate.
    It deliberately does not prove the source growth/condition propagation
    that supplies these budgets; that remains the open Problem 13.4/Eq.13.22
    obligation. -/
inductive Higham13BlockLUBudgetChain {r : ℕ} (hr : 0 < r) (C_L C_U : ℝ) :
    (m : ℕ) →
      (Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) →
      (ℕ → Matrix (Fin r) (Fin r) ℝ) → Prop
  | one {A : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hId : 1 ≤ C_L)
      (hA : blockMaxNorm (Nat.succ_pos 0) hr A ≤ C_U) :
      Higham13BlockLUBudgetChain hr C_L C_U 0 A pivotInv
  | succ {m : ℕ}
      {A : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      [Invertible (blockMatrixFirstSplitA11 A)]
      (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 A))
      (hId : 1 ≤ C_L)
      (hL21 :
        maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr) hr
            ((blockMatrixFirstSplitA21 A * pivotInv 0 :
              Matrix (Fin ((m + 1) * r)) (Fin r) ℝ)) ≤ C_L)
      (hFirstRow : ∀ j : Fin ((m + 1) + 1), maxEntryNorm hr (A 0 j) ≤ C_U)
      (hTail :
        Higham13BlockLUBudgetChain hr C_L C_U m
          (blockSchur A (pivotInv 0)) (fun k => pivotInv (k + 1))) :
      Higham13BlockLUBudgetChain hr C_L C_U (m + 1) A pivotInv

/-- Monotonicity of the ambient-budget recursive chain.

    This is the structural adapter needed by the full recursive Problem 13.4
    route: a Schur-tail chain proved under tail-local budgets can be reused
    under larger ambient full-matrix budgets once the source growth/condition
    estimates prove the two scalar comparisons. -/
theorem Higham13BlockLUBudgetChain.mono {r : ℕ} {hr : 0 < r}
    {C_L C_U C_L' C_U' : ℝ}
    (hCL : C_L ≤ C_L') (hCU : C_U ≤ C_U') :
    ∀ {m : ℕ}
      {A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13BlockLUBudgetChain hr C_L C_U m A pivotInv →
        Higham13BlockLUBudgetChain hr C_L' C_U' m A pivotInv := by
  intro m A pivotInv hchain
  induction hchain with
  | one hId hA =>
      exact Higham13BlockLUBudgetChain.one (hr := hr)
        (C_L := C_L') (C_U := C_U')
        (le_trans hId hCL) (le_trans hA hCU)
  | succ hpivot hId hL21 hFirstRow hTail ih =>
      exact Higham13BlockLUBudgetChain.succ (hr := hr)
        (C_L := C_L') (C_U := C_U')
        hpivot
        (le_trans hId hCL)
        (le_trans hL21 hCL)
        (fun j => le_trans (hFirstRow j) hCU)
        ih

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    a recursive ambient-budget chain produces concrete block LU factors.

    This is the structural full-factor theorem behind the source-specific
    Eq.13.22/Eq.13.23 route: once the Schur recursion has supplied compatible
    lower and upper budgets at every stage, the explicit recursive factors
    exist and satisfy those budgets.  The source proof still has to instantiate
    `Higham13BlockLUBudgetChain` from the growth-factor/condition-number
    estimates. -/
theorem Higham13BlockLUBudgetChain.exists_blockLUFact_norms {r : ℕ} (hr : 0 < r)
    {C_L C_U : ℝ} :
    ∀ {m : ℕ}
      {A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13BlockLUBudgetChain hr C_L C_U m A pivotInv →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r A L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L ≤ C_L ∧
            blockMaxNorm (Nat.succ_pos m) hr U ≤ C_U := by
  intro m A pivotInv hchain
  cases hchain with
  | one hId hA =>
      rename_i A0
      let L0 : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ := fun _ _ => idBlock r
      let U0 : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ := A0
      have hLnorm_one : blockMaxNorm (Nat.succ_pos 0) hr L0 ≤ 1 := by
        apply blockMaxNorm_le_of_entry_abs_le
        intro i j s t
        fin_cases i
        fin_cases j
        by_cases hst : s = t
        · simp [L0, idBlock, hst]
        · simp [L0, idBlock, hst]
      have hLU : BlockLUFactSpec 1 r A0 L0 U0 := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          fin_cases i
          simp [L0]
        · intro i j hij
          fin_cases i
          fin_cases j
          omega
        · intro i j hij
          fin_cases i
          fin_cases j
          omega
        · intro i j s t
          fin_cases i
          fin_cases j
          simp [L0, U0, idBlock]
      exact ⟨L0, U0, hLU, le_trans hLnorm_one hId, by simpa [U0] using hA⟩
  | succ hpivot hId hL21 hFirstRow hTail =>
      rename_i A0 hInvA11
      have ih :=
        Higham13BlockLUBudgetChain.exists_blockLUFact_norms
          (r := r) hr (C_L := C_L) (C_U := C_U) hTail
      rcases ih with ⟨L_S, U_S, hTailFact, hTailL, hTailU⟩
      let A11_inv : Matrix (Fin r) (Fin r) ℝ := pivotInv 0
      have hInvLeft :
          ∀ s t : Fin r,
            ∑ l : Fin r, A11_inv s l * A0 0 0 l t = if s = t then 1 else 0 := by
        intro s t
        have hA11_inv :
            A11_inv = ⅟(blockMatrixFirstSplitA11 A0) := by
          simpa [A11_inv] using hpivot
        have hmul :
            ((A11_inv * blockMatrixFirstSplitA11 A0) :
              Matrix (Fin r) (Fin r) ℝ) s t =
              (1 : Matrix (Fin r) (Fin r) ℝ) s t := by
          rw [hA11_inv]
          exact congr_fun
            (congr_fun (invOf_mul_self (blockMatrixFirstSplitA11 A0)) s) t
        simpa [Matrix.mul_apply, blockMatrixFirstSplitA11] using hmul
      let L := blockLUOneStepL A0 (pivotInv 0) L_S
      let U := blockLUOneStepU A0 U_S
      have hLU : BlockLUFactSpec _ r A0 L U := by
        simpa [L, U, A11_inv] using
          block_lu_one_step_explicit A0 A11_inv hInvLeft L_S U_S
            (by simpa [A11_inv] using hTailFact)
      have hL :
          blockMaxNorm (Nat.succ_pos _) hr L ≤ C_L := by
        simpa [L, A11_inv] using
          blockLUOneStepL_blockMaxNorm_le_of_firstSplit_tail
            (Nat.succ_pos _) hr A0 A11_inv L_S hId
            (by simpa [A11_inv] using hL21) hTailL
      have hU :
          blockMaxNorm (Nat.succ_pos _) hr U ≤ C_U := by
        simpa [U] using
          blockLUOneStepU_blockMaxNorm_le_of_firstRow_tail
            (Nat.succ_pos _) hr A0 U_S hFirstRow hTailU
      exact ⟨L, U, hLU, hL, hU⟩

/-- The lower ambient budget in a `Higham13BlockLUBudgetChain` is nonnegative.

    Each constructor carries the source-shaped diagonal lower-factor budget
    `1 <= C_L`; this helper keeps product wrappers from taking that as a
    separate hypothesis. -/
theorem Higham13BlockLUBudgetChain.lowerBudget_nonneg {r : ℕ} {hr : 0 < r}
    {C_L C_U : ℝ} {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
    {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
    (hchain : Higham13BlockLUBudgetChain hr C_L C_U m A pivotInv) :
    0 ≤ C_L := by
  cases hchain with
  | one hId hA =>
      exact le_trans zero_le_one hId
  | succ hpivot hId hL21 hFirstRow hTail =>
      exact le_trans zero_le_one hId

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    product-bound packaging for an ambient-budget recursive chain.

    Once the Schur recursion supplies compatible fixed lower and upper budgets,
    `Higham13BlockLUBudgetChain.exists_blockLUFact_norms` gives factors with
    those separate bounds, and this theorem packages the corresponding product
    bound.  Source-specific Eq.13.22/Eq.13.23 constants still require
    instantiating the chain with the growth/condition-number budgets. -/
theorem Higham13BlockLUBudgetChain.exists_blockLUFact_product {r : ℕ}
    (hr : 0 < r) {C_L C_U : ℝ} :
    ∀ {m : ℕ}
      {A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13BlockLUBudgetChain hr C_L C_U m A pivotInv →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r A L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤ C_L * C_U := by
  intro m A pivotInv hchain
  rcases Higham13BlockLUBudgetChain.exists_blockLUFact_norms
      (r := r) hr (C_L := C_L) (C_U := C_U) hchain with
    ⟨L, U, hFact, hL, hU⟩
  refine ⟨L, U, hFact, ?_⟩
  exact mul_le_mul hL hU
    (blockMaxNorm_nonneg (Nat.succ_pos m) hr U)
    (Higham13BlockLUBudgetChain.lowerBudget_nonneg hchain)

/-- **Eq. 13.22**: ‖L‖ · ‖U‖ ≤ n · ρ_n³ · κ(A) · ‖A‖ for general matrices.
    From ‖L‖ ≤ n · ρ_n² · κ(A) and ‖U‖ ≤ ρ_n · ‖A‖. -/
theorem block_lu_normLU_bound_general
    (normL normU _normA : ℝ) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (normL_bound normU_bound : ℝ)
    (hNormL : normL ≤ normL_bound) (hNormU : normU ≤ normU_bound) :
    normL * normU ≤ normL_bound * normU_bound :=
  mul_le_mul hNormL hNormU hU (le_trans hL hNormL)

/-- Source-shaped scalar consequence for Higham eq. (13.22):
    if `‖L‖ ≤ n ρ_n^2 κ(A)` and `‖U‖ ≤ ρ_n ‖A‖`, then
    `‖L‖‖U‖ ≤ n ρ_n^3 κ(A) ‖A‖`.  The hard source work is proving the two
    displayed premises from growth-factor and Schur-complement analysis
    (Problem 13.4); this theorem records the exact algebraic combination. -/
theorem block_lu_normLU_bound_general_higham_13_22
    (normL normU normA rho kappa : ℝ) (n : ℕ)
    (hU : 0 ≤ normU) (_hRho : 0 ≤ rho) (hKappa : 0 ≤ kappa)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa)
    (hNormU : normU ≤ rho * normA) :
    normL * normU ≤ (n : ℝ) * rho ^ 3 * kappa * normA := by
  have hLbound_nonneg : 0 ≤ (n : ℝ) * rho ^ 2 * kappa := by positivity
  have hmul := mul_le_mul hNormL hNormU hU hLbound_nonneg
  calc normL * normU
      ≤ ((n : ℝ) * rho ^ 2 * kappa) * (rho * normA) := hmul
    _ = (n : ℝ) * rho ^ 3 * kappa * normA := by ring

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    source-shaped product bound from an instantiated ambient-budget chain.

    If the recursive Schur chain has already been instantiated with the source
    lower budget `n rho^2 kappa(A)` and upper budget `rho ||A||`, then the
    concrete factors produced by the chain satisfy the displayed Eq.13.22
    product bound.  The theorem still leaves the source work of proving the
    chain itself visible. -/
theorem Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product {r : ℕ}
    (hr : 0 < r) {rho kappa normA : ℝ} (n : ℕ) :
    ∀ {m : ℕ}
      {A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13BlockLUBudgetChain hr ((n : ℝ) * rho ^ 2 * kappa) (rho * normA)
        m A pivotInv →
      0 ≤ rho →
      0 ≤ kappa →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r A L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
                (n : ℝ) * rho ^ 3 * kappa * normA := by
  intro m A pivotInv hchain hRho hKappa
  rcases Higham13BlockLUBudgetChain.exists_blockLUFact_norms
      (r := r) hr
      (C_L := (n : ℝ) * rho ^ 2 * kappa)
      (C_U := rho * normA) hchain with
    ⟨L, U, hFact, hL, hU⟩
  refine ⟨L, U, hFact, ?_⟩
  exact block_lu_normLU_bound_general_higham_13_22
    (blockMaxNorm (Nat.succ_pos m) hr L)
    (blockMaxNorm (Nat.succ_pos m) hr U)
    normA rho kappa n
    (blockMaxNorm_nonneg (Nat.succ_pos m) hr U)
    hRho hKappa hL hU

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    exact-`kappa(A)` source specialization of the ambient-budget chain.

    This wrapper fixes the chain constants to the source growth factor
    `rho = growthFactorEntry A0 G` and
    `kappa(A) = ‖A0‖ * ‖Ainv‖`.  The recursive proof obligation is still the
    explicit `Higham13BlockLUBudgetChain` hypothesis. -/
theorem Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
    {r N : ℕ} (hr : 0 < r) (hN : 0 < N)
    (A0 G Ainv : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN A0)
    (n : ℕ) :
    ∀ {m : ℕ}
      {A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m A pivotInv →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r A L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
                (n : ℝ) *
                  (growthFactorEntry hN A0 G hApos) ^ 3 *
                  (maxEntryNormRect hN hN A0 *
                    maxEntryNormRect hN hN Ainv) *
                  maxEntryNormRect hN hN A0 := by
  intro m A pivotInv hchain
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv
  let normA : ℝ := maxEntryNormRect hN hN A0
  have hRho : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A0 G hApos
  have hKappa : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A0)
      (maxEntryNormRect_nonneg hN hN Ainv)
  simpa [rho, kappaA, normA] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product
      (r := r) hr (rho := rho) (kappa := kappaA) (normA := normA) n
      hchain hRho hKappa

end NumStability
