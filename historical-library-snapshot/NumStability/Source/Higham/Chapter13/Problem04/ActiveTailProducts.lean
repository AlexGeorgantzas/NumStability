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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauChain
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Source.Higham.Chapter13.Problem04.ActiveTailProducts

This module formalizes the source-facing Chapter 13 statements for
`Problem04.ActiveTailProducts`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.22):
    product witness from the active-tail successor with automatic Schur-tail
    inverse-entry handoff.

    This packages
    `Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_with_derived_tail_inverse_entry_exact_kappa`
    through the fixed-ambient global-tableau Eq.13.22 product API.  The
    recursive tail constructor remains explicit, but it only has to consume the
    derived tail inverse-entry certificate. -/
theorem
    higham13_eq13_22_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
    {M r N m n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob)
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) →
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1)))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN Aglob
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
              hApos) ^ 3 *
            (maxEntryNormRect hN hN Aglob *
              maxEntryNormRect hN hN AinvGlob) *
            maxEntryNormRect hN hN Aglob := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n (m + 1)
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
        (fun q => pivotInv (k + q)) := by
    simpa [G] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_with_derived_tail_inverse_entry_exact_kappa
        (M := M) (r := r) (N := N) (m := m) (n := n) (k := k)
        hr hN hM Aglob AinvGlob A pivotInv hApos hkM
        tailFull tailSucc h0 hsucc hactive hpivot hsn hA_le_G
        hAinv_entry hTailFromEntry
  simpa [G] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob G AinvGlob
      hApos hRight hNn (by simpa [G] using hA_le_G) hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    point-row product witness from the active-tail successor with automatic
    Schur-tail inverse-entry handoff.

    This is the Eq.13.23 companion of
    `higham13_eq13_22_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`.
    The source-side `rho <= 2` theorem remains an explicit BDD/product-update
    obligation. -/
theorem
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
    {M r N m n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hRho_le_two :
      growthFactorEntry hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        hApos ≤ 2)
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob)
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) →
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1)))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN Aglob *
              maxEntryNormRect hN hN AinvGlob) *
            maxEntryNormRect hN hN Aglob := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n (m + 1)
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
        (fun q => pivotInv (k + q)) := by
    simpa [G] using
      Higham13Eq1322GlobalTableauSourceChain.succ_from_matrix_stage_history_active_tail_with_derived_tail_inverse_entry_exact_kappa
        (M := M) (r := r) (N := N) (m := m) (n := n) (k := k)
        hr hN hM Aglob AinvGlob A pivotInv hApos hkM
        tailFull tailSucc h0 hsucc hactive hpivot hsn hA_le_G
        hAinv_entry hTailFromEntry
  simpa [G] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob G AinvGlob
      hApos hRight hNn (by simpa [G] using hA_le_G)
      (by simpa [G] using hRho_le_two) hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.22):
    determinant-nonzero full-flat active-tail product witness with automatic
    ambient `nonsingInv` and positive growth denominator.

    This specializes
    `higham13_eq13_22_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa`
    to the actual flat Algorithm 13.3 input and derives the ambient right
    inverse and `growthFactorEntry` denominator from
    `det(blockMatrixFlatFin A) != 0`. -/
theorem
    higham13_eq13_22_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_det_ne_zero
    {M r m n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A))) →
      Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
        (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hM hr) hM hr A pivotInv)
        (nonsingInv (M * r) (blockMatrixFlatFin A))
        (maxEntryNorm_pos_of_det_ne_zero
          (Nat.mul_pos hM hr) (blockMatrixFlatFin A) hdet)
        n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1)))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          (n : ℝ) *
            (growthFactorEntry (Nat.mul_pos hM hr) (blockMatrixFlatFin A)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                (Nat.mul_pos hM hr) hM hr A pivotInv)
              (maxEntryNorm_pos_of_det_ne_zero
                (Nat.mul_pos hM hr) (blockMatrixFlatFin A) hdet)) ^ 3 *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  classical
  let hFlat : 0 < M * r := Nat.mul_pos hM hr
  let G : Fin (M * r) → Fin (M * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hFlat hM hr A pivotInv
  have hApos : 0 < maxEntryNorm hFlat (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hFlat (blockMatrixFlatFin A) hdet
  have hRight :
      IsRightInverse (M * r) (blockMatrixFlatFin A)
        (nonsingInv (M * r) (blockMatrixFlatFin A)) :=
    ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
  have hA_le_G :
      maxEntryNorm hFlat (blockMatrixFlatFin A) ≤ maxEntryNorm hFlat G := by
    rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hM hr A]
    simpa [G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hFlat hM hr A pivotInv
  simpa [hFlat, G] using
    higham13_eq13_22_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
      (M := M) (r := r) (N := M * r) (m := m) (n := n) (k := k)
      hr hFlat hM (blockMatrixFlatFin A)
      (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv
      hApos hRight hNn hkM tailFull tailSucc h0 hsucc hactive hpivot
      hsn hA_le_G hAinv_entry hTailFromEntry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    determinant-nonzero full-flat active-tail point-row product witness with
    automatic ambient `nonsingInv` and positive growth denominator.

    The source-side `rho <= 2` theorem is still explicit, but it is stated for
    the determinant-derived growth denominator. -/
theorem
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_det_ne_zero
    {M r m n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hRho_le_two :
      growthFactorEntry (Nat.mul_pos hM hr) (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hM hr) hM hr A pivotInv)
        (maxEntryNorm_pos_of_det_ne_zero
          (Nat.mul_pos hM hr) (blockMatrixFlatFin A) hdet) ≤ 2)
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A))) →
      Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
        (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hM hr) hM hr A pivotInv)
        (nonsingInv (M * r) (blockMatrixFlatFin A))
        (maxEntryNorm_pos_of_det_ne_zero
          (Nat.mul_pos hM hr) (blockMatrixFlatFin A) hdet)
        n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1)))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  classical
  let hFlat : 0 < M * r := Nat.mul_pos hM hr
  let G : Fin (M * r) → Fin (M * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hFlat hM hr A pivotInv
  have hApos : 0 < maxEntryNorm hFlat (blockMatrixFlatFin A) :=
    maxEntryNorm_pos_of_det_ne_zero hFlat (blockMatrixFlatFin A) hdet
  have hRight :
      IsRightInverse (M * r) (blockMatrixFlatFin A)
        (nonsingInv (M * r) (blockMatrixFlatFin A)) :=
    ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
  have hA_le_G :
      maxEntryNorm hFlat (blockMatrixFlatFin A) ≤ maxEntryNorm hFlat G := by
    rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hM hr A]
    simpa [G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hFlat hM hr A pivotInv
  simpa [hFlat, G] using
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
      (M := M) (r := r) (N := M * r) (m := m) (n := n) (k := k)
      hr hFlat hM (blockMatrixFlatFin A)
      (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv
      hApos hRight hNn hkM tailFull tailSucc h0 hsucc hactive hpivot
      hsn hA_le_G hRho_le_two hAinv_entry hTailFromEntry

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    full-flat active-tail product witness with the `rho <= 2` side condition
    supplied by the source-strength product-bound/diagonal-update BDD route.

    This specializes the generic derived-tail active product witness to the
    concrete flat Algorithm 13.3 source matrix, so the matrix-stage BDD theorem
    proves the growth-factor side condition instead of leaving it as a raw
    premise.  The recursive tail source-chain constructor still consumes the
    derived inverse-entry certificate for the successor tail. -/
theorem
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update
    {M r m n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob)
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob) →
      Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
        (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hM hr) hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1))))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  classical
  let hFlat : 0 < M * r := Nat.mul_pos hM hr
  let G : Fin (M * r) → Fin (M * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hFlat hM hr A pivotInv
  have hA_le_G :
      maxEntryNorm hFlat (blockMatrixFlatFin A) ≤ maxEntryNorm hFlat G := by
    rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hM hr A]
    simpa [G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hFlat hM hr A pivotInv
  have hRho_le_two :
      growthFactorEntry hFlat (blockMatrixFlatFin A) G hApos ≤ 2 := by
    simpa [hFlat, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hM hr A pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hFlat, G] using
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa
      (M := M) (r := r) (N := M * r) (m := m) (n := n) (k := k)
      hr hFlat hM (blockMatrixFlatFin A) AinvGlob A pivotInv
      hApos hRight hNn hkM tailFull tailSucc h0 hsucc hactive
      hpivot hsn hA_le_G hRho_le_two hAinv_entry hTailFromEntry

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    reciprocal-table version of the full-flat active-tail product-update
    witness with derived successor-tail inverse-entry data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update_reciprocal
    {M r m n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob)
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob) →
      Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
        (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hM hr) hM hr A pivotInv)
        AinvGlob hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1))))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update
      hr hM AinvGlob A pivotInv hApos hRight hNn hkM tailFull tailSucc
      h0 hsucc hactive hpivot hsn hAinv_entry hTailFromEntry
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    determinant-nonzero version of the full-flat active-tail product-update
    witness, using the canonical `nonsingInv` ambient inverse. -/
theorem
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {M r m n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A))) →
      Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
        (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hM hr) hM hr A pivotInv)
        (nonsingInv (M * r) (blockMatrixFlatFin A)) hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1))))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hkM tailFull tailSucc h0 hsucc hactive hpivot hsn hAinv_entry
      hTailFromEntry invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 / equation (13.23):
    determinant-nonzero reciprocal-table version of the full-flat active-tail
    product-update witness with derived successor-tail inverse-entry data. -/
theorem
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {M r m n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin ((m + 1) + 1) → Fin M)
    (tailSucc : Fin (m + 1) → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin (m + 1), tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin (m + 1), k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin ((m + 1) * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin ((m + 1) * r))
            (Fin r ⊕ Fin ((m + 1) * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (hTailFromEntry :
      ∀ [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA12
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA21
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
        (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)))],
      (∀ i j : Fin r ⊕ Fin (m * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc))) :
          Matrix (Fin r ⊕ Fin (m * r)) (Fin r ⊕ Fin (m * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A))) →
      Higham13Eq1322GlobalTableauSourceChain hr (Nat.mul_pos hM hr)
        (blockMatrixFlatFin A)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          (Nat.mul_pos hM hr) hM hr A pivotInv)
        (nonsingInv (M * r) (blockMatrixFlatFin A)) hApos n m
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailSucc)
        (fun q => pivotInv (k + (q + 1))))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec ((m + 1) + 1) r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos (m + 1)) hr L *
            blockMaxNorm (Nat.succ_pos (m + 1)) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_active_tail_product_from_global_tableau_matrix_stage_history_with_derived_tail_inverse_entry_exact_kappa_of_product_bound_diag_update_reciprocal
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hkM tailFull tailSucc h0 hsucc hactive hpivot hsn hAinv_entry
      hTailFromEntry invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      hReciprocal hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.22):
    concrete Eq.13.22 product witness for a recorded two-block active tail.

    This packages
    `Higham13Eq1322GlobalTableauSourceChain.two_from_matrix_stage_history_active_tail_exact_kappa`
    through the fixed-ambient global-tableau product API.  The ambient
    inverse-entry/source comparison remains an explicit hypothesis. -/
theorem
    higham13_eq13_22_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa
    {M r N n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hkM : k < M)
    (tailFull : Fin 2 → Fin M)
    (tailSucc : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 1, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin 1, k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (1 * r))
            (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    ∃ L U : Fin 2 → Fin 2 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 2 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 1) hr L *
            blockMaxNorm (Nat.succ_pos 1) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN Aglob
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
              hApos) ^ 3 *
            (maxEntryNormRect hN hN Aglob *
              maxEntryNormRect hN hN AinvGlob) *
            maxEntryNormRect hN hN Aglob := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n 1
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
        (fun q => pivotInv (k + q)) := by
    simpa [G] using
      Higham13Eq1322GlobalTableauSourceChain.two_from_matrix_stage_history_active_tail_exact_kappa
        (M := M) (r := r) (N := N) (n := n) (k := k)
        hr hN hM Aglob AinvGlob A pivotInv hApos hkM
        tailFull tailSucc h0 hsucc hactive hpivot hsn hA_le_G hAinv_entry
  simpa [G] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob G AinvGlob
      hApos hRight hNn (by simpa [G] using hA_le_G) hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    concrete point-row product witness for a recorded two-block active tail.

    This is the Eq.13.23 companion of
    `higham13_eq13_22_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa`;
    it keeps the source-side `rho <= 2` theorem as an explicit hypothesis. -/
theorem
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa
    {M r N n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hkM : k < M)
    (tailFull : Fin 2 → Fin M)
    (tailSucc : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 1, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin 1, k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hRho_le_two :
      growthFactorEntry hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        hApos ≤ 2)
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (1 * r))
            (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    ∃ L U : Fin 2 → Fin 2 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 2 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 1) hr L *
            blockMaxNorm (Nat.succ_pos 1) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN Aglob *
              maxEntryNormRect hN hN AinvGlob) *
            maxEntryNormRect hN hN Aglob := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n 1
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
        (fun q => pivotInv (k + q)) := by
    simpa [G] using
      Higham13Eq1322GlobalTableauSourceChain.two_from_matrix_stage_history_active_tail_exact_kappa
        (M := M) (r := r) (N := N) (n := n) (k := k)
        hr hN hM Aglob AinvGlob A pivotInv hApos hkM
        tailFull tailSucc h0 hsucc hactive hpivot hsn hA_le_G hAinv_entry
  simpa [G] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob G AinvGlob
      hApos hRight hNn (by simpa [G] using hA_le_G)
      (by simpa [G] using hRho_le_two) hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.22):
    concrete Eq.13.22 product witness for a recorded three-block active tail.

    This packages
    `Higham13Eq1322GlobalTableauSourceChain.three_from_matrix_stage_history_active_tail_exact_kappa`
    through the fixed-ambient global-tableau product API.  The parent
    inverse-entry certificate is propagated to the two-block tail by the
    three-tail source-chain constructor; the all-tail source certificate
    remains open beyond this finite instance. -/
theorem
    higham13_eq13_22_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa
    {M r N n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hkM : k < M)
    (tailFull : Fin 3 → Fin M)
    (tailMid : Fin 2 → Fin M)
    (tailLast : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 2, tailFull (Fin.succ i) = tailMid i)
    (hactive : ∀ i : Fin 2, k + 1 ≤ (tailMid i).val)
    (hkSuccM : k + 1 < M)
    (h1 : tailMid 0 = ⟨k + 1, hkSuccM⟩)
    (hsuccTail : ∀ i : Fin 1, tailMid (Fin.succ i) = tailLast i)
    (hactiveTail : ∀ i : Fin 1, k + 1 + 1 ≤ (tailLast i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hpivotTail :
      pivotInv (k + 1) =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)))
    (hsnParent : (((1 + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnTail : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (2 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (2 * r))
            (Fin r ⊕ Fin (2 * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    ∃ L U : Fin 3 → Fin 3 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 3 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 2) hr L *
            blockMaxNorm (Nat.succ_pos 2) hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN Aglob
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
              hApos) ^ 3 *
            (maxEntryNormRect hN hN Aglob *
              maxEntryNormRect hN hN AinvGlob) *
            maxEntryNormRect hN hN Aglob := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n 2
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
        (fun q => pivotInv (k + q)) := by
    simpa [G] using
      Higham13Eq1322GlobalTableauSourceChain.three_from_matrix_stage_history_active_tail_exact_kappa
        (M := M) (r := r) (N := N) (n := n) (k := k)
        hr hN hM Aglob AinvGlob A pivotInv hApos hkM
        tailFull tailMid tailLast h0 hsucc hactive hkSuccM h1 hsuccTail hactiveTail
        hpivot hpivotTail hsnParent hsnTail hA_le_G hAinv_entry
  simpa [G] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob G AinvGlob
      hApos hRight hNn (by simpa [G] using hA_le_G) hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    concrete point-row product witness for a recorded three-block active tail.

    This is the Eq.13.23 companion of
    `higham13_eq13_22_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa`;
    it keeps the source-side `rho <= 2` theorem as an explicit hypothesis. -/
theorem
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa
    {M r N n k : ℕ} (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (Aglob AinvGlob : Fin N → Fin N → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm hN Aglob)
    (hRight : IsRightInverse N Aglob AinvGlob)
    (hNn : (N : ℝ) ≤ (n : ℝ))
    (hkM : k < M)
    (tailFull : Fin 3 → Fin M)
    (tailMid : Fin 2 → Fin M)
    (tailLast : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 2, tailFull (Fin.succ i) = tailMid i)
    (hactive : ∀ i : Fin 2, k + 1 ≤ (tailMid i).val)
    (hkSuccM : k + 1 < M)
    (h1 : tailMid 0 = ⟨k + 1, hkSuccM⟩)
    (hsuccTail : ∀ i : Fin 1, tailMid (Fin.succ i) = tailLast i)
    (hactiveTail : ∀ i : Fin 1, k + 1 + 1 ≤ (tailLast i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hpivotTail :
      pivotInv (k + 1) =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)))
    (hsnParent : (((1 + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnTail : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hA_le_G :
      maxEntryNorm hN Aglob ≤
        maxEntryNorm hN
          (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv))
    (hRho_le_two :
      growthFactorEntry hN Aglob
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv)
        hApos ≤ 2)
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (2 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (2 * r))
            (Fin r ⊕ Fin (2 * r)) ℝ) i j| ≤
          maxEntryNormRect hN hN AinvGlob) :
    ∃ L U : Fin 3 → Fin 3 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 3 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 2) hr L *
            blockMaxNorm (Nat.succ_pos 2) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN Aglob *
              maxEntryNormRect hN hN AinvGlob) *
            maxEntryNormRect hN hN Aglob := by
  classical
  let G : Fin N → Fin N → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hM hr A pivotInv
  have hcert :
      Higham13Eq1322GlobalTableauSourceChain hr hN Aglob G AinvGlob hApos n 2
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)
        (fun q => pivotInv (k + q)) := by
    simpa [G] using
      Higham13Eq1322GlobalTableauSourceChain.three_from_matrix_stage_history_active_tail_exact_kappa
        (M := M) (r := r) (N := N) (n := n) (k := k)
        hr hN hM Aglob AinvGlob A pivotInv hApos hkM
        tailFull tailMid tailLast h0 hsucc hactive hkSuccM h1 hsuccTail hactiveTail
        hpivot hpivotTail hsnParent hsnTail hA_le_G hAinv_entry
  simpa [G] using
    Higham13Eq1322GlobalTableauSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_right_inverse
      (r := r) (N := N) (n := n) hr hN Aglob G AinvGlob
      hApos hRight hNn (by simpa [G] using hA_le_G)
      (by simpa [G] using hRho_le_two) hcert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    full-flat three-block active-tail product witness with the `rho <= 2`
    side condition supplied by the source-strength product-bound/diagonal-update
    BDD route.

    This is the three-block companion to
    `higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update`.
    It packages the already-closed three-block active-tail global-tableau
    certificate through the same full-matrix BDD product/update route. -/
theorem
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 3 → Fin M)
    (tailMid : Fin 2 → Fin M)
    (tailLast : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 2, tailFull (Fin.succ i) = tailMid i)
    (hactive : ∀ i : Fin 2, k + 1 ≤ (tailMid i).val)
    (hkSuccM : k + 1 < M)
    (h1 : tailMid 0 = ⟨k + 1, hkSuccM⟩)
    (hsuccTail : ∀ i : Fin 1, tailMid (Fin.succ i) = tailLast i)
    (hactiveTail : ∀ i : Fin 1, k + 1 + 1 ≤ (tailLast i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hpivotTail :
      pivotInv (k + 1) =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)))
    (hsnParent : (((1 + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnTail : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (2 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (2 * r))
            (Fin r ⊕ Fin (2 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 3 → Fin 3 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 3 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 2) hr L *
            blockMaxNorm (Nat.succ_pos 2) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  classical
  let hFlat : 0 < M * r := Nat.mul_pos hM hr
  let G : Fin (M * r) → Fin (M * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hFlat hM hr A pivotInv
  have hA_le_G :
      maxEntryNorm hFlat (blockMatrixFlatFin A) ≤ maxEntryNorm hFlat G := by
    rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hM hr A]
    simpa [G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hFlat hM hr A pivotInv
  have hRho_le_two :
      growthFactorEntry hFlat (blockMatrixFlatFin A) G hApos ≤ 2 := by
    simpa [hFlat, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hM hr A pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hFlat, G] using
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa
      (M := M) (r := r) (N := M * r) (n := n) (k := k)
      hr hFlat hM (blockMatrixFlatFin A) AinvGlob A pivotInv
      hApos hRight hNn hkM tailFull tailMid tailLast
      h0 hsucc hactive hkSuccM h1 hsuccTail hactiveTail
      hpivot hpivotTail hsnParent hsnTail hA_le_G hRho_le_two hAinv_entry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    reciprocal-table version of the full-flat three-block active-tail
    product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 3 → Fin M)
    (tailMid : Fin 2 → Fin M)
    (tailLast : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 2, tailFull (Fin.succ i) = tailMid i)
    (hactive : ∀ i : Fin 2, k + 1 ≤ (tailMid i).val)
    (hkSuccM : k + 1 < M)
    (h1 : tailMid 0 = ⟨k + 1, hkSuccM⟩)
    (hsuccTail : ∀ i : Fin 1, tailMid (Fin.succ i) = tailLast i)
    (hactiveTail : ∀ i : Fin 1, k + 1 + 1 ≤ (tailLast i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hpivotTail :
      pivotInv (k + 1) =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)))
    (hsnParent : (((1 + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnTail : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (2 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (2 * r))
            (Fin r ⊕ Fin (2 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 3 → Fin 3 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 3 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 2) hr L *
            blockMaxNorm (Nat.succ_pos 2) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hM AinvGlob A pivotInv hApos hRight hNn hkM
      tailFull tailMid tailLast h0 hsucc hactive hkSuccM h1 hsuccTail
      hactiveTail hpivot hpivotTail hsnParent hsnTail hAinv_entry
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    determinant-nonzero full-flat three-block active-tail product-update
    witness, using the canonical `nonsingInv` ambient inverse. -/
theorem
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 3 → Fin M)
    (tailMid : Fin 2 → Fin M)
    (tailLast : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 2, tailFull (Fin.succ i) = tailMid i)
    (hactive : ∀ i : Fin 2, k + 1 ≤ (tailMid i).val)
    (hkSuccM : k + 1 < M)
    (h1 : tailMid 0 = ⟨k + 1, hkSuccM⟩)
    (hsuccTail : ∀ i : Fin 1, tailMid (Fin.succ i) = tailLast i)
    (hactiveTail : ∀ i : Fin 1, k + 1 + 1 ≤ (tailLast i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hpivotTail :
      pivotInv (k + 1) =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)))
    (hsnParent : (((1 + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnTail : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (2 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (2 * r))
            (Fin r ⊕ Fin (2 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 3 → Fin 3 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 3 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 2) hr L *
            blockMaxNorm (Nat.succ_pos 2) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hkM tailFull tailMid tailLast h0 hsucc hactive hkSuccM h1
      hsuccTail hactiveTail hpivot hpivotTail hsnParent hsnTail hAinv_entry
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    determinant-nonzero reciprocal-table version of the full-flat three-block
    active-tail product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 3 → Fin M)
    (tailMid : Fin 2 → Fin M)
    (tailLast : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 2, tailFull (Fin.succ i) = tailMid i)
    (hactive : ∀ i : Fin 2, k + 1 ≤ (tailMid i).val)
    (hkSuccM : k + 1 < M)
    (h1 : tailMid 0 = ⟨k + 1, hkSuccM⟩)
    (hsuccTail : ∀ i : Fin 1, tailMid (Fin.succ i) = tailLast i)
    (hactiveTail : ∀ i : Fin 1, k + 1 + 1 ≤ (tailLast i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hpivotTail :
      pivotInv (k + 1) =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv (k + 1) tailMid)))
    (hsnParent : (((1 + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
    (hsnTail : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (2 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (2 * r))
            (Fin r ⊕ Fin (2 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 3 → Fin 3 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 3 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 2) hr L *
            blockMaxNorm (Nat.succ_pos 2) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_three_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hkM tailFull tailMid tailLast h0 hsucc hactive hkSuccM h1
      hsuccTail hactiveTail hpivot hpivotTail hsnParent hsnTail hAinv_entry
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hReciprocal
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    full-flat two-block active-tail product witness with the `rho <= 2` side
    condition supplied by the source-strength product-bound/diagonal-update
    BDD route.

    The generic two-active-tail witness allows an arbitrary ambient tableau
    denominator.  This specialization sets the ambient matrix to the actual
    flat Algorithm 13.3 input, so the existing matrix-stage BDD theorem proves
    the required growth-factor bound rather than taking it as a raw premise. -/
theorem
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 2 → Fin M)
    (tailSucc : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 1, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin 1, k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (1 * r))
            (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 2 → Fin 2 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 2 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 1) hr L *
            blockMaxNorm (Nat.succ_pos 1) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  classical
  let hFlat : 0 < M * r := Nat.mul_pos hM hr
  let G : Fin (M * r) → Fin (M * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hFlat hM hr A pivotInv
  have hA_le_G :
      maxEntryNorm hFlat (blockMatrixFlatFin A) ≤ maxEntryNorm hFlat G := by
    rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm hM hr A]
    simpa [G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_contains_initial
        hFlat hM hr A pivotInv
  have hRho_le_two :
      growthFactorEntry hFlat (blockMatrixFlatFin A) G hApos ≤ 2 := by
    simpa [hFlat, G] using
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hM hr A pivotInv hApos invDiagBound stageInvDiagBound hDom
        hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hFlat, G] using
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa
      (M := M) (r := r) (N := M * r) (n := n) (k := k)
      hr hFlat hM (blockMatrixFlatFin A) AinvGlob A pivotInv
      hApos hRight hNn hkM tailFull tailSucc h0 hsucc hactive
      hpivot hsn hA_le_G hRho_le_two hAinv_entry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    reciprocal-table version of the full-flat two-block active-tail
    product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (AinvGlob : Fin (M * r) → Fin (M * r) → ℝ)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hRight : IsRightInverse (M * r) (blockMatrixFlatFin A) AinvGlob)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 2 → Fin M)
    (tailSucc : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 1, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin 1, k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (1 * r))
            (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr) AinvGlob)
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 2 → Fin 2 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 2 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 1) hr L *
            blockMaxNorm (Nat.succ_pos 1) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                AinvGlob) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hM AinvGlob A pivotInv hApos hRight hNn hkM tailFull tailSucc
      h0 hsucc hactive hpivot hsn hAinv_entry invDiagBound stageInvDiagBound
      hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    determinant-nonzero full-flat two-block active-tail product-update
    witness, using the canonical `nonsingInv` ambient inverse. -/
theorem
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_of_det_ne_zero
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 2 → Fin M)
    (tailSucc : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 1, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin 1, k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (1 * r))
            (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < M,
      maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 2 → Fin 2 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 2 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 1) hr L *
            blockMaxNorm (Nat.succ_pos 1) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hkM tailFull tailSucc h0 hsucc hactive hpivot hsn hAinv_entry
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hPivotInvBound
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 / equation (13.23):
    determinant-nonzero reciprocal-table version of the full-flat two-block
    active-tail product-update witness. -/
theorem
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal_of_det_ne_zero
    {M r n k : ℕ} (hr : 0 < r) (hM : 0 < M)
    (A : Fin M → Fin M → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hApos : 0 < maxEntryNorm (Nat.mul_pos hM hr) (blockMatrixFlatFin A))
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (M * r)) (Fin (M * r)) ℝ) ≠ 0)
    (hNn : (((M * r : ℕ) : ℝ) ≤ (n : ℝ)))
    (hkM : k < M)
    (tailFull : Fin 2 → Fin M)
    (tailSucc : Fin 1 → Fin M)
    (h0 : tailFull 0 = ⟨k, hkM⟩)
    (hsucc : ∀ i : Fin 1, tailFull (Fin.succ i) = tailSucc i)
    (hactive : ∀ i : Fin 1, k + 1 ≤ (tailSucc i).val)
    [Invertible
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible
      (blockMatrixFirstSplitA22
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) -
        blockMatrixFirstSplitA21
            (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) *
          ⅟(blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)) *
            blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))]
    [Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA12
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA21
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
      (blockMatrixFirstSplitA22
        (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))]
    (hpivot :
      pivotInv k =
        ⅟(blockMatrixFirstSplitA11
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull)))
    (hsn : ((r : ℕ) : ℝ) ≤ (n : ℝ))
    (hAinv_entry :
      ∀ i j : Fin r ⊕ Fin (1 * r),
        |(⅟(Matrix.fromBlocks
            (blockMatrixFirstSplitA11
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA12
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA21
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))
            (blockMatrixFirstSplitA22
              (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull))) :
          Matrix (Fin r ⊕ Fin (1 * r))
            (Fin r ⊕ Fin (1 * r)) ℝ) i j| ≤
          maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
            (nonsingInv (M * r) (blockMatrixFlatFin A)))
    (invDiagBound : Fin M → ℝ)
    (stageInvDiagBound : ℕ → Fin M → ℝ)
    (hDom : IsBlockDiagDomCol M (fun i j => maxEntryNorm hr (A i j)) invDiagBound)
    (hDiagBound : ∀ j : Fin M, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInitInv : ∀ j : Fin M, stageInvDiagBound 0 j = invDiagBound j)
    (hReciprocal : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)))
    (hProduct : ∀ k : ℕ, ∀ hk : k < M, ∀ i j : Fin M,
      k + 1 ≤ i.val → k + 1 ≤ j.val →
        maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩ *
            pivotInv k *
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j) ≤
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i ⟨k, hk⟩) *
          maxEntryNorm hr (pivotInv k) *
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k ⟨k, hk⟩ j))
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound
      (fun k => maxEntryNorm hr (pivotInv k))) :
    ∃ L U : Fin 2 → Fin 2 → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec 2 r
          (higham13_algorithm13_3_schurStageMatrixTailBlock A pivotInv k tailFull) L U ∧
        blockMaxNorm (Nat.succ_pos 1) hr L *
            blockMaxNorm (Nat.succ_pos 1) hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (blockMatrixFlatFin A) *
              maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
                (nonsingInv (M * r) (blockMatrixFlatFin A))) *
            maxEntryNormRect (Nat.mul_pos hM hr) (Nat.mul_pos hM hr)
              (blockMatrixFlatFin A) := by
  exact
    higham13_eq13_23_exists_blockLUFact_two_active_tail_product_from_global_tableau_matrix_stage_history_exact_kappa_of_product_bound_diag_update_reciprocal
      hr hM (nonsingInv (M * r) (blockMatrixFlatFin A)) A pivotInv hApos
      ((isInverse_nonsingInv_of_det_ne_zero (M * r) (blockMatrixFlatFin A) hdet).2)
      hNn hkM tailFull tailSucc h0 hsucc hactive hpivot hsn hAinv_entry
      invDiagBound stageInvDiagBound hDom hDiagBound hInitInv hReciprocal
      hProduct hDiagUpdate

end NumStability
