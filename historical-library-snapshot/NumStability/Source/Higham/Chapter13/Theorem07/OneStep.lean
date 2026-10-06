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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance

/-!
# Source.Higham.Chapter13.Theorem07.OneStep

This module formalizes the source-facing Chapter 13 statements for
`Theorem07.OneStep`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.1  Theorem 13.7 one-step diagonal-dominance inheritance
-- ============================================================

/-- **Theorem 13.7 one-step inheritance** (Demmel--Higham--Schreiber).
    If A is block diag dom by columns with dominance parameters invDiagBound,
    and normInv · invDiagBound(0) ≤ 1 (i.e., ‖A₁₁⁻¹‖ ≤ ‖A₁₁⁻¹‖⁻¹⁻¹),
    then the Schur complement inherits block diagonal dominance. -/
theorem block_diag_dom_schur_inherit {m : ℕ}
    (blockNorm : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (invDiagBound : Fin (m + 1) → ℝ)
    (normInv : ℝ) (hNormInv : 0 ≤ normInv)
    (hDom : IsBlockDiagDomCol (m + 1) blockNorm invDiagBound)
    -- ‖A₁₁⁻¹‖ · ‖A₁₁⁻¹‖⁻¹ ≤ 1 (submultiplicativity)
    (hNormInvBound : normInv * invDiagBound 0 ≤ 1)
    -- Schur complement block norms (triangle inequality)
    (schurNorm : Fin m → Fin m → ℝ)
    (hSchurBound : ∀ i j : Fin m,
      schurNorm i j ≤ blockNorm i.succ j.succ +
        blockNorm i.succ 0 * normInv * blockNorm 0 j.succ)
    -- Schur complement inverse diagonal bounds
    (schurInvDiag : Fin m → ℝ)
    (hSchurDiag : ∀ j : Fin m,
      invDiagBound j.succ - blockNorm j.succ 0 * normInv * blockNorm 0 j.succ
        ≤ schurInvDiag j) :
    IsBlockDiagDomCol m schurNorm schurInvDiag := by
  intro j
  -- Use triangle inequality to bound each off-diagonal Schur block
  calc ∑ i : Fin m, (if i = j then 0 else schurNorm i j)
      ≤ ∑ i : Fin m, (if i = j then 0 else
          (blockNorm i.succ j.succ +
           blockNorm i.succ 0 * normInv * blockNorm 0 j.succ)) := by
        apply Finset.sum_le_sum; intro i _
        split_ifs with h <;> [exact le_refl 0; exact hSchurBound i j]
    _ = ∑ i : Fin m, (if i = j then 0 else blockNorm i.succ j.succ) +
        ∑ i : Fin m, (if i = j then 0 else
          blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
    _ ≤ (invDiagBound j.succ - blockNorm 0 j.succ) +
        normInv * blockNorm 0 j.succ * (invDiagBound 0 - blockNorm j.succ 0) := by
        apply add_le_add
        · -- ∑_{i≠j} ‖A_{i+1,j+1}‖ ≤ invDiagBound(j+1) - ‖A_{0,j+1}‖
          have hdom_j := hDom j.succ
          rw [Fin.sum_univ_succ] at hdom_j
          simp only [show ¬((0 : Fin (m + 1)) = j.succ) from
            fun h => absurd (congr_arg Fin.val h) (by simp)] at hdom_j
          simp_rw [show ∀ k : Fin m, (if k.succ = j.succ then (0 : ℝ)
            else blockNorm k.succ j.succ) =
            if k = j then 0 else blockNorm k.succ j.succ from
            fun k => by congr 1; exact propext Fin.succ_inj] at hdom_j
          simp only [ite_false] at hdom_j
          linarith
        · -- ∑_{i≠j} ‖A_{i+1,0}‖ · normInv · ‖A_{0,j+1}‖
          conv_lhs =>
            arg 2; ext i
            rw [show (if i = j then (0 : ℝ) else
              blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) =
              normInv * blockNorm 0 j.succ *
              (if i = j then 0 else blockNorm i.succ 0) by split_ifs <;> ring]
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hNormInv (hNorm 0 j.succ))
          -- ∑_{i≠j} ‖A_{i+1,0}‖ ≤ invDiagBound(0) - ‖A_{j+1,0}‖
          have hdom_0 := hDom 0
          rw [Fin.sum_univ_succ] at hdom_0
          simp only [ite_true] at hdom_0
          simp_rw [show ∀ k : Fin m, (if k.succ = (0 : Fin (m + 1)) then (0 : ℝ)
            else blockNorm k.succ 0) = blockNorm k.succ 0 from
            fun k => by simp [Fin.succ_ne_zero]] at hdom_0
          -- hdom_0: ∑ k, blockNorm k.succ 0 ≤ invDiagBound 0
          have hsplit : ∑ k : Fin m, blockNorm k.succ 0 =
              blockNorm j.succ 0 +
              ∑ i : Fin m, (if i = j then 0 else blockNorm i.succ 0) := by
            have h1 : ∀ k : Fin m, blockNorm k.succ 0 =
              (if k = j then blockNorm k.succ 0 else 0) +
              (if k = j then 0 else blockNorm k.succ 0) :=
              fun k => by split_ifs <;> simp
            conv_lhs => arg 2; ext k; rw [h1 k]
            rw [Finset.sum_add_distrib]
            congr 1
            simp [Finset.sum_ite_eq', Finset.mem_univ]
          rw [hsplit] at hdom_0; linarith
    _ ≤ invDiagBound j.succ - blockNorm j.succ 0 * normInv * blockNorm 0 j.succ := by
        -- Need: -blockNorm 0 j.succ + normInv * blockNorm 0 j.succ * invDiagBound 0
        --   - normInv * blockNorm 0 j.succ * blockNorm j.succ 0 ≤ 0
        -- i.e., blockNorm 0 j.succ * (normInv * invDiagBound 0 - 1) ≤ 0
        -- From hNormInvBound: normInv * invDiagBound 0 ≤ 1
        nlinarith [hNorm 0 j.succ, hNormInvBound]
    _ ≤ schurInvDiag j := hSchurDiag j

/-- **Theorem 13.7 one-step row inheritance**.

    The source proves the column case and says the row-wise case is analogous.
    This wrapper makes that analogous case explicit by applying the column
    theorem to the transposed block-norm and Schur-norm tables. -/
theorem block_diag_dom_schur_inherit_row {m : ℕ}
    (blockNorm : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (invDiagBound : Fin (m + 1) → ℝ)
    (normInv : ℝ) (hNormInv : 0 ≤ normInv)
    (hDom : IsBlockDiagDomRow (m + 1) blockNorm invDiagBound)
    (hNormInvBound : normInv * invDiagBound 0 ≤ 1)
    (schurNorm : Fin m → Fin m → ℝ)
    (hSchurBound : ∀ i j : Fin m,
      schurNorm i j ≤ blockNorm i.succ j.succ +
        blockNorm i.succ 0 * normInv * blockNorm 0 j.succ)
    (schurInvDiag : Fin m → ℝ)
    (hSchurDiag : ∀ i : Fin m,
      invDiagBound i.succ - blockNorm i.succ 0 * normInv * blockNorm 0 i.succ
        ≤ schurInvDiag i) :
    IsBlockDiagDomRow m schurNorm schurInvDiag := by
  rw [isBlockDiagDomRow_iff_col_transpose]
  exact block_diag_dom_schur_inherit
    (blockNorm := fun i j : Fin (m + 1) => blockNorm j i)
    (hNorm := fun i j => hNorm j i)
    (invDiagBound := invDiagBound)
    (normInv := normInv)
    (hNormInv := hNormInv)
    (hDom := (isBlockDiagDomRow_iff_col_transpose
      (m + 1) blockNorm invDiagBound).1 hDom)
    (hNormInvBound := hNormInvBound)
    (schurNorm := fun i j : Fin m => schurNorm j i)
    (hSchurBound := by
      intro i j
      calc
        schurNorm j i
            ≤ blockNorm j.succ i.succ +
                blockNorm j.succ 0 * normInv * blockNorm 0 i.succ :=
          hSchurBound j i
        _ = blockNorm j.succ i.succ +
                blockNorm 0 i.succ * normInv * blockNorm j.succ 0 := by
          ring)
    (schurInvDiag := schurInvDiag)
    (hSchurDiag := by
      intro i
      convert hSchurDiag i using 1
      ring)

end NumStability
