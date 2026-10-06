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
# Source.Higham.Chapter13.Theorem08.OneStep

This module formalizes the source-facing Chapter 13 statements for
`Theorem08.OneStep`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.1  Theorem 13.8 one-step growth bound
-- ============================================================

/-- **Theorem 13.8 one-step growth bound** (Demmel--Higham--Schreiber).
    For a block diag dom matrix, the Schur complement block column sums
    are bounded by the original column sums. Combined with ∑_i ‖A_{ij}‖ ≤ 2max ‖A_{ij}‖
    (eq. 13.19), this gives max_{k≤i,j≤m} ‖A^(k)_{ij}‖ ≤ 2 max_{i,j} ‖A_{ij}‖. -/
theorem block_diag_dom_growth_bound_step {m : ℕ}
    (blockNorm : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (invDiagBound : Fin (m + 1) → ℝ)
    (normInv : ℝ) (hNormInv : 0 ≤ normInv)
    (hDom : IsBlockDiagDomCol (m + 1) blockNorm invDiagBound)
    (hNormInvBound : normInv * invDiagBound 0 ≤ 1)
    (schurNorm : Fin m → Fin m → ℝ)
    (hSchurBound : ∀ i j : Fin m,
      schurNorm i j ≤ blockNorm i.succ j.succ +
        blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) :
    ∀ j : Fin m, ∑ i : Fin m, schurNorm i j ≤
      ∑ i : Fin (m + 1), blockNorm i j.succ := by
  intro j
  have h_sum_le : ∑ i : Fin m, blockNorm i.succ 0 ≤ invDiagBound 0 := by
    have hdom_0 := hDom 0
    rw [Fin.sum_univ_succ] at hdom_0
    simp only [ite_true] at hdom_0
    simp_rw [show ∀ k : Fin m, (if k.succ = (0 : Fin (m + 1)) then (0 : ℝ)
      else blockNorm k.succ 0) = blockNorm k.succ 0 from
      fun k => by simp [Fin.succ_ne_zero]] at hdom_0
    linarith
  calc ∑ i : Fin m, schurNorm i j
      ≤ ∑ i : Fin m, (blockNorm i.succ j.succ +
          blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) :=
        Finset.sum_le_sum (fun i _ => hSchurBound i j)
    _ = ∑ i : Fin m, blockNorm i.succ j.succ +
        (∑ i : Fin m, blockNorm i.succ 0) * normInv * blockNorm 0 j.succ := by
        rw [Finset.sum_add_distrib]; congr 1
        rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ∑ i : Fin m, blockNorm i.succ j.succ + blockNorm 0 j.succ := by
        nlinarith [hNorm 0 j.succ, hNormInvBound,
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h_sum_le hNormInv) (hNorm 0 j.succ)]
    _ = ∑ i : Fin (m + 1), blockNorm i j.succ := by
        rw [Fin.sum_univ_succ]; ring

end NumStability
