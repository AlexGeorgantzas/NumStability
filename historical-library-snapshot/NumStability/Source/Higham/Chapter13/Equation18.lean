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
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter13.Equation18

This module formalizes the source-facing Chapter 13 statements for
`Equation18`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.1  Equation 13.18 proof-chain pieces
-- ============================================================

/-- **Equation (13.18), min-step abstraction**.

    Higham's proof uses the reverse triangle inequality to pass from
    `min_{‖x‖=1} ‖A_jj x‖ - c` to
    `min_{‖x‖=1} ‖(A_jj - A_j1 A_11^{-1} A_1j) x‖`.  This lemma records that
    normed-space step without choosing a concrete subordinate matrix norm. -/
theorem higham13_eq13_18_min_lower_bound {E : Type*}
    [SeminormedAddCommGroup E]
    (diag perturb schur : E → E) (diagMin schurMin perturbBound : ℝ)
    (hDiagMin : ∀ x : E, ‖x‖ = 1 → diagMin ≤ ‖diag x‖)
    (hSchurMin : ∃ x : E, ‖x‖ = 1 ∧ schurMin = ‖schur x‖)
    (hPerturb : ∀ x : E, ‖x‖ = 1 → ‖perturb x‖ ≤ perturbBound)
    (hSchur : ∀ x : E, schur x = diag x - perturb x) :
    diagMin - perturbBound ≤ schurMin := by
  rcases hSchurMin with ⟨x, hxUnit, hxMin⟩
  calc
    diagMin - perturbBound ≤ ‖diag x‖ - perturbBound :=
      sub_le_sub_right (hDiagMin x hxUnit) perturbBound
    _ ≤ ‖diag x‖ - ‖perturb x‖ :=
      sub_le_sub_left (hPerturb x hxUnit) ‖diag x‖
    _ ≤ ‖diag x - perturb x‖ := norm_sub_norm_le (diag x) (perturb x)
    _ = schurMin := by rw [← hSchur x, hxMin]

/-- **Equation (13.18), Euclidean min-step abstraction**.

    This is the explicit `vecNorm2` version of
    `higham13_eq13_18_min_lower_bound`.  It is used when the block norm is
    represented by the repository's concrete finite-vector Euclidean norm rather
    than by the ambient typeclass norm on `Fin r → ℝ`. -/
theorem higham13_eq13_18_vecNorm2_min_lower_bound {r : ℕ}
    (diag perturb schur : (Fin r → ℝ) → (Fin r → ℝ))
    (diagMin schurMin perturbBound : ℝ)
    (hDiagMin : ∀ x : Fin r → ℝ, vecNorm2 x = 1 →
      diagMin ≤ vecNorm2 (diag x))
    (hSchurMin : ∃ x : Fin r → ℝ, vecNorm2 x = 1 ∧
      schurMin = vecNorm2 (schur x))
    (hPerturb : ∀ x : Fin r → ℝ, vecNorm2 x = 1 →
      vecNorm2 (perturb x) ≤ perturbBound)
    (hSchur : ∀ x : Fin r → ℝ,
      schur x = fun i => diag x i - perturb x i) :
    diagMin - perturbBound ≤ schurMin := by
  rcases hSchurMin with ⟨x, hxUnit, hxMin⟩
  calc
    diagMin - perturbBound ≤ vecNorm2 (diag x) - perturbBound :=
      sub_le_sub_right (hDiagMin x hxUnit) perturbBound
    _ ≤ vecNorm2 (diag x) - vecNorm2 (perturb x) :=
      sub_le_sub_left (hPerturb x hxUnit) (vecNorm2 (diag x))
    _ ≤ vecNorm2 (fun i => diag x i - perturb x i) :=
      (le_abs_self _).trans
        (abs_vecNorm2_sub_le_vecNorm2_sub (diag x) (perturb x))
    _ = schurMin := by rw [← hSchur x, hxMin]

/-- **Equation (13.18), scalar column-chain part**.

    From block column diagonal dominance (13.17), submultiplicativity for
    `‖A_11^{-1}‖`, and the Schur off-diagonal triangle bound, the off-diagonal
    column sum in the first Schur complement is bounded by
    `‖A_jj^{-1}‖^{-1} - ‖A_j1‖‖A_11^{-1}‖‖A_1j‖`. -/
theorem higham13_eq13_18_scalar_column_chain {m : ℕ}
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
    ∀ j : Fin m,
      ∑ i : Fin m, (if i = j then 0 else schurNorm i j) ≤
        invDiagBound j.succ - blockNorm j.succ 0 * normInv * blockNorm 0 j.succ := by
  intro j
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
        · have hdom_j := hDom j.succ
          rw [Fin.sum_univ_succ] at hdom_j
          simp only [show ¬((0 : Fin (m + 1)) = j.succ) from
            fun h => absurd (congr_arg Fin.val h) (by simp)] at hdom_j
          simp_rw [show ∀ k : Fin m, (if k.succ = j.succ then (0 : ℝ)
            else blockNorm k.succ j.succ) =
            if k = j then 0 else blockNorm k.succ j.succ from
            fun k => by congr 1; exact propext Fin.succ_inj] at hdom_j
          simp only [ite_false] at hdom_j
          linarith
        · conv_lhs =>
            arg 2; ext i
            rw [show (if i = j then (0 : ℝ) else
              blockNorm i.succ 0 * normInv * blockNorm 0 j.succ) =
              normInv * blockNorm 0 j.succ *
              (if i = j then 0 else blockNorm i.succ 0) by split_ifs <;> ring]
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hNormInv (hNorm 0 j.succ))
          have hdom_0 := hDom 0
          rw [Fin.sum_univ_succ] at hdom_0
          simp only [ite_true] at hdom_0
          simp_rw [show ∀ k : Fin m, (if k.succ = (0 : Fin (m + 1)) then (0 : ℝ)
            else blockNorm k.succ 0) = blockNorm k.succ 0 from
            fun k => by simp [Fin.succ_ne_zero]] at hdom_0
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
        nlinarith [hNorm 0 j.succ, hNormInvBound]

/-- **Equation (13.18), source-facing Schur column dominance wrapper**.

    The theorem combines the scalar column chain with the min/reverse-triangle
    step.  `diag`, `perturb`, and `schurDiag` abstract the actions of
    `A_jj`, `A_j1 A_11^{-1} A_1j`, and the diagonal Schur block on unit vectors.
    The full Theorem 13.7 still also needs the induction and nonsingularity
    argument around this one-step proof chain. -/
theorem higham13_eq13_18_schur_column_dominance {m : ℕ} {E : Type*}
    [SeminormedAddCommGroup E]
    (blockNorm : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (invDiagBound : Fin (m + 1) → ℝ)
    (normInv : ℝ) (hNormInv : 0 ≤ normInv)
    (hDom : IsBlockDiagDomCol (m + 1) blockNorm invDiagBound)
    (hNormInvBound : normInv * invDiagBound 0 ≤ 1)
    (schurNorm : Fin m → Fin m → ℝ)
    (hSchurBound : ∀ i j : Fin m,
      schurNorm i j ≤ blockNorm i.succ j.succ +
        blockNorm i.succ 0 * normInv * blockNorm 0 j.succ)
    (diag perturb schurDiag : Fin m → E → E)
    (schurDiagMin : Fin m → ℝ)
    (hDiagMin : ∀ j : Fin m, ∀ x : E, ‖x‖ = 1 →
      invDiagBound j.succ ≤ ‖diag j x‖)
    (hSchurMin : ∀ j : Fin m,
      ∃ x : E, ‖x‖ = 1 ∧ schurDiagMin j = ‖schurDiag j x‖)
    (hPerturb : ∀ j : Fin m, ∀ x : E, ‖x‖ = 1 →
      ‖perturb j x‖ ≤ blockNorm j.succ 0 * normInv * blockNorm 0 j.succ)
    (hSchurDiag : ∀ j : Fin m, ∀ x : E,
      schurDiag j x = diag j x - perturb j x) :
    IsBlockDiagDomCol m schurNorm schurDiagMin := by
  intro j
  calc
    ∑ i : Fin m, (if i = j then 0 else schurNorm i j)
        ≤ invDiagBound j.succ - blockNorm j.succ 0 * normInv * blockNorm 0 j.succ :=
      higham13_eq13_18_scalar_column_chain blockNorm hNorm invDiagBound normInv
        hNormInv hDom hNormInvBound schurNorm hSchurBound j
    _ ≤ schurDiagMin j :=
      higham13_eq13_18_min_lower_bound (diag j) (perturb j) (schurDiag j)
        (invDiagBound j.succ) (schurDiagMin j)
        (blockNorm j.succ 0 * normInv * blockNorm 0 j.succ)
        (hDiagMin j) (hSchurMin j) (hPerturb j) (hSchurDiag j)

end NumStability
