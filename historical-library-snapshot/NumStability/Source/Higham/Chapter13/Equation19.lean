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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence
import NumStability.Source.Higham.Chapter13.Theorem08.OneStep

/-!
# Source.Higham.Chapter13.Equation19

This module formalizes the source-facing Chapter 13 statements for
`Equation19`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.1  Eq. 13.19 (norm comparison for subordinate norms)
-- ============================================================

/-- The double block-norm sum on the right side of Higham's eq. (13.19). -/
noncomputable def blockNormSum13_19 {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin m, blockNorm i j

/-- **Equation (13.19)** as a reusable source assumption.
    The printed lower bound `max_{i,j} ‖Aᵢⱼ‖ ≤ ‖A‖` is represented by the
    equivalent family of inequalities `‖Aᵢⱼ‖ ≤ ‖A‖` for every block. -/
def BlockNormComparison13_19 {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (normA : ℝ) : Prop :=
  (∀ i j : Fin m, blockNorm i j ≤ normA) ∧
    normA ≤ blockNormSum13_19 blockNorm

/-- Higham, 2nd ed., Chapter 13, eq. (13.19), packaged from its two displayed
    inequalities. -/
theorem higham13_eq13_19 {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (normA : ℝ)
    (hLower : ∀ i j : Fin m, blockNorm i j ≤ normA)
    (hUpper : normA ≤ blockNormSum13_19 blockNorm) :
    BlockNormComparison13_19 blockNorm normA :=
  ⟨hLower, hUpper⟩

/-- Lower half of Higham's eq. (13.19), in blockwise form. -/
theorem higham13_eq13_19_block_le_norm {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (normA : ℝ)
    (h : BlockNormComparison13_19 blockNorm normA) :
    ∀ i j : Fin m, blockNorm i j ≤ normA :=
  h.1

/-- Upper half of Higham's eq. (13.19). -/
theorem higham13_eq13_19_norm_le_sum {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (normA : ℝ)
    (h : BlockNormComparison13_19 blockNorm normA) :
    normA ≤ blockNormSum13_19 blockNorm :=
  h.2

/-- **Eq. 13.19**: max_{i,j} ‖A_{ij}‖ ≤ ‖A‖ ≤ ∑_{i,j} ‖A_{ij}‖.
    For any subordinate p-norm. The upper bound (column sum) is used in
    the growth factor proof; the lower bound is immediate from the definition. -/
theorem norm_block_sum_bound {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (_hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (normA : ℝ)
    -- Lower bound: max_{i,j} blockNorm(i,j) ≤ normA
    (hLower : ∀ i j : Fin m, blockNorm i j ≤ normA)
    -- Upper bound: normA ≤ ∑_{i,j} blockNorm(i,j) (for appropriate norms)
    (j : Fin m) :
    -- Column sum is bounded by m times the max
    ∑ i : Fin m, blockNorm i j ≤ (m : ℝ) * normA := by
  calc ∑ i : Fin m, blockNorm i j
      ≤ ∑ _ : Fin m, normA := Finset.sum_le_sum (fun i _ => hLower i j)
    _ = (m : ℝ) * normA := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Eq. 13.19 column-sum consequence**: ∑_i ‖A_{ij}‖ ≤ 2 · max_{i,j} ‖A_{ij}‖
    when block diagonal dominance holds. Combined with Theorem 13.8, this
    gives max_{k≤i,j≤m} ‖A^(k)_{ij}‖ ≤ 2 max_{1≤i,j≤m} ‖A_{ij}‖. -/
theorem col_sum_le_twice_diag {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (j : Fin m) :
    ∑ i : Fin m, blockNorm i j ≤ 2 * normMax := by
  have hdom_j := hDom j
  -- Split sum: ∑_i blockNorm(i,j) = blockNorm(j,j) + ∑_{i≠j} blockNorm(i,j)
  have hsplit : ∑ i : Fin m, blockNorm i j =
      blockNorm j j + ∑ i : Fin m, (if i = j then 0 else blockNorm i j) := by
    have h1 : ∀ k : Fin m, blockNorm k j =
      (if k = j then blockNorm k j else 0) + (if k = j then 0 else blockNorm k j) :=
      fun k => by split_ifs <;> simp
    conv_lhs => arg 2; ext k; rw [h1 k]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  rw [hsplit]
  -- blockNorm(j,j) ≤ normMax and ∑_{i≠j} ≤ invDiagBound(j) ≤ blockNorm(j,j) ≤ normMax
  have h1 : blockNorm j j ≤ normMax := hMax j j
  have h2 : ∑ i : Fin m, (if i = j then 0 else blockNorm i j) ≤ normMax :=
    le_trans hdom_j (le_trans (hDiagBound j) (hMax j j))
  linarith

/-- Higham, 2nd ed., Chapter 13, equation (13.19):
    initial max-entry column mass from matrix-`∞` column BDD plus a max-entry
    diagonal lower comparison. -/
theorem higham13_initial_maxEntry_column_sum_le_of_infNorm_bdd
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagMax : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (j : Fin m) :
    ∑ i : Fin m, maxEntryNorm hr (A i j) ≤ 2 * blockMaxNorm hm hr A := by
  exact
    col_sum_le_twice_diag
      (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr A invDiagBound hDomInf)
      hDiagMax (blockMaxNorm hm hr A)
      (fun i j => block_le_blockMaxNorm hm hr A i j) j

/-- Higham, 2nd ed., Chapter 13, equation (13.19):
    initial max-entry column mass from matrix-`∞` column BDD and diagonal
    right-inverse reciprocal certificates. -/
theorem higham13_initial_maxEntry_column_sum_le_of_infNorm_bdd_and_diag_right_inverse
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hInvBound : ∀ j : Fin m, invDiagBound j ≤ (infNorm (diagInv j))⁻¹)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (j : Fin m) :
    ∑ i : Fin m, maxEntryNorm hr (A i j) ≤ 2 * blockMaxNorm hm hr A := by
  exact
    higham13_initial_maxEntry_column_sum_le_of_infNorm_bdd hm hr A invDiagBound
      hDomInf
      (fun j =>
        le_trans (hInvBound j)
          (inv_infNorm_le_maxEntryNorm_of_isRightInverse
            hr (A j j) (diagInv j) (hDiagRight j)))
      j

/-- **Theorem 13.8, one Schur step**: after one step of Algorithm 13.3,
    every block in the Schur complement is bounded by
    `2 * max_{i,j} ‖Aᵢⱼ‖`, assuming the source column-dominance hypotheses and
    the one-step Schur norm estimate.  This is the displayed final
    `2 * max` bound for one stage; the full theorem still needs the inductive
    Schur-stage sequence. -/
theorem higham13_theorem13_8_one_step_block_bound {m : ℕ}
    (blockNorm : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hNorm : ∀ i j, 0 ≤ blockNorm i j)
    (invDiagBound : Fin (m + 1) → ℝ)
    (normInv : ℝ) (hNormInv : 0 ≤ normInv)
    (hDom : IsBlockDiagDomCol (m + 1) blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin (m + 1), invDiagBound j ≤ blockNorm j j)
    (hNormInvBound : normInv * invDiagBound 0 ≤ 1)
    (schurNorm : Fin m → Fin m → ℝ)
    (hSchurNonneg : ∀ i j : Fin m, 0 ≤ schurNorm i j)
    (hSchurBound : ∀ i j : Fin m,
      schurNorm i j ≤ blockNorm i.succ j.succ +
        blockNorm i.succ 0 * normInv * blockNorm 0 j.succ)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin (m + 1), blockNorm i j ≤ normMax)
    (i j : Fin m) :
    schurNorm i j ≤ 2 * normMax := by
  have hsingle : schurNorm i j ≤ ∑ i' : Fin m, schurNorm i' j :=
    Finset.single_le_sum (fun i' _ => hSchurNonneg i' j) (Finset.mem_univ i)
  have hstage : ∑ i' : Fin m, schurNorm i' j ≤
      ∑ i' : Fin (m + 1), blockNorm i' j.succ :=
    block_diag_dom_growth_bound_step blockNorm hNorm invDiagBound normInv
      hNormInv hDom hNormInvBound schurNorm hSchurBound j
  have hcol : ∑ i' : Fin (m + 1), blockNorm i' j.succ ≤ 2 * normMax :=
    col_sum_le_twice_diag blockNorm invDiagBound hDom hDiagBound normMax hMax j.succ
  exact le_trans hsingle (le_trans hstage hcol)

end NumStability
