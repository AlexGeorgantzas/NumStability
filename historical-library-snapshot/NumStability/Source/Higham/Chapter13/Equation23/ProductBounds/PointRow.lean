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
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation22

/-!
# Higham Chapter 13, equation (13.23) point-row product bounds

Canonical declaration owner created by the frozen B0004/R12 route map.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics

/-- Source-shaped scalar bridge for Higham eq. (13.23): specializing the
    general growth-factor product bound (13.22) with `ρ_n ≤ 2` gives
    `‖L‖‖U‖ ≤ 8 n κ(A) ‖A‖`.  The premises `‖L‖ ≤ nρ_n^2κ(A)` and
    `‖U‖ ≤ ρ_n‖A‖` are still the source obligations supplied by Problem 13.4
    and (13.21). -/
theorem higham13_eq13_23_point_row_from_growth
    (normL normU normA rho kappa : ℝ) (n : ℕ)
    (hU : 0 ≤ normU) (hA : 0 ≤ normA)
    (hRho_nonneg : 0 ≤ rho) (hRho_le_two : rho ≤ 2) (hKappa : 0 ≤ kappa)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa)
    (hNormU : normU ≤ rho * normA) :
    normL * normU ≤ 8 * (n : ℝ) * kappa * normA := by
  have h22 :
      normL * normU ≤ (n : ℝ) * rho ^ 3 * kappa * normA :=
    block_lu_normLU_bound_general_higham_13_22
      normL normU normA rho kappa n hU hRho_nonneg hKappa hNormL hNormU
  have hrho3 : rho ^ 3 ≤ 8 := by
    have hpow : rho ^ 3 ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hRho_nonneg hRho_le_two 3
    norm_num at hpow
    exact hpow
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcoef_left : (n : ℝ) * rho ^ 3 ≤ (n : ℝ) * 8 :=
    mul_le_mul_of_nonneg_left hrho3 hn
  have hcoef : (n : ℝ) * rho ^ 3 * kappa ≤ (n : ℝ) * 8 * kappa :=
    mul_le_mul_of_nonneg_right hcoef_left hKappa
  have hprod :
      (n : ℝ) * rho ^ 3 * kappa * normA ≤
        (n : ℝ) * 8 * kappa * normA :=
    mul_le_mul_of_nonneg_right hcoef hA
  calc
    normL * normU ≤ (n : ℝ) * rho ^ 3 * kappa * normA := h22
    _ ≤ (n : ℝ) * 8 * kappa * normA := hprod
    _ = 8 * (n : ℝ) * kappa * normA := by ring

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    point-row product specialization from an instantiated ambient-budget chain.

    This is the chain-level analogue of `higham13_eq13_23_point_row_from_growth`:
    an Eq.13.22-budget chain plus the source-side `rho <= 2` hypothesis gives
    concrete block LU factors satisfying `8 n kappa(A) ||A||`.  Proving the
    chain and the final point-row `rho <= 2` condition remains the source
    obligation. -/
theorem Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product {r : ℕ}
    (hr : 0 < r) {rho kappa normA : ℝ} (n : ℕ) :
    ∀ {m : ℕ}
      {A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13BlockLUBudgetChain hr ((n : ℝ) * rho ^ 2 * kappa) (rho * normA)
        m A pivotInv →
      0 ≤ normA →
      0 ≤ rho →
      rho ≤ 2 →
      0 ≤ kappa →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r A L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
                8 * (n : ℝ) * kappa * normA := by
  intro m A pivotInv hchain hA hRho hRho_le_two hKappa
  rcases Higham13BlockLUBudgetChain.exists_blockLUFact_norms
      (r := r) hr
      (C_L := (n : ℝ) * rho ^ 2 * kappa)
      (C_U := rho * normA) hchain with
    ⟨L, U, hFact, hL, hU⟩
  refine ⟨L, U, hFact, ?_⟩
  exact higham13_eq13_23_point_row_from_growth
    (blockMaxNorm (Nat.succ_pos m) hr L)
    (blockMaxNorm (Nat.succ_pos m) hr U)
    normA rho kappa n
    (blockMaxNorm_nonneg (Nat.succ_pos m) hr U)
    hA hRho hRho_le_two hKappa hL hU

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    exact-`kappa(A)` source specialization of the ambient-budget chain.

    After the recursive chain has been instantiated with the exact source
    constants and the source row-growth theorem supplies `rho <= 2`, this gives
    the displayed point-row product bound. -/
theorem Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
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
      growthFactorEntry hN A0 G hApos ≤ 2 →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r A L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
                8 * (n : ℝ) *
                  (maxEntryNormRect hN hN A0 *
                    maxEntryNormRect hN hN Ainv) *
                  maxEntryNormRect hN hN A0 := by
  intro m A pivotInv hchain hRho_le_two
  let rho : ℝ := growthFactorEntry hN A0 G hApos
  let kappaA : ℝ := maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv
  let normA : ℝ := maxEntryNormRect hN hN A0
  have hNormA : 0 ≤ normA := by
    simpa [normA] using maxEntryNormRect_nonneg hN hN A0
  have hRho : 0 ≤ rho := by
    simpa [rho] using growthFactorEntry_nonneg hN A0 G hApos
  have hKappa : 0 ≤ kappaA := by
    exact mul_nonneg (maxEntryNormRect_nonneg hN hN A0)
      (maxEntryNormRect_nonneg hN hN Ainv)
  simpa [rho, kappaA, normA] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product
      (r := r) hr (rho := rho) (kappa := kappaA) (normA := normA) n
      hchain hNormA hRho (by simpa [rho] using hRho_le_two) hKappa

end NumStability
