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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement

/-!
# Source.Higham.Chapter13.Algorithm03

This module formalizes the source-facing Chapter 13 statements for
`Algorithm03`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **One explicit step of block LU factorization** (Higham, 2nd ed.,
    Algorithm 13.3).

    This is the named-factor version of `block_lu_one_step`: it proves that the
    concrete factors `blockLUOneStepL` and `blockLUOneStepU` multiply to `A`
    whenever the leading block inverse and Schur-tail factorization data are
    supplied.  The explicit factor names are used in the Theorem 13.2 converse
    spine to lift Schur-tail factorizations back to full factorizations. -/
theorem block_lu_one_step_explicit {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (hInv : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A (0 : Fin (m + 1)) (0 : Fin (m + 1)) l t =
        if s = t then 1 else 0)
    (L_S U_S : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hS : BlockLUFactSpec m r (blockSchur A A11_inv) L_S U_S) :
    BlockLUFactSpec (m + 1) r A
      (blockLUOneStepL A A11_inv L_S)
      (blockLUOneStepU A U_S) := by
  let L := blockLUOneStepL A A11_inv L_S
  let U := blockLUOneStepU A U_S
  change BlockLUFactSpec (m + 1) r A L U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst hi; simp [L, blockLUOneStepL]
    · simp only [L, blockLUOneStepL, dif_neg hi]; exact hS.L_diag (i.pred hi)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := by intro h; subst h; exact lt_irrefl _ hij
      simp [L, blockLUOneStepL, hj]
    · have hj : j ≠ 0 := by intro h; subst h; exact absurd hij (Nat.not_lt_zero _)
      simp only [L, blockLUOneStepL, dif_neg hi, dif_neg hj]
      exact hS.L_upper_zero _ _ (by
        have := Fin.val_pred j hj; have := Fin.val_pred i hi
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi; exact absurd hij (Nat.not_lt_zero _)
    · by_cases hj : j = 0
      · subst hj; simp [U, blockLUOneStepU, hi]
      · simp only [U, blockLUOneStepU, dif_neg hi, dif_neg hj]
        exact hS.U_lower_zero _ _ (by
          have := Fin.val_pred j hj; have := Fin.val_pred i hi
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
  · intro i j s t
    rw [Fin.sum_univ_succ]
    have hL0 : ∀ p, L 0 p = if p = 0 then idBlock r else zeroBlock r :=
      fun p => by simp [L, blockLUOneStepL]
    have hU0 : ∀ p, U 0 p = A 0 p :=
      fun p => by simp [U, blockLUOneStepU]
    have hL0s : ∀ k : Fin m, L 0 (Fin.succ k) = zeroBlock r :=
      fun k => by rw [hL0]; simp [Fin.succ_ne_zero]
    have hLs0 : ∀ k : Fin m, L (Fin.succ k) 0 =
        fun s t => ∑ l, A (Fin.succ k) 0 s l * A11_inv l t :=
      fun k => by simp [L, blockLUOneStepL, Fin.succ_ne_zero]
    have hLss : ∀ (p q : Fin m), L (Fin.succ p) (Fin.succ q) = L_S p q :=
      fun p q => by simp [L, blockLUOneStepL, Fin.succ_ne_zero, Fin.pred_succ]
    have hUs0 : ∀ k : Fin m, U (Fin.succ k) 0 = zeroBlock r :=
      fun k => by simp [U, blockLUOneStepU, Fin.succ_ne_zero]
    have hUss : ∀ (p q : Fin m), U (Fin.succ p) (Fin.succ q) = U_S p q :=
      fun p q => by simp [U, blockLUOneStepU, Fin.succ_ne_zero, Fin.pred_succ]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi; subst hj
      rw [hL0 0, if_pos rfl, hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      simp only [idBlock]
      conv_lhs =>
        arg 2
        ext l
        rw [show (if s = l then (1 : ℝ) else 0) * A 0 0 l t =
          if s = l then A 0 0 l t else 0 by split_ifs <;> simp]
      simp [Finset.mem_univ]
    · subst hi
      rw [hL0 0, if_pos rfl, hU0 j]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) j l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      simp only [idBlock]
      conv_lhs =>
        arg 2
        ext l
        rw [show (if s = l then (1 : ℝ) else 0) * A 0 j l t =
          if s = l then A 0 j l t else 0 by split_ifs <;> simp]
      simp [Finset.mem_univ]
    · subst hj; rw [hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L i (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hUs0 k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, hInv]
      simp_rw [mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    · rw [hU0 j]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0]
      have hsec : ∀ (k : Fin m) (l : Fin r),
          L i (Fin.succ k) s l * U (Fin.succ k) j l t =
          L_S (i.pred hi) k s l * U_S k (j.pred hj) l t := by
        intro k l
        have hLeq : L i (Fin.succ k) = L_S (i.pred hi) k := by
          have := hLss (i.pred hi) k; rwa [Fin.succ_pred i hi] at this
        have hUeq : U (Fin.succ k) j = U_S k (j.pred hj) := by
          have := hUss k (j.pred hj); rwa [Fin.succ_pred j hj] at this
        rw [hLeq, hUeq]
      simp_rw [hsec]
      have hprod := hS.product_eq (i.pred hi) (j.pred hj) s t
      simp only [blockSchur, Fin.succ_pred] at hprod
      rw [hprod]
      have hfirst : ∑ l : Fin r,
          (∑ l' : Fin r, A i 0 s l' * A11_inv l' l) * A 0 j l t =
          ∑ l₁ : Fin r, ∑ l₂ : Fin r,
            A i 0 s l₁ * A11_inv l₁ l₂ * A 0 j l₂ t := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
      linarith

/-- **Algorithm 13.3**, exact output check for block LU recursion.
    With `U₁₁ = A₁₁`, `U₁₂ = A₁₂`, `L₂₁ A₁₁ = A₂₁`,
    `S = A₂₂ - L₂₁ A₁₂`, and recursive factors `S = L₂₂ U₂₂`, the assembled
    block LU factors multiply to the original matrix. -/
theorem higham13_algorithm13_3_block_lu_reconstructs
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (A11 : Matrix m m α) (A12 : Matrix m n α)
    (L21 A21 : Matrix n m α) (L22 U22 S A22 : Matrix n n α)
    (h21 : L21 * A11 = A21) (hSfact : L22 * U22 = S)
    (hSdef : S = A22 - L21 * A12) :
    Matrix.fromBlocks A11 A12 A21 A22 =
      Matrix.fromBlocks 1 0 L21 L22 * Matrix.fromBlocks A11 A12 0 U22 := by
  rw [Matrix.fromBlocks_multiply]
  simp [h21, hSfact, hSdef]

end NumStability
