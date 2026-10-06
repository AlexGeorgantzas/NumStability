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
import NumStability.Source.Higham.Chapter13.Algorithm03
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization

/-!
# Source.Higham.Chapter13.Theorem02.Uniqueness

This module formalizes the source-facing Chapter 13 statements for
`Theorem02.Uniqueness`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 one-step uniqueness spine:
    in any block LU factorization, the first block row of `U` is the first
    block row of `A`. -/
theorem BlockLUFactSpec.firstRow_eq {m r : ℕ}
    {A L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hLU : BlockLUFactSpec (m + 1) r A L U) :
    ∀ j : Fin (m + 1), U 0 j = A 0 j := by
  intro j
  ext s t
  have hprod := hLU.product_eq 0 j s t
  rw [Fin.sum_univ_succ] at hprod
  have hdiag : L 0 0 = idBlock r := hLU.L_diag 0
  have htail_zero :
      ∑ k : Fin m, ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) j l t = 0 := by
    apply Finset.sum_eq_zero
    intro k _hk
    have hzero : L 0 (Fin.succ k) = zeroBlock r := by
      exact hLU.L_upper_zero 0 (Fin.succ k) (by simp)
    simp [hzero, zeroBlock]
  have hfirst : ∑ l : Fin r, L 0 0 s l * U 0 j l t = U 0 j s t := by
    rw [hdiag]
    simp only [idBlock]
    conv_lhs =>
      arg 2
      ext l
      rw [show (if s = l then (1 : ℝ) else 0) * U 0 j l t =
        if s = l then U 0 j l t else 0 by split_ifs <;> simp]
    simp [Finset.mem_univ]
  linarith

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 one-step uniqueness spine:
    if the leading block has a right inverse, then the first block column of
    `L` below the diagonal is forced to be `A₂₁ A₁₁⁻¹`. -/
theorem BlockLUFactSpec.firstColumnBelow_eq_of_right_inverse {m r : ℕ}
    {A L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hLU : BlockLUFactSpec (m + 1) r A L U)
    (A11_inv : Fin r → Fin r → ℝ)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0) :
    ∀ i : Fin m,
      L (Fin.succ i) 0 = fun s t =>
        ∑ l : Fin r, A (Fin.succ i) 0 s l * A11_inv l t := by
  intro i
  ext s t
  have hU00 : U 0 0 = A 0 0 := hLU.firstRow_eq 0
  have hmul : ∀ q : Fin r,
      ∑ l : Fin r, L (Fin.succ i) 0 s l * A 0 0 l q =
        A (Fin.succ i) 0 s q := by
    intro q
    have hprod := hLU.product_eq (Fin.succ i) 0 s q
    rw [Fin.sum_univ_succ] at hprod
    have htail_zero :
        ∑ k : Fin m,
          ∑ l : Fin r, L (Fin.succ i) (Fin.succ k) s l *
            U (Fin.succ k) 0 l q = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      have hzero : U (Fin.succ k) 0 = zeroBlock r := by
        exact hLU.U_lower_zero (Fin.succ k) 0 (by simp)
      simp [hzero, zeroBlock]
    have hfirst :
        ∑ l : Fin r, L (Fin.succ i) 0 s l * U 0 0 l q =
          ∑ l : Fin r, L (Fin.succ i) 0 s l * A 0 0 l q := by
      rw [hU00]
    linarith
  calc
    L (Fin.succ i) 0 s t
        = ∑ l : Fin r, L (Fin.succ i) 0 s l * (if l = t then 1 else 0) := by
            symm
            simp_rw [mul_ite, mul_one, mul_zero]
            simp [Finset.sum_ite_eq', Finset.mem_univ]
    _ = ∑ l : Fin r,
          L (Fin.succ i) 0 s l *
            (∑ q : Fin r, A 0 0 l q * A11_inv q t) := by
            simp_rw [hInvRight]
    _ = ∑ q : Fin r,
          (∑ l : Fin r, L (Fin.succ i) 0 s l * A 0 0 l q) * A11_inv q t := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            congr
            ext q
            rw [Finset.sum_mul]
            simp_rw [mul_assoc]
    _ = ∑ q : Fin r, A (Fin.succ i) 0 s q * A11_inv q t := by
            simp_rw [hmul]

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 one-step induction spine:
    any block LU factorization of `A` restricts to a block LU factorization of
    the Schur complement after the first block is eliminated. -/
theorem BlockLUFactSpec.schurTailFactSpec_of_right_inverse {m r : ℕ}
    {A L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hLU : BlockLUFactSpec (m + 1) r A L U)
    (A11_inv : Fin r → Fin r → ℝ)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0) :
    BlockLUFactSpec m r (blockSchur A A11_inv)
      (fun i j => L (Fin.succ i) (Fin.succ j))
      (fun i j => U (Fin.succ i) (Fin.succ j)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact hLU.L_diag (Fin.succ i)
  · intro i j hij
    exact hLU.L_upper_zero (Fin.succ i) (Fin.succ j) (by simpa using hij)
  · intro i j hij
    exact hLU.U_lower_zero (Fin.succ i) (Fin.succ j) (by simpa using hij)
  · intro i j s t
    have hprod := hLU.product_eq (Fin.succ i) (Fin.succ j) s t
    rw [Fin.sum_univ_succ] at hprod
    have hUrow : U 0 (Fin.succ j) = A 0 (Fin.succ j) :=
      hLU.firstRow_eq (Fin.succ j)
    have hLcol :
        L (Fin.succ i) 0 = fun s t =>
          ∑ l : Fin r, A (Fin.succ i) 0 s l * A11_inv l t :=
      hLU.firstColumnBelow_eq_of_right_inverse A11_inv hInvRight i
    have hfirst :
        ∑ l : Fin r, L (Fin.succ i) 0 s l * U 0 (Fin.succ j) l t =
          ∑ l₁ : Fin r, ∑ l₂ : Fin r,
            A (Fin.succ i) 0 s l₁ * A11_inv l₁ l₂ *
              A 0 (Fin.succ j) l₂ t := by
      rw [hLcol, hUrow]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    have htail :
        ∑ k : Fin m,
          ∑ l : Fin r,
            L (Fin.succ i) (Fin.succ k) s l *
              U (Fin.succ k) (Fin.succ j) l t =
          A (Fin.succ i) (Fin.succ j) s t -
            ∑ l₁ : Fin r, ∑ l₂ : Fin r,
              A (Fin.succ i) 0 s l₁ * A11_inv l₁ l₂ *
                A 0 (Fin.succ j) l₂ t := by
      linarith
    simpa [blockSchur] using htail

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 one-step uniqueness spine:
    if the Schur-complement block LU factorization is unique, then the full
    one-step block LU factorization is unique. -/
theorem BlockLUFactSpec.eq_of_schurTail_unique_of_right_inverse {m r : ℕ}
    {A L₁ U₁ L₂ U₂ : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (h₁ : BlockLUFactSpec (m + 1) r A L₁ U₁)
    (h₂ : BlockLUFactSpec (m + 1) r A L₂ U₂)
    (A11_inv : Fin r → Fin r → ℝ)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hTailUnique :
      ∀ Ls₁ Us₁ Ls₂ Us₂ : Fin m → Fin m → (Fin r → Fin r → ℝ),
        BlockLUFactSpec m r (blockSchur A A11_inv) Ls₁ Us₁ →
        BlockLUFactSpec m r (blockSchur A A11_inv) Ls₂ Us₂ →
        Ls₁ = Ls₂ ∧ Us₁ = Us₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  let Ls₁ : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => L₁ (Fin.succ i) (Fin.succ j)
  let Us₁ : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => U₁ (Fin.succ i) (Fin.succ j)
  let Ls₂ : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => L₂ (Fin.succ i) (Fin.succ j)
  let Us₂ : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => U₂ (Fin.succ i) (Fin.succ j)
  have htail₁ : BlockLUFactSpec m r (blockSchur A A11_inv) Ls₁ Us₁ :=
    h₁.schurTailFactSpec_of_right_inverse A11_inv hInvRight
  have htail₂ : BlockLUFactSpec m r (blockSchur A A11_inv) Ls₂ Us₂ :=
    h₂.schurTailFactSpec_of_right_inverse A11_inv hInvRight
  have htail := hTailUnique Ls₁ Us₁ Ls₂ Us₂ htail₁ htail₂
  constructor
  · ext i j s t
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        rw [h₁.L_diag 0, h₂.L_diag 0]
      · have hlt : (0 : Fin (m + 1)).val < j.val := by
          have hjval : j.val ≠ 0 := fun h => hj (Fin.ext h)
          simpa using Nat.pos_of_ne_zero hjval
        rw [h₁.L_upper_zero 0 j hlt, h₂.L_upper_zero 0 j hlt]
    · by_cases hj : j = 0
      · subst j
        have hcol₁ :
            L₁ (Fin.succ (i.pred hi)) 0 =
              fun s t => ∑ l : Fin r, A (Fin.succ (i.pred hi)) 0 s l * A11_inv l t :=
          h₁.firstColumnBelow_eq_of_right_inverse A11_inv hInvRight (i.pred hi)
        have hcol₂ :
            L₂ (Fin.succ (i.pred hi)) 0 =
              fun s t => ∑ l : Fin r, A (Fin.succ (i.pred hi)) 0 s l * A11_inv l t :=
          h₂.firstColumnBelow_eq_of_right_inverse A11_inv hInvRight (i.pred hi)
        have hscalar₁ := congr_fun (congr_fun hcol₁ s) t
        have hscalar₂ := congr_fun (congr_fun hcol₂ s) t
        simpa [Fin.succ_pred i hi] using hscalar₁.trans hscalar₂.symm
      · have htail_block := congr_fun (congr_fun htail.1 (i.pred hi)) (j.pred hj)
        have htail_scalar := congr_fun (congr_fun htail_block s) t
        simpa [Ls₁, Ls₂, Fin.succ_pred i hi, Fin.succ_pred j hj] using htail_scalar
  · ext i j s t
    by_cases hi : i = 0
    · subst i
      have hrow₁ : U₁ 0 j = A 0 j := h₁.firstRow_eq j
      have hrow₂ : U₂ 0 j = A 0 j := h₂.firstRow_eq j
      have hscalar₁ := congr_fun (congr_fun hrow₁ s) t
      have hscalar₂ := congr_fun (congr_fun hrow₂ s) t
      exact hscalar₁.trans hscalar₂.symm
    · by_cases hj : j = 0
      · subst j
        have hlt : (0 : Fin (m + 1)).val < i.val := by
          have hival : i.val ≠ 0 := fun h => hi (Fin.ext h)
          simpa using Nat.pos_of_ne_zero hival
        rw [h₁.U_lower_zero i 0 hlt, h₂.U_lower_zero i 0 hlt]
      · have htail_block := congr_fun (congr_fun htail.2 (i.pred hi)) (j.pred hj)
        have htail_scalar := congr_fun (congr_fun htail_block s) t
        simpa [Us₁, Us₂, Fin.succ_pred i hi, Fin.succ_pred j hj] using htail_scalar

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 one-step induction:
    a two-sided inverse for the leading block and an exists-unique block LU
    factorization of the Schur complement give an exists-unique block LU
    factorization of the full block matrix. -/
theorem BlockLUFactSpec.existsUnique_step_of_schurTail_existsUnique {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hTailExistsUnique :
      ∃ Ls Us : Fin m → Fin m → (Fin r → Fin r → ℝ),
        BlockLUFactSpec m r (blockSchur A A11_inv) Ls Us ∧
          ∀ Ls' Us' : Fin m → Fin m → (Fin r → Fin r → ℝ),
            BlockLUFactSpec m r (blockSchur A A11_inv) Ls' Us' →
              Ls' = Ls ∧ Us' = Us) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
      BlockLUFactSpec (m + 1) r A L U ∧
        ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
          BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U := by
  rcases hTailExistsUnique with ⟨Ls, Us, hS, hSunique⟩
  rcases block_lu_one_step A A11_inv hInvLeft Ls Us hS with ⟨L, U, hLU⟩
  refine ⟨L, U, hLU, ?_⟩
  intro L' U' hLU'
  have hTailUnique :
      ∀ Ls₁ Us₁ Ls₂ Us₂ : Fin m → Fin m → (Fin r → Fin r → ℝ),
        BlockLUFactSpec m r (blockSchur A A11_inv) Ls₁ Us₁ →
        BlockLUFactSpec m r (blockSchur A A11_inv) Ls₂ Us₂ →
        Ls₁ = Ls₂ ∧ Us₁ = Us₂ := by
    intro Ls₁ Us₁ Ls₂ Us₂ h₁ h₂
    have h₁unique := hSunique Ls₁ Us₁ h₁
    have h₂unique := hSunique Ls₂ Us₂ h₂
    exact ⟨h₁unique.1.trans h₂unique.1.symm,
      h₁unique.2.trans h₂unique.2.symm⟩
  exact hLU'.eq_of_schurTail_unique_of_right_inverse hLU A11_inv hInvRight hTailUnique

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 converse-side induction
    dependency: if the full one-step block matrix has a unique block LU
    factorization and the first block has the supplied two-sided inverse, then
    the Schur complement has a unique block LU factorization.

    The proof lifts any Schur-tail factorization back to the full matrix using
    the explicit one-step factors, applies full uniqueness, and then reads off
    equality of the trailing blocks. -/
theorem BlockLUFactSpec.schurTail_existsUnique_of_existsUnique_of_first_block_inverse {m r : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hExistsUnique :
      ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
        BlockLUFactSpec (m + 1) r A L U ∧
          ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
            BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U) :
    ∃ Ls Us : Fin m → Fin m → (Fin r → Fin r → ℝ),
      BlockLUFactSpec m r (blockSchur A A11_inv) Ls Us ∧
        ∀ Ls' Us' : Fin m → Fin m → (Fin r → Fin r → ℝ),
          BlockLUFactSpec m r (blockSchur A A11_inv) Ls' Us' →
            Ls' = Ls ∧ Us' = Us := by
  rcases hExistsUnique with ⟨L, U, hLU, hUnique⟩
  let Ls : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => L (Fin.succ i) (Fin.succ j)
  let Us : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => U (Fin.succ i) (Fin.succ j)
  have hTail : BlockLUFactSpec m r (blockSchur A A11_inv) Ls Us :=
    hLU.schurTailFactSpec_of_right_inverse A11_inv hInvRight
  refine ⟨Ls, Us, hTail, ?_⟩
  intro Ls' Us' hTail'
  let L' := blockLUOneStepL A A11_inv Ls'
  let U' := blockLUOneStepU A Us'
  have hFull' : BlockLUFactSpec (m + 1) r A L' U' := by
    simpa [L', U'] using
      block_lu_one_step_explicit A A11_inv hInvLeft Ls' Us' hTail'
  have hEq := hUnique L' U' hFull'
  constructor
  · ext i j s t
    have hblock := congr_fun (congr_fun hEq.1 (Fin.succ i)) (Fin.succ j)
    have hscalar := congr_fun (congr_fun hblock s) t
    simpa [L', blockLUOneStepL, Ls, Fin.succ_ne_zero, Fin.pred_succ] using hscalar
  · ext i j s t
    have hblock := congr_fun (congr_fun hEq.2 (Fin.succ i)) (Fin.succ j)
    have hscalar := congr_fun (congr_fun hblock s) t
    simpa [U', blockLUOneStepU, Us, Fin.succ_ne_zero, Fin.pred_succ] using hscalar

/-- Convert a block table into a matrix whose entries are ordinary `r × r`
    matrices.  This private adapter lets short matrix-algebra proofs reuse
    Mathlib associativity for the block level. -/
private noncomputable def blockMatrixOf {m r : ℕ}
    (B : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Matrix (Fin m) (Fin m) (Matrix (Fin r) (Fin r) ℝ) :=
  fun i j => Matrix.of (B i j)

private noncomputable def blockMatrixFrom {m r : ℕ}
    (B : Matrix (Fin m) (Fin m) (Matrix (Fin r) (Fin r) ℝ)) :
    Fin m → Fin m → (Fin r → Fin r → ℝ) :=
  fun i j s t => B i j s t

private noncomputable def firstPivotRow {m : ℕ} (hm : 0 < m) : Fin (m + 1) :=
  Fin.succ ⟨0, hm⟩

private noncomputable def firstPivotShearE {m r : ℕ} (hm : 0 < m)
    (X : Fin r → Fin r → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (Matrix (Fin r) (Fin r) ℝ) :=
  fun i j => if i = firstPivotRow hm ∧ j = 0 then Matrix.of X else 0

private lemma firstPivotRow_ne_zero {m : ℕ} (hm : 0 < m) :
    firstPivotRow hm ≠ (0 : Fin (m + 1)) := by
  intro h
  have := congrArg Fin.val h
  simp [firstPivotRow] at this

private lemma blockMatrixOf_mul_firstPivotShearE_apply {m r : ℕ} (hm : 0 < m)
    (B : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (X : Fin r → Fin r → ℝ) (i j : Fin (m + 1)) :
    (blockMatrixOf B * firstPivotShearE hm X) i j =
      if j = 0 then
        Matrix.of (fun s t => ∑ q : Fin r, B i (firstPivotRow hm) s q * X q t)
      else 0 := by
  classical
  ext s t
  by_cases hj : j = 0
  · subst j
    simp only [Matrix.mul_apply, blockMatrixOf, firstPivotShearE,
      Matrix.of_apply, Matrix.sum_apply]
    rw [Finset.sum_eq_single (firstPivotRow hm)]
    · simp
    · intro k _hk hk
      simp [hk]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · simp only [Matrix.mul_apply, blockMatrixOf, firstPivotShearE,
      Matrix.of_apply, Matrix.sum_apply]
    simp [hj]

private lemma firstPivotShearE_mul_blockMatrixOf_apply {m r : ℕ} (hm : 0 < m)
    (X : Fin r → Fin r → ℝ)
    (B : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (i j : Fin (m + 1)) :
    (firstPivotShearE hm X * blockMatrixOf B) i j =
      if i = firstPivotRow hm then
        Matrix.of (fun s t => ∑ q : Fin r, X s q * B 0 j q t)
      else 0 := by
  classical
  ext s t
  by_cases hi : i = firstPivotRow hm
  · subst i
    simp only [Matrix.mul_apply, blockMatrixOf, firstPivotShearE,
      Matrix.of_apply, Matrix.sum_apply]
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp
    · intro k _hk hk
      simp [hk]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · simp only [Matrix.mul_apply, blockMatrixOf, firstPivotShearE,
      Matrix.of_apply, Matrix.sum_apply]
    simp [hi]

private lemma firstPivotShearE_sq {m r : ℕ} (hm : 0 < m)
    (X : Fin r → Fin r → ℝ) :
    firstPivotShearE hm X * firstPivotShearE hm X = 0 := by
  classical
  ext i j s t
  by_cases hi : i = firstPivotRow hm
  · subst i
    simp only [Matrix.mul_apply, firstPivotShearE, Matrix.sum_apply]
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · have h0ne : (0 : Fin (m + 1)) ≠ firstPivotRow hm :=
        (firstPivotRow_ne_zero hm).symm
      simp [h0ne]
    · intro k _hk hk
      simp [hk]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · simp only [Matrix.mul_apply, firstPivotShearE, Matrix.sum_apply]
    simp [hi]

private lemma firstPivotShear_mul_inv {m r : ℕ} (hm : 0 < m)
    (X : Fin r → Fin r → ℝ) :
    (1 + firstPivotShearE hm X) * (1 - firstPivotShearE hm X) = 1 := by
  have hneg : firstPivotShearE hm X * -firstPivotShearE hm X = 0 := by
    calc
      firstPivotShearE hm X * -firstPivotShearE hm X =
          -(firstPivotShearE hm X * firstPivotShearE hm X) :=
        Matrix.mul_neg (firstPivotShearE hm X) (firstPivotShearE hm X)
      _ = 0 := by
        rw [firstPivotShearE_sq hm X]
        simp
  rw [sub_eq_add_neg, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul,
    hneg]
  abel

private noncomputable def firstPivotShearL {m r : ℕ} (hm : 0 < m)
    (L : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (X : Fin r → Fin r → ℝ) :
    Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) :=
  blockMatrixFrom (blockMatrixOf L * (1 + firstPivotShearE hm X))

private noncomputable def firstPivotShearU {m r : ℕ} (hm : 0 < m)
    (U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (X : Fin r → Fin r → ℝ) :
    Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) :=
  blockMatrixFrom ((1 - firstPivotShearE hm X) * blockMatrixOf U)

private theorem firstPivotShear_spec {m r : ℕ} (hm : 0 < m)
    {A L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hLU : BlockLUFactSpec (m + 1) r A L U)
    (X : Fin r → Fin r → ℝ)
    (hXker : ∀ s t : Fin r, ∑ q : Fin r, X s q * A 0 0 q t = 0) :
    BlockLUFactSpec (m + 1) r A
      (firstPivotShearL hm L X) (firstPivotShearU hm U X) := by
  classical
  let E := firstPivotShearE hm X
  let Lb := blockMatrixOf L
  let Ub := blockMatrixOf U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    ext s t
    by_cases hi0 : i = 0
    · subst i
      have hupper : L 0 (firstPivotRow hm) = zeroBlock r :=
        hLU.L_upper_zero 0 (firstPivotRow hm) (by simp [firstPivotRow])
      rw [show firstPivotShearL hm L X 0 0 s t =
          (blockMatrixOf L * (1 + firstPivotShearE hm X)) 0 0 s t by rfl,
        Matrix.mul_add, Matrix.mul_one]
      change blockMatrixOf L 0 0 s t +
          (blockMatrixOf L * firstPivotShearE hm X) 0 0 s t = idBlock r s t
      rw [blockMatrixOf_mul_firstPivotShearE_apply]
      have hdiag := congr_fun (congr_fun (hLU.L_diag 0) s) t
      simpa [blockMatrixOf, hupper, zeroBlock, idBlock] using hdiag
    · rw [show firstPivotShearL hm L X i i s t =
          (blockMatrixOf L * (1 + firstPivotShearE hm X)) i i s t by rfl,
        Matrix.mul_add, Matrix.mul_one]
      change blockMatrixOf L i i s t +
          (blockMatrixOf L * firstPivotShearE hm X) i i s t = idBlock r s t
      rw [blockMatrixOf_mul_firstPivotShearE_apply]
      have hdiag := congr_fun (congr_fun (hLU.L_diag i) s) t
      simpa [blockMatrixOf, hi0, idBlock] using hdiag
  · intro i j hij
    have hj0 : j ≠ 0 := by
      intro hj
      subst j
      simp at hij
    ext s t
    rw [show firstPivotShearL hm L X i j s t =
        (blockMatrixOf L * (1 + firstPivotShearE hm X)) i j s t by rfl,
      Matrix.mul_add, Matrix.mul_one]
    change blockMatrixOf L i j s t +
        (blockMatrixOf L * firstPivotShearE hm X) i j s t = zeroBlock r s t
    rw [blockMatrixOf_mul_firstPivotShearE_apply]
    have hzero := congr_fun (congr_fun (hLU.L_upper_zero i j hij) s) t
    simpa [blockMatrixOf, hj0, zeroBlock] using hzero
  · intro i j hij
    ext s t
    by_cases hi : i = firstPivotRow hm
    · subst i
      have hj0 : j = 0 := by
        apply Fin.ext
        have hrowval : (firstPivotRow hm).val = 1 := by
          simp [firstPivotRow]
        have hjlt : j.val < 1 := by
          omega
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hjlt)
      subst j
      have hzero_lt : (0 : Fin (m + 1)).val < (firstPivotRow hm).val := by
        have hrowval : (firstPivotRow hm).val = 1 := by
          simp [firstPivotRow]
        rw [hrowval]
        norm_num
      have hU10 : U (firstPivotRow hm) 0 = zeroBlock r :=
        hLU.U_lower_zero (firstPivotRow hm) 0 hzero_lt
      have hU00 : U 0 0 = A 0 0 := hLU.firstRow_eq 0
      rw [show firstPivotShearU hm U X (firstPivotRow hm) 0 s t =
          ((1 - firstPivotShearE hm X) * blockMatrixOf U) (firstPivotRow hm) 0 s t by rfl,
        sub_eq_add_neg, Matrix.add_mul, Matrix.one_mul]
      change blockMatrixOf U (firstPivotRow hm) 0 s t +
          (-firstPivotShearE hm X * blockMatrixOf U) (firstPivotRow hm) 0 s t =
        zeroBlock r s t
      have hnegEntry :
          (-firstPivotShearE hm X * blockMatrixOf U) (firstPivotRow hm) 0 s t =
            -((firstPivotShearE hm X * blockMatrixOf U) (firstPivotRow hm) 0 s t) := by
        have hnegMat : -firstPivotShearE hm X * blockMatrixOf U =
            -(firstPivotShearE hm X * blockMatrixOf U) :=
          Matrix.neg_mul (firstPivotShearE hm X) (blockMatrixOf U)
        exact congr_fun (congr_fun (congr_fun (congr_fun hnegMat
          (firstPivotRow hm)) 0) s) t
      rw [hnegEntry]
      change blockMatrixOf U (firstPivotRow hm) 0 s t -
          (firstPivotShearE hm X * blockMatrixOf U) (firstPivotRow hm) 0 s t =
        zeroBlock r s t
      rw [firstPivotShearE_mul_blockMatrixOf_apply]
      have hzero := congr_fun (congr_fun hU10 s) t
      have hrow := hXker s t
      have hzero' : blockMatrixOf U (firstPivotRow hm) 0 s t = zeroBlock r s t := by
        simpa [blockMatrixOf] using hzero
      rw [hzero']
      simp [hU00, zeroBlock, hrow]
    · rw [show firstPivotShearU hm U X i j s t =
          ((1 - firstPivotShearE hm X) * blockMatrixOf U) i j s t by rfl,
        sub_eq_add_neg, Matrix.add_mul, Matrix.one_mul]
      change blockMatrixOf U i j s t +
          (-firstPivotShearE hm X * blockMatrixOf U) i j s t = zeroBlock r s t
      have hnegEntry :
          (-firstPivotShearE hm X * blockMatrixOf U) i j s t =
            -((firstPivotShearE hm X * blockMatrixOf U) i j s t) := by
        have hnegMat : -firstPivotShearE hm X * blockMatrixOf U =
            -(firstPivotShearE hm X * blockMatrixOf U) :=
          Matrix.neg_mul (firstPivotShearE hm X) (blockMatrixOf U)
        exact congr_fun (congr_fun (congr_fun (congr_fun hnegMat i) j) s) t
      rw [hnegEntry]
      change blockMatrixOf U i j s t -
          (firstPivotShearE hm X * blockMatrixOf U) i j s t = zeroBlock r s t
      rw [firstPivotShearE_mul_blockMatrixOf_apply]
      have hzero := congr_fun (congr_fun (hLU.U_lower_zero i j hij) s) t
      simpa [blockMatrixOf, hi, zeroBlock] using hzero
  · intro i j s t
    have hprodMatrix :
        ((blockMatrixOf L * (1 + firstPivotShearE hm X)) *
          ((1 - firstPivotShearE hm X) * blockMatrixOf U)) i j s t = A i j s t := by
      calc
        ((blockMatrixOf L * (1 + firstPivotShearE hm X)) *
            ((1 - firstPivotShearE hm X) * blockMatrixOf U)) i j s t =
            (blockMatrixOf L *
              (((1 + firstPivotShearE hm X) * (1 - firstPivotShearE hm X)) *
                blockMatrixOf U)) i j s t := by
              rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + firstPivotShearE hm X)]
        _ = (blockMatrixOf L * blockMatrixOf U) i j s t := by
              rw [firstPivotShear_mul_inv hm X]
              simp
        _ = A i j s t := by
              simpa [blockMatrixOf, Matrix.mul_apply, Matrix.sum_apply]
                using hLU.product_eq i j s t
    simpa [blockMatrixOf, firstPivotShearL, firstPivotShearU, blockMatrixFrom,
      Matrix.mul_apply, Matrix.sum_apply] using hprodMatrix

private lemma sum_idBlock_mul_eq_val {r : ℕ} (f : Fin r → ℝ) (s : Fin r) :
    ∑ q : Fin r, idBlock r s q * f q = f s := by
  conv_lhs =>
    arg 2; ext q
    rw [show idBlock r s q * f q = if s = q then f q else 0 by
      by_cases h : s = q <;> simp [idBlock, h]]
  simp [Finset.mem_univ]

private lemma firstPivotShearL_firstPivot_zero_apply {m r : ℕ} (hm : 0 < m)
    {L : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hLdiag : ∀ i : Fin (m + 1), L i i = idBlock r)
    (X : Fin r → Fin r → ℝ) (s t : Fin r) :
    firstPivotShearL hm L X (firstPivotRow hm) 0 s t =
      L (firstPivotRow hm) 0 s t + X s t := by
  rw [show firstPivotShearL hm L X (firstPivotRow hm) 0 s t =
      (blockMatrixOf L * (1 + firstPivotShearE hm X)) (firstPivotRow hm) 0 s t by rfl,
    Matrix.mul_add, Matrix.mul_one]
  change blockMatrixOf L (firstPivotRow hm) 0 s t +
      (blockMatrixOf L * firstPivotShearE hm X) (firstPivotRow hm) 0 s t =
    L (firstPivotRow hm) 0 s t + X s t
  rw [blockMatrixOf_mul_firstPivotShearE_apply]
  have hsum :
      (∑ q : Fin r, L (firstPivotRow hm) (firstPivotRow hm) s q * X q t) = X s t := by
    rw [hLdiag (firstPivotRow hm)]
    exact sum_idBlock_mul_eq_val (fun q => X q t) s
  simp [blockMatrixOf, hsum]

private theorem firstPivotShearL_ne_of_X_ne_zero {m r : ℕ} (hm : 0 < m)
    {A L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hLU : BlockLUFactSpec (m + 1) r A L U)
    (X : Fin r → Fin r → ℝ) (hXne : X ≠ zeroBlock r) :
    firstPivotShearL hm L X ≠ L := by
  intro hEq
  apply hXne
  ext s t
  have hentry := congr_fun (congr_fun (congr_fun (congr_fun hEq
    (firstPivotRow hm)) 0) s) t
  have hshape := firstPivotShearL_firstPivot_zero_apply hm hLU.L_diag X s t
  rw [hshape] at hentry
  simp [zeroBlock] at hentry ⊢
  linarith

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 dependency:
    Mathlib determinant nonsingularity for the first block supplies the
    explicit two-sided inverse data used by the block-level Schur induction. -/
theorem first_block_inverse_of_isUnit_det {r : ℕ}
    (A00 : Fin r → Fin r → ℝ)
    (hdet : IsUnit (Matrix.det (Matrix.of A00))) :
    ∃ Ainv : Fin r → Fin r → ℝ,
      (∀ s t : Fin r,
        ∑ l : Fin r, Ainv s l * A00 l t = if s = t then 1 else 0) ∧
      (∀ s t : Fin r,
        ∑ l : Fin r, A00 s l * Ainv l t = if s = t then 1 else 0) := by
  let M : Matrix (Fin r) (Fin r) ℝ := Matrix.of A00
  refine ⟨fun s t => M⁻¹ s t, ?_, ?_⟩
  · intro s t
    have h := congr_fun (congr_fun (Matrix.nonsing_inv_mul M hdet) s) t
    simpa [M, Matrix.mul_apply, Matrix.one_apply] using h
  · intro s t
    have h := congr_fun (congr_fun (Matrix.mul_nonsing_inv M hdet) s) t
    simpa [M, Matrix.mul_apply, Matrix.one_apply] using h

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 converse-side dependency:
    uniqueness of a block LU factorization forces the first pivot block to be
    nonsingular.

    If the first block were singular, Mathlib gives a nonzero left-kernel
    vector.  The rank-one matrix formed from that vector defines a nontrivial
    unit-lower shear of the block factors; the shear preserves the product and
    triangular/unit-diagonal shape, contradicting uniqueness. -/
theorem BlockLUFactSpec.first_block_inverse_of_existsUnique {m r : ℕ}
    (hm : 0 < m)
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    (hExistsUnique :
      ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
        BlockLUFactSpec (m + 1) r A L U ∧
          ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
            BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U) :
    ∃ A11_inv : Fin r → Fin r → ℝ,
      (∀ s t : Fin r,
        ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0) ∧
      (∀ s t : Fin r,
        ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0) := by
  classical
  by_cases hdet : IsUnit (Matrix.det (Matrix.of (A 0 0)))
  · exact first_block_inverse_of_isUnit_det (A 0 0) hdet
  · have hdet0 : Matrix.det (Matrix.of (A 0 0)) = 0 := by
      by_contra hne
      exact hdet (isUnit_iff_ne_zero.mpr hne)
    rcases (Matrix.exists_vecMul_eq_zero_iff (M := Matrix.of (A 0 0))).2 hdet0 with
      ⟨v, hvne, hvker⟩
    let X : Fin r → Fin r → ℝ := fun s t => v s * v t
    have hXker : ∀ s t : Fin r, ∑ q : Fin r, X s q * A 0 0 q t = 0 := by
      intro s t
      have hrow := congr_fun hvker t
      calc
        ∑ q : Fin r, X s q * A 0 0 q t =
            v s * ∑ q : Fin r, v q * A 0 0 q t := by
              simp [X, Finset.mul_sum, mul_assoc]
        _ = 0 := by
              simpa [Matrix.vecMul, dotProduct] using congrArg (fun z => v s * z) hrow
    have hXne : X ≠ zeroBlock r := by
      intro hXzero
      apply hvne
      funext s
      by_contra hs
      have hentry := congr_fun (congr_fun hXzero s) s
      simp [X, zeroBlock] at hentry
      exact hs hentry
    rcases hExistsUnique with ⟨L, U, hLU, hUnique⟩
    have hShear : BlockLUFactSpec (m + 1) r A
        (firstPivotShearL hm L X) (firstPivotShearU hm U X) :=
      firstPivotShear_spec hm hLU X hXker
    have hEq := hUnique (firstPivotShearL hm L X) (firstPivotShearU hm U X) hShear
    exact (firstPivotShearL_ne_of_X_ne_zero hm hLU X hXne hEq.1).elim

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 base case:
    a `1 × 1` block matrix has the unique block LU factorization `L = I`,
    `U = A`.  This is the zero-prefix base case for the global induction. -/
theorem BlockLUFactSpec.existsUnique_one {r : ℕ}
    (A : Fin 1 → Fin 1 → (Fin r → Fin r → ℝ)) :
    ∃ L U : Fin 1 → Fin 1 → (Fin r → Fin r → ℝ),
      BlockLUFactSpec 1 r A L U ∧
        ∀ L' U' : Fin 1 → Fin 1 → (Fin r → Fin r → ℝ),
          BlockLUFactSpec 1 r A L' U' → L' = L ∧ U' = U := by
  let L0 : Fin 1 → Fin 1 → (Fin r → Fin r → ℝ) := fun _ _ => idBlock r
  let U0 : Fin 1 → Fin 1 → (Fin r → Fin r → ℝ) := A
  refine ⟨L0, U0, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
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
  · intro L' U' hLU'
    constructor
    · ext i j s t
      fin_cases i
      fin_cases j
      have hL := hLU'.L_diag 0
      exact congr_fun (congr_fun hL s) t
    · ext i j s t
      fin_cases i
      fin_cases j
      have hU : U' 0 0 = A 0 0 := hLU'.firstRow_eq 0
      exact congr_fun (congr_fun hU s) t

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 forward induction direction:
    if the first `m` leading principal block submatrices of an `(m+1) × (m+1)`
    uniform block matrix are nonsingular, then the block LU factorization exists
    and is unique.

    This is the source induction direction from leading-principal-block
    nonsingularity to existence/uniqueness.  The converse direction of the
    printed iff is tracked separately. -/
theorem BlockLUFactSpec.existsUnique_of_leadingPrincipalBlockNonsingular13_2
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (hlead : LeadingPrincipalBlockNonsingular13_2 A) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
      BlockLUFactSpec (m + 1) r A L U ∧
        ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
          BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U := by
  induction m with
  | zero =>
      simpa using BlockLUFactSpec.existsUnique_one A
  | succ m ih =>
      rcases LeadingPrincipalBlockNonsingular13_2.first_block_inverse
          (m := m + 1) (r := r) (A := A) (Nat.succ_pos m) hlead with
        ⟨A11_inv, hInvLeft, hInvRight⟩
      have hTailLead :
          LeadingPrincipalBlockNonsingular13_2 (blockSchur A A11_inv) :=
        LeadingPrincipalBlockNonsingular13_2.schur hInvLeft hInvRight hlead
      have hTailExistsUnique :
          ∃ Ls Us : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
            BlockLUFactSpec (m + 1) r (blockSchur A A11_inv) Ls Us ∧
              ∀ Ls' Us' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
                BlockLUFactSpec (m + 1) r (blockSchur A A11_inv) Ls' Us' →
                  Ls' = Ls ∧ Us' = Us :=
        ih (blockSchur A A11_inv) hTailLead
      exact BlockLUFactSpec.existsUnique_step_of_schurTail_existsUnique
        A A11_inv hInvLeft hInvRight hTailExistsUnique

/-- Higham, 2nd ed., Chapter 13, §13.3.2:
    an SPD block matrix has a unique block LU factorization.

    The SPD assumption is expressed as positive definiteness of the flattened
    uniform block matrix.  The proof first derives the leading-principal-block
    nonsingularity condition and then applies Theorem 13.2. -/
theorem BlockLUFactSpec.existsUnique_of_posDef_flat {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (hPos : Matrix.PosDef (blockMatrixFlat A)) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
      BlockLUFactSpec (m + 1) r A L U ∧
        ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
          BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U :=
  BlockLUFactSpec.existsUnique_of_leadingPrincipalBlockNonsingular13_2 A
    (LeadingPrincipalBlockNonsingular13_2.of_posDef_flat A hPos)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 converse induction direction:
    if a uniform block matrix has a unique block LU factorization, then its
    first `m` leading principal block submatrices are nonsingular.

    The first pivot inverse is forced by uniqueness via
    `BlockLUFactSpec.first_block_inverse_of_existsUnique`; uniqueness then
    descends to the Schur complement and the induction hypothesis supplies the
    Schur-tail leading-prefix condition. -/
theorem LeadingPrincipalBlockNonsingular13_2.of_existsUnique {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (hExistsUnique :
      ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
        BlockLUFactSpec (m + 1) r A L U ∧
          ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
            BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U) :
    LeadingPrincipalBlockNonsingular13_2 A := by
  induction m with
  | zero =>
      intro p hp
      omega
  | succ m ih =>
      rcases BlockLUFactSpec.first_block_inverse_of_existsUnique
          (m := m + 1) (r := r) (A := A) (Nat.succ_pos m) hExistsUnique with
        ⟨A11_inv, hInvLeft, hInvRight⟩
      have hTailExistsUnique :
          ∃ Ls Us : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
            BlockLUFactSpec (m + 1) r (blockSchur A A11_inv) Ls Us ∧
              ∀ Ls' Us' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
                BlockLUFactSpec (m + 1) r (blockSchur A A11_inv) Ls' Us' →
                  Ls' = Ls ∧ Us' = Us :=
        BlockLUFactSpec.schurTail_existsUnique_of_existsUnique_of_first_block_inverse
          (A := A) (A11_inv := A11_inv) hInvLeft hInvRight hExistsUnique
      have hTailLead :
          LeadingPrincipalBlockNonsingular13_2 (blockSchur A A11_inv) :=
        ih (blockSchur A A11_inv) hTailExistsUnique
      exact LeadingPrincipalBlockNonsingular13_2.of_first_block_inverse_of_schur
        hInvLeft hInvRight hTailLead

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2:
    a uniform block matrix has a unique block LU factorization if and only if
    its first `m` leading principal block submatrices are nonsingular.

    For a matrix indexed by `Fin (m+1)`, this is the source condition on the
    first `m` leading block prefixes, i.e. all prefixes except the whole
    matrix. -/
theorem BlockLUFactSpec.existsUnique_iff_leadingPrincipalBlockNonsingular13_2
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    (∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
      BlockLUFactSpec (m + 1) r A L U ∧
        ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
          BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U) ↔
      LeadingPrincipalBlockNonsingular13_2 A := by
  constructor
  · exact LeadingPrincipalBlockNonsingular13_2.of_existsUnique A
  · exact BlockLUFactSpec.existsUnique_of_leadingPrincipalBlockNonsingular13_2 A

end NumStability
