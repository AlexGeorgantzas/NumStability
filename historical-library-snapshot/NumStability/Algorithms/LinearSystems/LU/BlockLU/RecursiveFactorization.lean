import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Recursive block LU factorization

Reusable one-step block-LU factor constructors, factorization existence, and
entrywise max-norm propagation. Numbered Chapter 13 correspondence lives under
`NumStability.Source.Higham`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix

-- ============================================================
-- One-step recursive block LU construction
-- ============================================================

/-- Helper: summing (if s = l then 1 else 0) · f(l) gives f(s). -/
private lemma sum_ite_eq_val {r : ℕ} (f : Fin r → ℝ) (s : Fin r) :
    ∑ l : Fin r, (if s = l then (1 : ℝ) else 0) * f l = f s := by
  conv_lhs =>
    arg 2; ext l
    rw [show (if s = l then (1 : ℝ) else 0) * f l =
      if s = l then f l else 0 by split_ifs <;> simp]
  simp [Finset.mem_univ]

/-- Helper: summing f(l) · (if l = t then 1 else 0) gives f(t). -/
private lemma sum_ite_eq_val_right {r : ℕ} (f : Fin r → ℝ) (t : Fin r) :
    ∑ l : Fin r, f l * (if l = t then (1 : ℝ) else 0) = f t := by
  simp_rw [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Constructed lower factor for one step of Higham's partitioned block LU.
    This is the explicit `L` used by `block_lu_one_step_explicit`: identity in
    the first block row, `Aᵢ₁ A₁₁⁻¹` in the first block column below the
    diagonal, and the Schur-tail lower factor in the trailing block. -/
noncomputable def blockLUOneStepL {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (L_S : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
  if hi : i = 0 then
    if j = 0 then idBlock r else zeroBlock r
  else if hj : j = 0 then
    fun s t => ∑ l : Fin r, A i 0 s l * A11_inv l t
  else L_S (i.pred hi) (j.pred hj)

/-- Constructed upper factor for one step of Higham's partitioned block LU:
    the first block row is the first block row of `A`, the first block column
    below the diagonal is zero, and the trailing block is the Schur-tail upper
    factor. -/
noncomputable def blockLUOneStepU {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (U_S : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
  if hi : i = 0 then A 0 j
  else if hj : j = 0 then zeroBlock r
  else U_S (i.pred hi) (j.pred hj)

/-- One-step norm propagation for the explicit lower factor in
    `block_lu_one_step_explicit`.

    The full lower factor is bounded by a common entrywise block bound `C` once
    the identity diagonal, the first-split lower-left block
    `A₂₁ A₁₁⁻¹`, and the recursive tail lower factor are each bounded by `C`.
    This is a small structural dependency for the recursive/full-factor
    Eq.13.22 lift. -/
theorem blockLUOneStepL_blockMaxNorm_le_of_firstSplit_tail {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (L_S : Fin m → Fin m → (Fin r → Fin r → ℝ))
    {C : ℝ}
    (hId : 1 ≤ C)
    (hL21 :
      maxEntryNormRect (Nat.mul_pos hm hr) hr
          ((blockMatrixFirstSplitA21 A * A11_inv :
            Matrix (Fin (m * r)) (Fin r) ℝ)) ≤ C)
    (hTail : blockMaxNorm hm hr L_S ≤ C) :
    blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepL A A11_inv L_S) ≤ C := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hId
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      by_cases hst : s = t
      · simpa [blockLUOneStepL, idBlock, hst] using hId
      · simpa [blockLUOneStepL, idBlock, hst, abs_of_nonneg hC0] using hC0
    · simpa [blockLUOneStepL, hj, zeroBlock, abs_of_nonneg hC0] using hC0
  · by_cases hj : j = 0
    · subst j
      have hentry :=
        entry_le_maxEntryNormRect (Nat.mul_pos hm hr) hr
          ((blockMatrixFirstSplitA21 A * A11_inv :
            Matrix (Fin (m * r)) (Fin r) ℝ))
          (finProdFinEquiv (i.pred hi, s)) t
      exact le_trans
        (by
          simpa [blockLUOneStepL, hi, Matrix.mul_apply, blockMatrixFirstSplitA21]
            using hentry)
        hL21
    · exact le_trans
        (by
          simpa [blockLUOneStepL, hi, hj] using
            block_entry_abs_le_blockMaxNorm hm hr L_S (i.pred hi) (j.pred hj) s t)
        hTail

/-- One-step norm propagation for the explicit upper factor in
    `block_lu_one_step_explicit`.

    The full upper factor is bounded by a common entrywise block bound `C` once
    the first block row of `A` and the recursive tail upper factor are bounded
    by `C`. -/
theorem blockLUOneStepU_blockMaxNorm_le_of_firstRow_tail {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (U_S : Fin m → Fin m → (Fin r → Fin r → ℝ))
    {C : ℝ}
    (hFirstRow : ∀ j : Fin (m + 1), maxEntryNorm hr (A 0 j) ≤ C)
    (hTail : blockMaxNorm hm hr U_S ≤ C) :
    blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU A U_S) ≤ C := by
  have hC0 : 0 ≤ C := le_trans (maxEntryNorm_nonneg hr (A 0 0)) (hFirstRow 0)
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  by_cases hi : i = 0
  · subst i
    exact le_trans (entry_le_maxEntryNorm hr (A 0 j) s t) (hFirstRow j)
  · by_cases hj : j = 0
    · subst j
      simpa [blockLUOneStepU, hi, zeroBlock, abs_of_nonneg hC0] using hC0
    · exact le_trans
        (by
          simpa [blockLUOneStepU, hi, hj] using
            block_entry_abs_le_blockMaxNorm hm hr U_S (i.pred hi) (j.pred hj) s t)
        hTail

/-- One-step product-norm propagation for the explicit block LU factors in
    `block_lu_one_step_explicit`.

    This packages the lower- and upper-factor one-step norm propagation lemmas:
    if the first-split lower-left block, first block row, and recursive Schur
    tail factors are bounded by `C_L` and `C_U`, then the full one-step product
    `‖L‖‖U‖` is bounded by `C_L * C_U`. -/
theorem blockLUOneStep_blockMaxNorm_product_le_of_firstSplit_tail {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (L_S U_S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    {C_L C_U : ℝ}
    (hId : 1 ≤ C_L)
    (hL21 :
      maxEntryNormRect (Nat.mul_pos hm hr) hr
          ((blockMatrixFirstSplitA21 A * A11_inv :
            Matrix (Fin (m * r)) (Fin r) ℝ)) ≤ C_L)
    (hTailL : blockMaxNorm hm hr L_S ≤ C_L)
    (hFirstRow : ∀ j : Fin (m + 1), maxEntryNorm hr (A 0 j) ≤ C_U)
    (hTailU : blockMaxNorm hm hr U_S ≤ C_U) :
    blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepL A A11_inv L_S) *
        blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU A U_S) ≤
      C_L * C_U := by
  have hL :
      blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepL A A11_inv L_S) ≤
        C_L :=
    blockLUOneStepL_blockMaxNorm_le_of_firstSplit_tail
      hm hr A A11_inv L_S hId hL21 hTailL
  have hU :
      blockMaxNorm (Nat.succ_pos m) hr (blockLUOneStepU A U_S) ≤
        C_U :=
    blockLUOneStepU_blockMaxNorm_le_of_firstRow_tail
      hm hr A U_S hFirstRow hTailU
  exact mul_le_mul hL hU
    (blockMaxNorm_nonneg (Nat.succ_pos m) hr (blockLUOneStepU A U_S))
    (le_trans zero_le_one hId)

/-- **One step of block LU factorization** (Higham, 2nd ed., Algorithm 13.3).
    Given A with m+1 blocks, A₁₁ invertible, and the Schur complement S having
    a block LU factorization S = L_S · U_S, constructs the block LU of A.

    Proof sketch: define L by cases (identity at (0,0), zero above diagonal,
    A_{i0}·A₁₁⁻¹ in column 0 below, L_S in the lower-right); define U similarly
    (A_{0j} in row 0, zero below column 0, U_S in the lower-right). Verify the
    product L·U = A using the inverse property and Schur complement cancellation. -/
theorem block_lu_one_step {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (hInv : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A (0 : Fin (m + 1)) (0 : Fin (m + 1)) l t =
        if s = t then 1 else 0)
    (L_S U_S : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hS : BlockLUFactSpec m r (blockSchur A A11_inv) L_S U_S) :
    ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
      BlockLUFactSpec (m + 1) r A L U := by
  -- Define L using dif for clean case analysis (following cholesky_existence pattern)
  let L : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
    if hi : i = 0 then
      if hj : j = 0 then idBlock r else zeroBlock r
    else if hj : j = 0 then
      fun s t => ∑ l : Fin r, A i 0 s l * A11_inv l t
    else L_S (i.pred hi) (j.pred hj)
  -- Define U using dif
  let U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
    if hi : i = 0 then A 0 j
    else if hj : j = 0 then zeroBlock r
    else U_S (i.pred hi) (j.pred hj)
  refine ⟨L, U, ?_, ?_, ?_, ?_⟩
  · -- L_diag: L i i = idBlock r
    intro i
    by_cases hi : i = 0
    · subst hi; simp [L]
    · simp only [L, dif_neg hi]; exact hS.L_diag (i.pred hi)
  · -- L_upper_zero: L i j = zeroBlock r when i.val < j.val
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := by intro h; subst h; exact lt_irrefl _ hij
      simp [L, hj]
    · have hj : j ≠ 0 := by intro h; subst h; exact absurd hij (Nat.not_lt_zero _)
      simp only [L, dif_neg hi, dif_neg hj]
      exact hS.L_upper_zero _ _ (by
        have := Fin.val_pred j hj; have := Fin.val_pred i hi
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega)
  · -- U_lower_zero: U i j = zeroBlock r when j.val < i.val
    intro i j hij
    by_cases hi : i = 0
    · subst hi; exact absurd hij (Nat.not_lt_zero _)
    · by_cases hj : j = 0
      · subst hj; simp [U, hi]
      · simp only [U, dif_neg hi, dif_neg hj]
        exact hS.U_lower_zero _ _ (by
          have := Fin.val_pred j hj; have := Fin.val_pred i hi
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
  · -- product_eq: ∑_k ∑_l L i k s l * U k j l t = A i j s t
    intro i j s t
    rw [Fin.sum_univ_succ]
    -- Entry value helpers (proven by simp on the let definitions)
    have hL0 : ∀ p, L 0 p = if p = 0 then idBlock r else zeroBlock r :=
      fun p => by simp [L]
    have hU0 : ∀ p, U 0 p = A 0 p := fun p => by simp [U]
    have hL0s : ∀ k : Fin m, L 0 (Fin.succ k) = zeroBlock r :=
      fun k => by rw [hL0]; simp [Fin.succ_ne_zero]
    have hLs0 : ∀ k : Fin m, L (Fin.succ k) 0 =
        fun s t => ∑ l, A (Fin.succ k) 0 s l * A11_inv l t :=
      fun k => by simp [L, Fin.succ_ne_zero]
    have hLss : ∀ (p q : Fin m), L (Fin.succ p) (Fin.succ q) = L_S p q :=
      fun p q => by simp [L, Fin.succ_ne_zero, Fin.pred_succ]
    have hUs0 : ∀ k : Fin m, U (Fin.succ k) 0 = zeroBlock r :=
      fun k => by simp [U, Fin.succ_ne_zero]
    have hUss : ∀ (p q : Fin m), U (Fin.succ p) (Fin.succ q) = U_S p q :=
      fun p q => by simp [U, Fin.succ_ne_zero, Fin.pred_succ]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · -- i = 0, j = 0: ∑_l δ(s,l) · A₀₀(l,t) + 0 = A₀₀(s,t)
      subst hi; subst hj
      rw [hL0 0, if_pos rfl, hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      exact sum_ite_eq_val _ s
    · -- i = 0, j ≠ 0: ∑_l δ(s,l) · A₀ⱼ(l,t) + 0 = A₀ⱼ(s,t)
      subst hi
      rw [hL0 0, if_pos rfl, hU0 j]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) j l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      exact sum_ite_eq_val _ s
    · -- i ≠ 0, j = 0: A_{i0}·A₁₁⁻¹·A₀₀ + 0 = A_{i0}
      subst hj; rw [hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L i (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hUs0 k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, hInv]
      exact sum_ite_eq_val_right _ t
    · -- i ≠ 0, j ≠ 0: Schur complement cancellation
      rw [hU0 j]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0]
      -- Rewrite successor terms to L_S/U_S
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
      -- Use Schur complement product equation
      have hprod := hS.product_eq (i.pred hi) (j.pred hj) s t
      simp only [blockSchur, Fin.succ_pred] at hprod
      rw [hprod]
      -- first_sum + (A(i,j) − triple_sum) = A(i,j)
      have hfirst : ∑ l : Fin r,
          (∑ l' : Fin r, A i 0 s l' * A11_inv l' l) * A 0 j l t =
          ∑ l₁ : Fin r, ∑ l₂ : Fin r,
            A i 0 s l₁ * A11_inv l₁ l₂ * A 0 j l₂ t := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
      linarith


end NumStability
