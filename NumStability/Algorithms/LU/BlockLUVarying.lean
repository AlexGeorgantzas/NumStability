/-
# Chapter 13 block LU with unequal block dimensions

Higham's Theorem 13.2 permits the diagonal blocks to have different positive
orders.  This module gives a global-matrix model for such a partition: a list
`dims = [r₀, ..., rₘ₋₁]` produces the scalar index `Fin (r₀ + ... + rₘ₋₁)`.
The recursive lower/upper shape predicates split at each cumulative block
boundary and express unit block-lower and block-upper triangularity without
imposing a common block order.
-/

import NumStability.Algorithms.LU.BlockLU

namespace NumStability

open scoped BigOperators Matrix

noncomputable section

/-- Scalar indices of a matrix partitioned into blocks with the listed
orders. -/
abbrev Higham13VaryingBlockIndex (dims : List ℕ) := Fin dims.sum

/-- Reindex a first-block/tail split from `Fin r ⊕ Fin n` to `Fin (r+n)`. -/
noncomputable def higham13VaryingFromBlocks {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (r + n)) (Fin (r + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A11 A12 A21 A22)

@[simp] theorem higham13VaryingFromBlocks_apply₁₁ {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ) (i j : Fin r) :
    higham13VaryingFromBlocks A11 A12 A21 A22
        (Fin.castAdd n i) (Fin.castAdd n j) = A11 i j := by
  simp [higham13VaryingFromBlocks]

@[simp] theorem higham13VaryingFromBlocks_apply₁₂ {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ) (i : Fin r) (j : Fin n) :
    higham13VaryingFromBlocks A11 A12 A21 A22
        (Fin.castAdd n i) (Fin.natAdd r j) = A12 i j := by
  simp [higham13VaryingFromBlocks]

@[simp] theorem higham13VaryingFromBlocks_apply₂₁ {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (j : Fin r) :
    higham13VaryingFromBlocks A11 A12 A21 A22
        (Fin.natAdd r i) (Fin.castAdd n j) = A21 i j := by
  simp [higham13VaryingFromBlocks]

@[simp] theorem higham13VaryingFromBlocks_apply₂₂ {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    higham13VaryingFromBlocks A11 A12 A21 A22
        (Fin.natAdd r i) (Fin.natAdd r j) = A22 i j := by
  simp [higham13VaryingFromBlocks]

/-- Recover the `Fin r ⊕ Fin n` representation of a cumulative split. -/
noncomputable def higham13VaryingToBlocks {r n : ℕ}
    (A : Matrix (Fin (r + n)) (Fin (r + n)) ℝ) :
    Matrix (Fin r ⊕ Fin n) (Fin r ⊕ Fin n) ℝ :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A

@[simp] theorem higham13VaryingToBlocks_apply₁₁ {r n : ℕ}
    (A : Matrix (Fin (r + n)) (Fin (r + n)) ℝ) (i j : Fin r) :
    higham13VaryingToBlocks A (Sum.inl i) (Sum.inl j) =
      A (Fin.castAdd n i) (Fin.castAdd n j) := by
  simp [higham13VaryingToBlocks]

@[simp] theorem higham13VaryingToBlocks_apply₁₂ {r n : ℕ}
    (A : Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (i : Fin r) (j : Fin n) :
    higham13VaryingToBlocks A (Sum.inl i) (Sum.inr j) =
      A (Fin.castAdd n i) (Fin.natAdd r j) := by
  simp [higham13VaryingToBlocks]

@[simp] theorem higham13VaryingToBlocks_apply₂₁ {r n : ℕ}
    (A : Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (i : Fin n) (j : Fin r) :
    higham13VaryingToBlocks A (Sum.inr i) (Sum.inl j) =
      A (Fin.natAdd r i) (Fin.castAdd n j) := by
  simp [higham13VaryingToBlocks]

@[simp] theorem higham13VaryingToBlocks_apply₂₂ {r n : ℕ}
    (A : Matrix (Fin (r + n)) (Fin (r + n)) ℝ) (i j : Fin n) :
    higham13VaryingToBlocks A (Sum.inr i) (Sum.inr j) =
      A (Fin.natAdd r i) (Fin.natAdd r j) := by
  simp [higham13VaryingToBlocks]

@[simp] theorem higham13VaryingToBlocks_fromBlocks {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ) :
    higham13VaryingToBlocks
        (higham13VaryingFromBlocks A11 A12 A21 A22) =
      Matrix.fromBlocks A11 A12 A21 A22 := by
  simp [higham13VaryingToBlocks, higham13VaryingFromBlocks]

@[simp] theorem higham13VaryingFromBlocks_toBlocks {r n : ℕ}
    (A : Matrix (Fin (r + n)) (Fin (r + n)) ℝ) :
    higham13VaryingFromBlocks
        (higham13VaryingToBlocks A).toBlocks₁₁
        (higham13VaryingToBlocks A).toBlocks₁₂
        (higham13VaryingToBlocks A).toBlocks₂₁
        (higham13VaryingToBlocks A).toBlocks₂₂ = A := by
  unfold higham13VaryingFromBlocks
  rw [Matrix.fromBlocks_toBlocks (higham13VaryingToBlocks A)]
  simp [higham13VaryingToBlocks]

/-- Reindexing the four-block constructor does not change its determinant. -/
theorem higham13VaryingFromBlocks_det {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.det (higham13VaryingFromBlocks A11 A12 A21 A22) =
      Matrix.det (Matrix.fromBlocks A11 A12 A21 A22) := by
  exact Matrix.det_reindex_self finSumFinEquiv
    (Matrix.fromBlocks A11 A12 A21 A22)

/-- Unit block-lower-triangular shape for unequal block orders. -/
def Higham13VaryingBlockUnitLower :
    (dims : List ℕ) →
      Matrix (Higham13VaryingBlockIndex dims)
        (Higham13VaryingBlockIndex dims) ℝ → Prop
  | [], _L => True
  | _r :: rs, L =>
      (higham13VaryingToBlocks L).toBlocks₁₁ = 1 ∧
      (higham13VaryingToBlocks L).toBlocks₁₂ = 0 ∧
      Higham13VaryingBlockUnitLower rs
        (higham13VaryingToBlocks L).toBlocks₂₂

/-- Block-upper-triangular shape for unequal block orders. -/
def Higham13VaryingBlockUpper :
    (dims : List ℕ) →
      Matrix (Higham13VaryingBlockIndex dims)
        (Higham13VaryingBlockIndex dims) ℝ → Prop
  | [], _U => True
  | _r :: rs, U =>
      (higham13VaryingToBlocks U).toBlocks₂₁ = 0 ∧
      Higham13VaryingBlockUpper rs
        (higham13VaryingToBlocks U).toBlocks₂₂

/-- Exact block LU certificate for a partition with possibly unequal positive
block orders. -/
structure Higham13VaryingBlockLUFactSpec (dims : List ℕ)
    (A L U : Matrix (Higham13VaryingBlockIndex dims)
      (Higham13VaryingBlockIndex dims) ℝ) : Prop where
  lower : Higham13VaryingBlockUnitLower dims L
  upper : Higham13VaryingBlockUpper dims U
  product_eq : L * U = A

/-- The scalar order in a taken block prefix never exceeds the total order. -/
theorem higham13_sum_take_le_sum (dims : List ℕ) (k : ℕ) :
    (dims.take k).sum ≤ dims.sum := by
  have hsum : (dims.take k).sum + (dims.drop k).sum = dims.sum := by
    rw [← List.sum_append, List.take_append_drop]
  omega

/-- Leading principal scalar matrix containing the first `k` (possibly
unequal) blocks. -/
noncomputable def higham13VaryingLeadingSubmatrix (dims : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex dims)
      (Higham13VaryingBlockIndex dims) ℝ) (k : ℕ) :
    Matrix (Fin (dims.take k).sum) (Fin (dims.take k).sum) ℝ :=
  A.submatrix (Fin.castLE (higham13_sum_take_le_sum dims k))
    (Fin.castLE (higham13_sum_take_le_sum dims k))

/-- Higham's source condition for Theorem 13.2 with unequal block orders:
every nonempty proper leading principal block submatrix is nonsingular. -/
def Higham13VaryingLeadingPrincipalNonsingular (dims : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex dims)
      (Higham13VaryingBlockIndex dims) ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → k < dims.length →
    Matrix.det (higham13VaryingLeadingSubmatrix dims A k) ≠ 0

/-- Block orders are genuine positive dimensions. -/
def Higham13PositiveBlockOrders (dims : List ℕ) : Prop :=
  ∀ r : ℕ, r ∈ dims → 0 < r

/-- The reindexed block constructor preserves multiplication. -/
theorem higham13VaryingFromBlocks_mul {r n : ℕ}
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A12 : Matrix (Fin r) (Fin n) ℝ)
    (A21 : Matrix (Fin n) (Fin r) ℝ)
    (A22 : Matrix (Fin n) (Fin n) ℝ)
    (B11 : Matrix (Fin r) (Fin r) ℝ)
    (B12 : Matrix (Fin r) (Fin n) ℝ)
    (B21 : Matrix (Fin n) (Fin r) ℝ)
    (B22 : Matrix (Fin n) (Fin n) ℝ) :
    higham13VaryingFromBlocks A11 A12 A21 A22 *
        higham13VaryingFromBlocks B11 B12 B21 B22 =
      higham13VaryingFromBlocks
        (A11 * B11 + A12 * B21) (A11 * B12 + A12 * B22)
        (A21 * B11 + A22 * B21) (A21 * B12 + A22 * B22) := by
  apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
  change higham13VaryingToBlocks
      (higham13VaryingFromBlocks A11 A12 A21 A22 *
        higham13VaryingFromBlocks B11 B12 B21 B22) =
    higham13VaryingToBlocks
      (higham13VaryingFromBlocks
        (A11 * B11 + A12 * B21) (A11 * B12 + A12 * B22)
        (A21 * B11 + A22 * B21) (A21 * B12 + A22 * B22))
  rw [show higham13VaryingToBlocks
      (higham13VaryingFromBlocks A11 A12 A21 A22 *
        higham13VaryingFromBlocks B11 B12 B21 B22) =
      higham13VaryingToBlocks
          (higham13VaryingFromBlocks A11 A12 A21 A22) *
        higham13VaryingToBlocks
          (higham13VaryingFromBlocks B11 B12 B21 B22) by
    simp [higham13VaryingToBlocks]]
  simp [Matrix.fromBlocks_multiply]

/-- Recovering the first/tail split commutes with ordinary matrix
multiplication. -/
theorem higham13VaryingToBlocks_mul {r n : ℕ}
    (A B : Matrix (Fin (r + n)) (Fin (r + n)) ℝ) :
    higham13VaryingToBlocks (A * B) =
      higham13VaryingToBlocks A * higham13VaryingToBlocks B := by
  simp [higham13VaryingToBlocks]

/-- The four ordinary block equations extracted from an exact product. -/
theorem higham13VaryingProductBlocks {r n : ℕ}
    {A L U : Matrix (Fin (r + n)) (Fin (r + n)) ℝ}
    (hprod : L * U = A) :
    let Lb := higham13VaryingToBlocks L
    let Ub := higham13VaryingToBlocks U
    let Ab := higham13VaryingToBlocks A
    Lb.toBlocks₁₁ * Ub.toBlocks₁₁ +
          Lb.toBlocks₁₂ * Ub.toBlocks₂₁ = Ab.toBlocks₁₁ ∧
      Lb.toBlocks₁₁ * Ub.toBlocks₁₂ +
          Lb.toBlocks₁₂ * Ub.toBlocks₂₂ = Ab.toBlocks₁₂ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₁ +
          Lb.toBlocks₂₂ * Ub.toBlocks₂₁ = Ab.toBlocks₂₁ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₂ +
          Lb.toBlocks₂₂ * Ub.toBlocks₂₂ = Ab.toBlocks₂₂ := by
  dsimp only
  have hblocks :
      higham13VaryingToBlocks L * higham13VaryingToBlocks U =
        higham13VaryingToBlocks A := by
    rw [← higham13VaryingToBlocks_mul, hprod]
  rw [← Matrix.fromBlocks_toBlocks (higham13VaryingToBlocks L),
    ← Matrix.fromBlocks_toBlocks (higham13VaryingToBlocks U),
    Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_toBlocks (higham13VaryingToBlocks A)] at hblocks
  constructor
  · exact congrArg Matrix.toBlocks₁₁ hblocks
  constructor
  · exact congrArg Matrix.toBlocks₁₂ hblocks
  constructor
  · exact congrArg Matrix.toBlocks₂₁ hblocks
  · exact congrArg Matrix.toBlocks₂₂ hblocks

@[simp] theorem higham13VaryingBlockUnitLower_fromBlocks {r : ℕ}
    {rs : List ℕ}
    (L21 : Matrix (Fin rs.sum) (Fin r) ℝ)
    (L22 : Matrix (Fin rs.sum) (Fin rs.sum) ℝ) :
    Higham13VaryingBlockUnitLower (r :: rs)
        (higham13VaryingFromBlocks 1 0 L21 L22) ↔
      Higham13VaryingBlockUnitLower rs L22 := by
  simp [Higham13VaryingBlockUnitLower]

@[simp] theorem higham13VaryingBlockUpper_fromBlocks {r : ℕ}
    {rs : List ℕ}
    (U11 : Matrix (Fin r) (Fin r) ℝ)
    (U12 : Matrix (Fin r) (Fin rs.sum) ℝ)
    (U22 : Matrix (Fin rs.sum) (Fin rs.sum) ℝ) :
    Higham13VaryingBlockUpper (r :: rs)
        (higham13VaryingFromBlocks U11 U12 0 U22) ↔
      Higham13VaryingBlockUpper rs U22 := by
  simp [Higham13VaryingBlockUpper]

/-- Updating only rows in the first scalar block row preserves the recursive
block-upper shape. -/
theorem higham13VaryingBlockUpper_sub_mul_of_rows_zero {s r : ℕ}
    {ss : List ℕ}
    {U : Matrix
      (Fin (List.foldr (fun r n => r + n) 0 (s :: ss)))
      (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) ℝ}
    (hU : Higham13VaryingBlockUpper (s :: ss) U)
    (X : Matrix
      (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) (Fin r) ℝ)
    (B : Matrix (Fin r)
      (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) ℝ)
    (hXzero : ∀ i : Fin (List.foldr (fun r n => r + n) 0 (s :: ss)),
      s ≤ i.val → ∀ j : Fin r, X i j = 0) :
    Higham13VaryingBlockUpper (s :: ss) (U - X * B) := by
  have hshape : (higham13VaryingToBlocks U).toBlocks₂₁ = 0 ∧
      Higham13VaryingBlockUpper ss
        (higham13VaryingToBlocks U).toBlocks₂₂ := by
    simpa only [Higham13VaryingBlockUpper] using hU
  refine ⟨?_, ?_⟩
  · ext i j
    have hu := congr_fun (congr_fun hshape.1 i) j
    change U (Fin.natAdd s i)
      (Fin.castAdd (List.foldr (fun r n => r + n) 0 ss) j) = 0 at hu
    change U (Fin.natAdd s i)
        (Fin.castAdd (List.foldr (fun r n => r + n) 0 ss) j) -
      (X * B) (Fin.natAdd s i)
        (Fin.castAdd (List.foldr (fun r n => r + n) 0 ss) j) = 0
    have hx : ∀ q : Fin r, X (Fin.natAdd s i) q = 0 :=
      hXzero (Fin.natAdd s i) (by simp)
    rw [show (X * B) (Fin.natAdd s i)
        (Fin.castAdd (List.foldr (fun r n => r + n) 0 ss) j) = 0 by
      change (∑ q : Fin r, X (Fin.natAdd s i) q *
        B q (Fin.castAdd (List.foldr (fun r n => r + n) 0 ss) j)) = 0
      apply Finset.sum_eq_zero
      intro q _hq
      rw [hx q, zero_mul]]
    exact sub_eq_zero.mpr hu
  · have heq : (higham13VaryingToBlocks (U - X * B)).toBlocks₂₂ =
        (higham13VaryingToBlocks U).toBlocks₂₂ := by
      ext i j
      change U (Fin.natAdd s i) (Fin.natAdd s j) -
          (X * B) (Fin.natAdd s i) (Fin.natAdd s j) =
        U (Fin.natAdd s i) (Fin.natAdd s j)
      have hx : ∀ q : Fin r, X (Fin.natAdd s i) q = 0 :=
        hXzero (Fin.natAdd s i) (by simp)
      rw [show (X * B) (Fin.natAdd s i) (Fin.natAdd s j) = 0 by
        change (∑ q : Fin r, X (Fin.natAdd s i) q *
          B q (Fin.natAdd s j)) = 0
        apply Finset.sum_eq_zero
        intro q _hq
        rw [hx q, zero_mul]]
      exact sub_zero _
    rw [heq]
    exact hshape.2

/-- Splitting a cumulative leading prefix exposes the original first block
and the corresponding leading part of the tail. -/
theorem higham13VaryingLeadingSubmatrix_cons_succ {r : ℕ}
    (rs : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ) (k : ℕ) :
    higham13VaryingLeadingSubmatrix (r :: rs) A (k + 1) =
      higham13VaryingFromBlocks
        (higham13VaryingToBlocks A).toBlocks₁₁
        ((higham13VaryingToBlocks A).toBlocks₁₂.submatrix
          id (Fin.castLE (higham13_sum_take_le_sum rs k)))
        ((higham13VaryingToBlocks A).toBlocks₂₁.submatrix
          (Fin.castLE (higham13_sum_take_le_sum rs k)) id)
        (higham13VaryingLeadingSubmatrix rs
          (higham13VaryingToBlocks A).toBlocks₂₂ k) := by
  let P : Matrix (Fin (r + (rs.take k).sum))
      (Fin (r + (rs.take k).sum)) ℝ :=
    A.submatrix
      (Fin.castLE (Nat.add_le_add_left (higham13_sum_take_le_sum rs k) r))
      (Fin.castLE (Nat.add_le_add_left (higham13_sum_take_le_sum rs k) r))
  have hP : higham13VaryingLeadingSubmatrix (r :: rs) A (k + 1) = P := by
    ext i j
    simp [higham13VaryingLeadingSubmatrix, P, Matrix.submatrix_apply]
  rw [hP]
  apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
  change higham13VaryingToBlocks P =
    higham13VaryingToBlocks
      (higham13VaryingFromBlocks
        (higham13VaryingToBlocks A).toBlocks₁₁
        ((higham13VaryingToBlocks A).toBlocks₁₂.submatrix
          id (Fin.castLE (higham13_sum_take_le_sum rs k)))
        ((higham13VaryingToBlocks A).toBlocks₂₁.submatrix
          (Fin.castLE (higham13_sum_take_le_sum rs k)) id)
        (higham13VaryingLeadingSubmatrix rs
          (higham13VaryingToBlocks A).toBlocks₂₂ k))
  rw [higham13VaryingToBlocks_fromBlocks]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [P, higham13VaryingLeadingSubmatrix, higham13VaryingToBlocks,
      Matrix.submatrix_apply, Matrix.fromBlocks] <;>
    apply congrArg₂ A <;> apply Fin.ext <;> simp

/-- The first cumulative leading submatrix is exactly the leading diagonal
block. -/
theorem higham13VaryingLeadingSubmatrix_cons_one {r : ℕ}
    (rs : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ) :
    higham13VaryingLeadingSubmatrix (r :: rs) A 1 =
      (higham13VaryingToBlocks A).toBlocks₁₁ := by
  ext i j
  simp [higham13VaryingLeadingSubmatrix, higham13VaryingToBlocks,
    Matrix.submatrix_apply]
  apply congrArg₂ A <;> apply Fin.ext <;> simp

/-- First-block Schur complement for a partition whose tail may itself have
unequal block orders. -/
noncomputable def higham13VaryingSchur {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ) :
    Matrix (Fin (List.foldr (fun r n => r + n) 0 rs))
      (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ :=
  let Ab := higham13VaryingToBlocks A
  Ab.toBlocks₂₂ - Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂

/-- Taking a cumulative tail prefix commutes with the first-block Schur
complement. -/
theorem higham13VaryingLeadingSubmatrix_schur {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ) (k : ℕ) :
    higham13VaryingLeadingSubmatrix rs (higham13VaryingSchur A) k =
      higham13VaryingLeadingSubmatrix rs
          (higham13VaryingToBlocks A).toBlocks₂₂ k -
        ((higham13VaryingToBlocks A).toBlocks₂₁.submatrix
          (Fin.castLE (higham13_sum_take_le_sum rs k)) id) *
          (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
        ((higham13VaryingToBlocks A).toBlocks₁₂.submatrix
          id (Fin.castLE (higham13_sum_take_le_sum rs k))) := by
  ext i j
  simp [higham13VaryingLeadingSubmatrix, higham13VaryingSchur,
    Matrix.submatrix_apply, Matrix.mul_apply,
    Finset.sum_mul, mul_assoc]
  rfl

/-- The source leading-prefix nonsingularity condition descends to the Schur
tail for arbitrary positive or zero block orders.  Positivity is needed only
for the converse uniqueness argument below. -/
theorem Higham13VaryingLeadingPrincipalNonsingular.schur
    {r : ℕ} {rs : List ℕ}
    {A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ}
    (hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0)
    (hlead : Higham13VaryingLeadingPrincipalNonsingular (r :: rs) A) :
    Higham13VaryingLeadingPrincipalNonsingular rs
      (higham13VaryingSchur A) := by
  intro k hkpos hklt
  have hfull : Matrix.det
      (higham13VaryingLeadingSubmatrix (r :: rs) A (k + 1)) ≠ 0 :=
    hlead (k + 1) (Nat.succ_pos k) (by simpa using Nat.succ_lt_succ hklt)
  have hpref := higham13VaryingLeadingSubmatrix_cons_succ rs A k
  let A11 := (higham13VaryingToBlocks A).toBlocks₁₁
  let B := (higham13VaryingToBlocks A).toBlocks₁₂.submatrix
    id (Fin.castLE (higham13_sum_take_le_sum rs k))
  let C := (higham13VaryingToBlocks A).toBlocks₂₁.submatrix
    (Fin.castLE (higham13_sum_take_le_sum rs k)) id
  let D := higham13VaryingLeadingSubmatrix rs
    (higham13VaryingToBlocks A).toBlocks₂₂ k
  have hunit : IsUnit (Matrix.det A11) := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible A11 := Matrix.invertibleOfIsUnitDet A11 hunit
  have hschur : D - C * ⅟A11 * B =
      higham13VaryingLeadingSubmatrix rs (higham13VaryingSchur A) k := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact (higham13VaryingLeadingSubmatrix_schur A k).symm
  have hdetEq : Matrix.det
        (higham13VaryingLeadingSubmatrix (r :: rs) A (k + 1)) =
      Matrix.det A11 * Matrix.det
        (higham13VaryingLeadingSubmatrix rs (higham13VaryingSchur A) k) := by
    calc
      _ = Matrix.det (higham13VaryingFromBlocks A11 B C D) :=
        congrArg Matrix.det hpref
      _ = Matrix.det (Matrix.fromBlocks A11 B C D) :=
        higham13VaryingFromBlocks_det A11 B C D
      _ = Matrix.det A11 * Matrix.det (D - C * ⅟A11 * B) :=
        Matrix.det_fromBlocks₁₁ A11 B C D
      _ = _ := congrArg (fun X => Matrix.det A11 * Matrix.det X) hschur
  intro hzero
  apply hfull
  rw [hdetEq, hzero, mul_zero]

/-- Reverse Schur bookkeeping for the source leading-prefix condition. -/
theorem Higham13VaryingLeadingPrincipalNonsingular.of_det_of_schur
    {r : ℕ} {rs : List ℕ}
    {A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ}
    (hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0)
    (htail : Higham13VaryingLeadingPrincipalNonsingular rs
      (higham13VaryingSchur A)) :
    Higham13VaryingLeadingPrincipalNonsingular (r :: rs) A := by
  intro k hkpos hklt
  cases k with
  | zero => omega
  | succ t =>
      cases t with
      | zero =>
          simpa [higham13VaryingLeadingSubmatrix_cons_one] using hdet
      | succ p =>
          let kTail := p + 1
          have hkTailLt : kTail < rs.length := by
            simp at hklt
            omega
          have htailDet : Matrix.det
              (higham13VaryingLeadingSubmatrix rs
                (higham13VaryingSchur A) kTail) ≠ 0 :=
            htail kTail (by omega) hkTailLt
          have hpref := higham13VaryingLeadingSubmatrix_cons_succ rs A kTail
          let A11 := (higham13VaryingToBlocks A).toBlocks₁₁
          let B := (higham13VaryingToBlocks A).toBlocks₁₂.submatrix
            id (Fin.castLE (higham13_sum_take_le_sum rs kTail))
          let C := (higham13VaryingToBlocks A).toBlocks₂₁.submatrix
            (Fin.castLE (higham13_sum_take_le_sum rs kTail)) id
          let D := higham13VaryingLeadingSubmatrix rs
            (higham13VaryingToBlocks A).toBlocks₂₂ kTail
          have hunit : IsUnit (Matrix.det A11) :=
            isUnit_iff_ne_zero.mpr hdet
          letI : Invertible A11 := Matrix.invertibleOfIsUnitDet A11 hunit
          have hschur : D - C * ⅟A11 * B =
              higham13VaryingLeadingSubmatrix rs
                (higham13VaryingSchur A) kTail := by
            rw [Matrix.invOf_eq_nonsing_inv]
            exact (higham13VaryingLeadingSubmatrix_schur A kTail).symm
          have hdetEq : Matrix.det
                (higham13VaryingLeadingSubmatrix (r :: rs) A (kTail + 1)) =
              Matrix.det A11 * Matrix.det
                (higham13VaryingLeadingSubmatrix rs
                  (higham13VaryingSchur A) kTail) := by
            calc
              _ = Matrix.det (higham13VaryingFromBlocks A11 B C D) :=
                congrArg Matrix.det hpref
              _ = Matrix.det (Matrix.fromBlocks A11 B C D) :=
                higham13VaryingFromBlocks_det A11 B C D
              _ = Matrix.det A11 * Matrix.det (D - C * ⅟A11 * B) :=
                Matrix.det_fromBlocks₁₁ A11 B C D
              _ = _ := congrArg
                (fun X => Matrix.det A11 * Matrix.det X) hschur
          change Matrix.det
            (higham13VaryingLeadingSubmatrix (r :: rs) A (kTail + 1)) ≠ 0
          rw [hdetEq]
          exact mul_ne_zero hdet htailDet

/-- One Schur step's block unit-lower factor. -/
noncomputable def higham13VaryingStepL {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    (Ls : Matrix (Fin (List.foldr (fun r n => r + n) 0 rs))
      (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ) :
    Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ :=
  let Ab := higham13VaryingToBlocks A
  higham13VaryingFromBlocks 1 0
    (Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹) Ls

/-- One Schur step's block-upper factor. -/
noncomputable def higham13VaryingStepU {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    (Us : Matrix (Fin (List.foldr (fun r n => r + n) 0 rs))
      (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ) :
    Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ :=
  let Ab := higham13VaryingToBlocks A
  higham13VaryingFromBlocks Ab.toBlocks₁₁ Ab.toBlocks₁₂ 0 Us

/-- The unequal-order Schur construction multiplies back to the original
matrix. -/
theorem higham13VaryingStep_mul {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    (Ls Us : Matrix (Fin (List.foldr (fun r n => r + n) 0 rs))
      (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ)
    (hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0)
    (htail : Ls * Us = higham13VaryingSchur A) :
    higham13VaryingStepL A Ls * higham13VaryingStepU A Us = A := by
  have hunit : IsUnit (Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁) :=
    isUnit_iff_ne_zero.mpr hdet
  apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
  change higham13VaryingToBlocks
      (higham13VaryingStepL A Ls * higham13VaryingStepU A Us) =
    higham13VaryingToBlocks A
  rw [show higham13VaryingToBlocks
      (higham13VaryingStepL A Ls * higham13VaryingStepU A Us) =
        higham13VaryingToBlocks (higham13VaryingStepL A Ls) *
          higham13VaryingToBlocks (higham13VaryingStepU A Us) by
    simpa only using higham13VaryingToBlocks_mul
      (r := r) (n := rs.sum)
      (higham13VaryingStepL A Ls) (higham13VaryingStepU A Us)]
  simp only [higham13VaryingStepL, higham13VaryingStepU]
  rw [higham13VaryingToBlocks_fromBlocks,
    higham13VaryingToBlocks_fromBlocks, Matrix.fromBlocks_multiply]
  have htail' : Ls * Us =
      (higham13VaryingToBlocks A).toBlocks₂₂ -
        (higham13VaryingToBlocks A).toBlocks₂₁ *
          (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
            (higham13VaryingToBlocks A).toBlocks₁₂ := by
    simpa only [higham13VaryingSchur] using htail
  have hinv : (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
      (higham13VaryingToBlocks A).toBlocks₁₁ = 1 :=
    Matrix.nonsing_inv_mul _ hunit
  rw [← Matrix.fromBlocks_toBlocks (higham13VaryingToBlocks A)]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁]
  rw [Matrix.fromBlocks_inj]
  constructor
  · ext i j
    simp
  constructor
  · have hz : (0 : Matrix (Fin r)
        (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ) * Us = 0 :=
      Matrix.zero_mul Us
    change (1 : Matrix (Fin r) (Fin r) ℝ) *
          (higham13VaryingToBlocks A).toBlocks₁₂ +
        (0 : Matrix (Fin r)
          (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ) * Us =
      (higham13VaryingToBlocks A).toBlocks₁₂
    rw [Matrix.one_mul, hz, add_zero]
  constructor
  · have hz : Ls * (0 : Matrix
        (Fin (List.foldr (fun r n => r + n) 0 rs)) (Fin r) ℝ) = 0 :=
      Matrix.mul_zero Ls
    have hmain :
        (higham13VaryingToBlocks A).toBlocks₂₁ *
            (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
              (higham13VaryingToBlocks A).toBlocks₁₁ =
          (higham13VaryingToBlocks A).toBlocks₂₁ := by
      calc
        _ = (higham13VaryingToBlocks A).toBlocks₂₁ *
              ((higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
                (higham13VaryingToBlocks A).toBlocks₁₁) :=
            Matrix.mul_assoc _ _ _
        _ = (higham13VaryingToBlocks A).toBlocks₂₁ * 1 :=
          congrArg _ hinv
        _ = _ := Matrix.mul_one _
    change (higham13VaryingToBlocks A).toBlocks₂₁ *
          (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
            (higham13VaryingToBlocks A).toBlocks₁₁ +
        Ls * (0 : Matrix
          (Fin (List.foldr (fun r n => r + n) 0 rs)) (Fin r) ℝ) =
      (higham13VaryingToBlocks A).toBlocks₂₁
    rw [hz, add_zero]
    exact hmain
  · calc
      ((higham13VaryingToBlocks A).toBlocks₂₁ *
            (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
              (higham13VaryingToBlocks A).toBlocks₁₂ :
          Matrix (Fin (List.foldr (fun r n => r + n) 0 rs))
            (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ) + Ls * Us =
          (higham13VaryingToBlocks A).toBlocks₂₁ *
            (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
              (higham13VaryingToBlocks A).toBlocks₁₂ +
            ((higham13VaryingToBlocks A).toBlocks₂₂ -
              (higham13VaryingToBlocks A).toBlocks₂₁ *
                (higham13VaryingToBlocks A).toBlocks₁₁⁻¹ *
                  (higham13VaryingToBlocks A).toBlocks₁₂) :=
        congrArg _ htail'
      _ = (higham13VaryingToBlocks A).toBlocks₂₂ := by abel

/-- Lift an exact unequal-order factorization of the Schur tail through one
block Gaussian-elimination step. -/
theorem Higham13VaryingBlockLUFactSpec.step {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    {Ls Us : Matrix (Fin (List.foldr (fun r n => r + n) 0 rs))
      (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ}
    (hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0)
    (htail : Higham13VaryingBlockLUFactSpec rs
      (higham13VaryingSchur A) Ls Us) :
    Higham13VaryingBlockLUFactSpec (r :: rs) A
      (higham13VaryingStepL A Ls) (higham13VaryingStepU A Us) := by
  refine ⟨?_, ?_, higham13VaryingStep_mul A Ls Us hdet htail.product_eq⟩
  · simpa [higham13VaryingStepL] using htail.lower
  · simpa [higham13VaryingStepU] using htail.upper

/-- Uniqueness also lifts through an unequal-order Schur step. -/
theorem Higham13VaryingBlockLUFactSpec.eq_step_of_tail_unique
    {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    {Ls Us : Matrix (Fin (List.foldr (fun r n => r + n) 0 rs))
      (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ}
    (hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0)
    (_htail : Higham13VaryingBlockLUFactSpec rs
      (higham13VaryingSchur A) Ls Us)
    (hunique : ∀ L' U' : Matrix
        (Fin (List.foldr (fun r n => r + n) 0 rs))
        (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ,
      Higham13VaryingBlockLUFactSpec rs
        (higham13VaryingSchur A) L' U' → L' = Ls ∧ U' = Us)
    {L U : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ}
    (hLU : Higham13VaryingBlockLUFactSpec (r :: rs) A L U) :
    L = higham13VaryingStepL A Ls ∧
      U = higham13VaryingStepU A Us := by
  let Ab := higham13VaryingToBlocks A
  let Lb := higham13VaryingToBlocks L
  let Ub := higham13VaryingToBlocks U
  have hLshape : Lb.toBlocks₁₁ = 1 ∧ Lb.toBlocks₁₂ = 0 ∧
      Higham13VaryingBlockUnitLower rs Lb.toBlocks₂₂ := by
    simpa only [Higham13VaryingBlockUnitLower] using hLU.lower
  have hUshape : Ub.toBlocks₂₁ = 0 ∧
      Higham13VaryingBlockUpper rs Ub.toBlocks₂₂ := by
    simpa only [Higham13VaryingBlockUpper] using hLU.upper
  have hblocks := higham13VaryingProductBlocks
    (r := r) (n := List.foldr (fun r n => r + n) 0 rs)
    hLU.product_eq
  change
    Lb.toBlocks₁₁ * Ub.toBlocks₁₁ + Lb.toBlocks₁₂ * Ub.toBlocks₂₁ =
          Ab.toBlocks₁₁ ∧
      Lb.toBlocks₁₁ * Ub.toBlocks₁₂ + Lb.toBlocks₁₂ * Ub.toBlocks₂₂ =
          Ab.toBlocks₁₂ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₁ + Lb.toBlocks₂₂ * Ub.toBlocks₂₁ =
          Ab.toBlocks₂₁ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₂ + Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
          Ab.toBlocks₂₂ at hblocks
  have hU11 : Ub.toBlocks₁₁ = Ab.toBlocks₁₁ := by
    simpa [hLshape.1, hLshape.2.1, hUshape.1, Matrix.zero_mul] using hblocks.1
  have hU12 : Ub.toBlocks₁₂ = Ab.toBlocks₁₂ := by
    simpa [hLshape.1, hLshape.2.1, Matrix.zero_mul] using hblocks.2.1
  have hunit : IsUnit (Matrix.det Ab.toBlocks₁₁) :=
    isUnit_iff_ne_zero.mpr hdet
  have hrightInv : Ab.toBlocks₁₁ * Ab.toBlocks₁₁⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hunit
  have hL21 : Lb.toBlocks₂₁ = Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ := by
    have hprod : Lb.toBlocks₂₁ * Ab.toBlocks₁₁ = Ab.toBlocks₂₁ := by
      simpa [hU11, hUshape.1, Matrix.mul_zero] using hblocks.2.2.1
    calc
      Lb.toBlocks₂₁ = Lb.toBlocks₂₁ * 1 := (Matrix.mul_one _).symm
      _ = Lb.toBlocks₂₁ * (Ab.toBlocks₁₁ * Ab.toBlocks₁₁⁻¹) :=
        congrArg _ hrightInv.symm
      _ = (Lb.toBlocks₂₁ * Ab.toBlocks₁₁) * Ab.toBlocks₁₁⁻¹ := by
        rw [Matrix.mul_assoc]
      _ = Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ :=
        congrArg (fun X => X * Ab.toBlocks₁₁⁻¹) hprod
  have htailProd : Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
      higham13VaryingSchur A := by
    have h22 := hblocks.2.2.2
    rw [hL21, hU12] at h22
    change Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
      Ab.toBlocks₂₂ - Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂
    calc
      Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
          (Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂ +
            Lb.toBlocks₂₂ * Ub.toBlocks₂₂) -
              Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂ := by abel
      _ = Ab.toBlocks₂₂ -
          Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂ :=
        congrArg (fun X => X -
          Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂) h22
  have htailSpec : Higham13VaryingBlockLUFactSpec rs
      (higham13VaryingSchur A) Lb.toBlocks₂₂ Ub.toBlocks₂₂ :=
    ⟨hLshape.2.2, hUshape.2, htailProd⟩
  rcases hunique Lb.toBlocks₂₂ Ub.toBlocks₂₂ htailSpec with
    ⟨hL22, hU22⟩
  constructor
  · apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
    change Lb = higham13VaryingToBlocks (higham13VaryingStepL A Ls)
    simp only [higham13VaryingStepL]
    rw [higham13VaryingToBlocks_fromBlocks]
    rw [← Matrix.fromBlocks_toBlocks Lb, Matrix.fromBlocks_inj]
    exact ⟨hLshape.1, hLshape.2.1, hL21, hL22⟩
  · apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
    change Ub = higham13VaryingToBlocks (higham13VaryingStepU A Us)
    simp only [higham13VaryingStepU]
    rw [higham13VaryingToBlocks_fromBlocks]
    rw [← Matrix.fromBlocks_toBlocks Ub, Matrix.fromBlocks_inj]
    exact ⟨hU11, hU12, hUshape.1, hU22⟩

/-- Any full factorization with a nonsingular first pivot restricts to an
exact factorization of the unequal-order Schur tail. -/
theorem Higham13VaryingBlockLUFactSpec.schurTail_of_det
    {r : ℕ} {rs : List ℕ}
    {A L U : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ}
    (hLU : Higham13VaryingBlockLUFactSpec (r :: rs) A L U)
    (hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0) :
    Higham13VaryingBlockLUFactSpec rs (higham13VaryingSchur A)
      (higham13VaryingToBlocks L).toBlocks₂₂
      (higham13VaryingToBlocks U).toBlocks₂₂ := by
  let Ab := higham13VaryingToBlocks A
  let Lb := higham13VaryingToBlocks L
  let Ub := higham13VaryingToBlocks U
  have hLshape : Lb.toBlocks₁₁ = 1 ∧ Lb.toBlocks₁₂ = 0 ∧
      Higham13VaryingBlockUnitLower rs Lb.toBlocks₂₂ := by
    simpa only [Higham13VaryingBlockUnitLower] using hLU.lower
  have hUshape : Ub.toBlocks₂₁ = 0 ∧
      Higham13VaryingBlockUpper rs Ub.toBlocks₂₂ := by
    simpa only [Higham13VaryingBlockUpper] using hLU.upper
  have hblocks := higham13VaryingProductBlocks
    (r := r) (n := List.foldr (fun r n => r + n) 0 rs)
    hLU.product_eq
  change
    Lb.toBlocks₁₁ * Ub.toBlocks₁₁ + Lb.toBlocks₁₂ * Ub.toBlocks₂₁ =
          Ab.toBlocks₁₁ ∧
      Lb.toBlocks₁₁ * Ub.toBlocks₁₂ + Lb.toBlocks₁₂ * Ub.toBlocks₂₂ =
          Ab.toBlocks₁₂ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₁ + Lb.toBlocks₂₂ * Ub.toBlocks₂₁ =
          Ab.toBlocks₂₁ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₂ + Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
          Ab.toBlocks₂₂ at hblocks
  have hU11 : Ub.toBlocks₁₁ = Ab.toBlocks₁₁ := by
    simpa [hLshape.1, hLshape.2.1, hUshape.1, Matrix.zero_mul] using hblocks.1
  have hU12 : Ub.toBlocks₁₂ = Ab.toBlocks₁₂ := by
    simpa [hLshape.1, hLshape.2.1, Matrix.zero_mul] using hblocks.2.1
  have hunit : IsUnit (Matrix.det Ab.toBlocks₁₁) :=
    isUnit_iff_ne_zero.mpr hdet
  have hrightInv : Ab.toBlocks₁₁ * Ab.toBlocks₁₁⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hunit
  have hL21 : Lb.toBlocks₂₁ = Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ := by
    have hprod : Lb.toBlocks₂₁ * Ab.toBlocks₁₁ = Ab.toBlocks₂₁ := by
      simpa [hU11, hUshape.1, Matrix.mul_zero] using hblocks.2.2.1
    calc
      Lb.toBlocks₂₁ = Lb.toBlocks₂₁ * 1 := (Matrix.mul_one _).symm
      _ = Lb.toBlocks₂₁ * (Ab.toBlocks₁₁ * Ab.toBlocks₁₁⁻¹) :=
        congrArg _ hrightInv.symm
      _ = (Lb.toBlocks₂₁ * Ab.toBlocks₁₁) * Ab.toBlocks₁₁⁻¹ := by
        rw [Matrix.mul_assoc]
      _ = Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ :=
        congrArg (fun X => X * Ab.toBlocks₁₁⁻¹) hprod
  have htailProd : Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
      higham13VaryingSchur A := by
    have h22 := hblocks.2.2.2
    rw [hL21, hU12] at h22
    change Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
      Ab.toBlocks₂₂ - Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂
    calc
      Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
          (Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂ +
            Lb.toBlocks₂₂ * Ub.toBlocks₂₂) -
              Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂ := by abel
      _ = Ab.toBlocks₂₂ -
          Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂ :=
        congrArg (fun X => X -
          Ab.toBlocks₂₁ * Ab.toBlocks₁₁⁻¹ * Ab.toBlocks₁₂) h22
  exact ⟨hLshape.2.2, hUshape.2, htailProd⟩

/-- Existence and uniqueness of an exact block LU factorization for a fixed
unequal-order partition. -/
def Higham13VaryingBlockLUExistsUnique (dims : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex dims)
      (Higham13VaryingBlockIndex dims) ℝ) : Prop :=
  ∃ L U : Matrix (Higham13VaryingBlockIndex dims)
      (Higham13VaryingBlockIndex dims) ℝ,
    Higham13VaryingBlockLUFactSpec dims A L U ∧
      ∀ L' U' : Matrix (Higham13VaryingBlockIndex dims)
          (Higham13VaryingBlockIndex dims) ℝ,
        Higham13VaryingBlockLUFactSpec dims A L' U' →
          L' = L ∧ U' = U

private theorem higham13_matrix_fin_zero_rows_eq_zero {n : ℕ}
    (M : Matrix (Fin 0) (Fin n) ℝ) : M = 0 := by
  ext i
  exact Fin.elim0 i

private theorem higham13_matrix_fin_zero_cols_eq_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin 0) ℝ) : M = 0 := by
  ext i j
  exact Fin.elim0 j

/-- A single (possibly nonsingular or singular) block always has the unique
factorization `L = I`, `U = A`. -/
theorem Higham13VaryingBlockLUExistsUnique.one (r : ℕ)
    (A : Matrix (Higham13VaryingBlockIndex [r])
      (Higham13VaryingBlockIndex [r]) ℝ) :
    Higham13VaryingBlockLUExistsUnique [r] A := by
  let L0 : Matrix (Fin (r + 0)) (Fin (r + 0)) ℝ :=
    higham13VaryingFromBlocks
      (1 : Matrix (Fin r) (Fin r) ℝ)
      (0 : Matrix (Fin r) (Fin 0) ℝ)
      (0 : Matrix (Fin 0) (Fin r) ℝ)
      (0 : Matrix (Fin 0) (Fin 0) ℝ)
  have hL0one : L0 = 1 := by
    apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
    change higham13VaryingToBlocks L0 = higham13VaryingToBlocks 1
    rw [show higham13VaryingToBlocks L0 = Matrix.fromBlocks
        (1 : Matrix (Fin r) (Fin r) ℝ)
        (0 : Matrix (Fin r) (Fin 0) ℝ)
        (0 : Matrix (Fin 0) (Fin r) ℝ)
        (0 : Matrix (Fin 0) (Fin 0) ℝ) by
      simp [L0]]
    ext p q
    rcases p with i | i
    · rcases q with j | j
      · simp [higham13VaryingToBlocks, Matrix.fromBlocks,
          Matrix.one_apply]
      · exact Fin.elim0 j
    · exact Fin.elim0 i
  refine ⟨L0, A, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [Higham13VaryingBlockUnitLower, L0]
      rfl
    · constructor
      · exact higham13_matrix_fin_zero_rows_eq_zero _
      · trivial
    · rw [hL0one]
      simpa only using Matrix.one_mul A
  · intro L U hLU
    have hLshape :
        (higham13VaryingToBlocks L).toBlocks₁₁ = 1 ∧
        (higham13VaryingToBlocks L).toBlocks₁₂ = 0 := by
      simpa [Higham13VaryingBlockUnitLower] using hLU.lower
    have hLeq : L = L0 := by
      apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
      change higham13VaryingToBlocks L = higham13VaryingToBlocks L0
      have hcanon : higham13VaryingToBlocks L0 = Matrix.fromBlocks
          (1 : Matrix (Fin r) (Fin r) ℝ)
          (0 : Matrix (Fin r) (Fin 0) ℝ)
          (0 : Matrix (Fin 0) (Fin r) ℝ)
          (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
        simp [L0]
      have hL21 : (higham13VaryingToBlocks L).toBlocks₂₁ = 0 :=
        higham13_matrix_fin_zero_rows_eq_zero _
      have hL22 : (higham13VaryingToBlocks L).toBlocks₂₂ = 0 :=
        higham13_matrix_fin_zero_rows_eq_zero _
      exact (Matrix.ext_iff_blocks.mpr
        ⟨hLshape.1, hLshape.2, hL21, hL22⟩).trans hcanon.symm
    constructor
    · exact hLeq
    · have hprod := hLU.product_eq
      rw [hLeq, hL0one] at hprod
      exact (Matrix.one_mul U).symm.trans hprod

/-- Forward direction of Higham's Theorem 13.2 for genuinely unequal block
orders. -/
theorem Higham13VaryingBlockLUExistsUnique.of_leadingPrincipalNonsingular
    (r : ℕ) (rs : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    (hlead : Higham13VaryingLeadingPrincipalNonsingular (r :: rs) A) :
    Higham13VaryingBlockLUExistsUnique (r :: rs) A := by
  induction rs generalizing r with
  | nil => exact Higham13VaryingBlockLUExistsUnique.one r A
  | cons s ss ih =>
      have hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0 := by
        have hfirst := hlead 1 (by omega) (by simp)
        rwa [higham13VaryingLeadingSubmatrix_cons_one] at hfirst
      have htailLead : Higham13VaryingLeadingPrincipalNonsingular (s :: ss)
          (higham13VaryingSchur A) :=
        Higham13VaryingLeadingPrincipalNonsingular.schur hdet hlead
      rcases ih s (higham13VaryingSchur A) htailLead with
        ⟨Ls, Us, htail, hunique⟩
      refine ⟨higham13VaryingStepL A Ls, higham13VaryingStepU A Us,
        Higham13VaryingBlockLUFactSpec.step A hdet htail, ?_⟩
      intro L U hLU
      exact Higham13VaryingBlockLUFactSpec.eq_step_of_tail_unique
        A hdet htail hunique hLU

/-- With a nonempty positive-order tail, uniqueness forces the first pivot
block to be nonsingular.  A singular pivot would admit a nontrivial
block-preserving shear of the factors. -/
theorem Higham13VaryingBlockLUExistsUnique.first_block_det_ne_zero
    {r s : ℕ} {ss : List ℕ} (hs : 0 < s)
    (A : Matrix (Higham13VaryingBlockIndex (r :: s :: ss))
      (Higham13VaryingBlockIndex (r :: s :: ss)) ℝ)
    (hExistsUnique : Higham13VaryingBlockLUExistsUnique (r :: s :: ss) A) :
    Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0 := by
  classical
  by_contra hdet
  have hdet0 : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ = 0 := hdet
  rcases hExistsUnique with ⟨L, U, hLU, hunique⟩
  let Ab := higham13VaryingToBlocks A
  let Lb := higham13VaryingToBlocks L
  let Ub := higham13VaryingToBlocks U
  have hLshape : Lb.toBlocks₁₁ = 1 ∧ Lb.toBlocks₁₂ = 0 ∧
      Higham13VaryingBlockUnitLower (s :: ss) Lb.toBlocks₂₂ := by
    simpa only [Higham13VaryingBlockUnitLower] using hLU.lower
  have hUshape : Ub.toBlocks₂₁ = 0 ∧
      Higham13VaryingBlockUpper (s :: ss) Ub.toBlocks₂₂ := by
    simpa only [Higham13VaryingBlockUpper] using hLU.upper
  have hblocks := higham13VaryingProductBlocks
    (r := r) (n := List.foldr (fun r n => r + n) 0 (s :: ss))
    hLU.product_eq
  change
    Lb.toBlocks₁₁ * Ub.toBlocks₁₁ + Lb.toBlocks₁₂ * Ub.toBlocks₂₁ =
          Ab.toBlocks₁₁ ∧
      Lb.toBlocks₁₁ * Ub.toBlocks₁₂ + Lb.toBlocks₁₂ * Ub.toBlocks₂₂ =
          Ab.toBlocks₁₂ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₁ + Lb.toBlocks₂₂ * Ub.toBlocks₂₁ =
          Ab.toBlocks₂₁ ∧
      Lb.toBlocks₂₁ * Ub.toBlocks₁₂ + Lb.toBlocks₂₂ * Ub.toBlocks₂₂ =
          Ab.toBlocks₂₂ at hblocks
  have hU11 : Ub.toBlocks₁₁ = Ab.toBlocks₁₁ := by
    have h := hblocks.1
    rw [hLshape.1, hLshape.2.1, hUshape.1] at h
    simpa only [Matrix.one_mul, Matrix.zero_mul, add_zero] using h
  have hU12 : Ub.toBlocks₁₂ = Ab.toBlocks₁₂ := by
    have h := hblocks.2.1
    rw [hLshape.1, hLshape.2.1] at h
    simpa only [Matrix.one_mul, Matrix.zero_mul, add_zero] using h
  have hA21 : Lb.toBlocks₂₁ * Ub.toBlocks₁₁ = Ab.toBlocks₂₁ := by
    have h := hblocks.2.2.1
    rw [hUshape.1] at h
    simpa only [Matrix.mul_zero, add_zero] using h
  have hA22 : Lb.toBlocks₂₁ * Ub.toBlocks₁₂ +
      Lb.toBlocks₂₂ * Ub.toBlocks₂₂ = Ab.toBlocks₂₂ := hblocks.2.2.2
  rcases (Matrix.exists_vecMul_eq_zero_iff
      (M := Ab.toBlocks₁₁)).2 hdet0 with ⟨v, hvne, hvker⟩
  let X : Matrix
      (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) (Fin r) ℝ :=
    fun i j => if i.val = 0 then v j else 0
  have hXker : X * Ab.toBlocks₁₁ = 0 := by
    ext i j
    by_cases hi : i.val = 0
    · have hvrow := congr_fun hvker j
      change ∑ q : Fin r, X i q * Ab.toBlocks₁₁ q j = 0
      simpa [X, hi, Matrix.vecMul, dotProduct] using hvrow
    · change ∑ q : Fin r, X i q * Ab.toBlocks₁₁ q j = 0
      simp [X, hi]
  have hXU11 : X * Ub.toBlocks₁₁ = 0 := by
    rw [hU11, hXker]
  have hXrows : ∀ i : Fin
      (List.foldr (fun r n => r + n) 0 (s :: ss)),
      s ≤ i.val → ∀ j : Fin r, X i j = 0 := by
    intro i hi j
    have hi0 : i.val ≠ 0 := by omega
    simp [X, hi0]
  let Lalt := higham13VaryingFromBlocks
    (1 : Matrix (Fin r) (Fin r) ℝ)
    (0 : Matrix (Fin r)
      (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) ℝ)
    (Lb.toBlocks₂₁ + Lb.toBlocks₂₂ * X) Lb.toBlocks₂₂
  let Ualt := higham13VaryingFromBlocks Ub.toBlocks₁₁ Ub.toBlocks₁₂
    (0 : Matrix
      (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) (Fin r) ℝ)
    (Ub.toBlocks₂₂ - X * Ub.toBlocks₁₂)
  have hLaltBlocks : higham13VaryingToBlocks Lalt = Matrix.fromBlocks
      (1 : Matrix (Fin r) (Fin r) ℝ)
      (0 : Matrix (Fin r)
        (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) ℝ)
      (Lb.toBlocks₂₁ + Lb.toBlocks₂₂ * X) Lb.toBlocks₂₂ := by
    simp [Lalt]
  have hUaltBlocks : higham13VaryingToBlocks Ualt = Matrix.fromBlocks
      Ub.toBlocks₁₁ Ub.toBlocks₁₂
      (0 : Matrix
        (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) (Fin r) ℝ)
      (Ub.toBlocks₂₂ - X * Ub.toBlocks₁₂) := by
    simp [Ualt]
  have hAltProduct : Lalt * Ualt = A := by
    apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
    change higham13VaryingToBlocks (Lalt * Ualt) = Ab
    rw [show higham13VaryingToBlocks (Lalt * Ualt) =
        higham13VaryingToBlocks Lalt * higham13VaryingToBlocks Ualt by
      simpa only using higham13VaryingToBlocks_mul
        (r := r) (n := List.foldr (fun r n => r + n) 0 (s :: ss)) Lalt Ualt]
    rw [hLaltBlocks, hUaltBlocks, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_toBlocks Ab, Matrix.fromBlocks_inj]
    constructor
    · have hz : (0 : Matrix (Fin r)
          (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) ℝ) *
          (0 : Matrix
            (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) (Fin r) ℝ) = 0 :=
        Matrix.zero_mul _
      calc
        1 * Ub.toBlocks₁₁ + 0 * 0 = Ub.toBlocks₁₁ + 0 :=
          congrArg₂ (· + ·) (Matrix.one_mul _) hz
        _ = Ub.toBlocks₁₁ := add_zero _
        _ = Ab.toBlocks₁₁ := hU11
    constructor
    · have hz : (0 : Matrix (Fin r)
          (Fin (List.foldr (fun r n => r + n) 0 (s :: ss))) ℝ) *
          (Ub.toBlocks₂₂ - X * Ub.toBlocks₁₂) = 0 := Matrix.zero_mul _
      calc
        1 * Ub.toBlocks₁₂ +
            0 * (Ub.toBlocks₂₂ - X * Ub.toBlocks₁₂) =
          Ub.toBlocks₁₂ + 0 := congrArg₂ (· + ·) (Matrix.one_mul _) hz
        _ = Ub.toBlocks₁₂ := add_zero _
        _ = Ab.toBlocks₁₂ := hU12
    constructor
    · calc
        (Lb.toBlocks₂₁ + Lb.toBlocks₂₂ * X) * Ub.toBlocks₁₁ +
              Lb.toBlocks₂₂ *
                (0 : Matrix
                  (Fin (List.foldr (fun r n => r + n) 0 (s :: ss)))
                  (Fin r) ℝ) =
            Lb.toBlocks₂₁ * Ub.toBlocks₁₁ +
              Lb.toBlocks₂₂ * (X * Ub.toBlocks₁₁) := by
                rw [Matrix.mul_zero, add_zero, Matrix.add_mul,
                  Matrix.mul_assoc]
        _ = Lb.toBlocks₂₁ * Ub.toBlocks₁₁ := by
          rw [hXU11, Matrix.mul_zero, add_zero]
        _ = Ab.toBlocks₂₁ := hA21
    · calc
        (Lb.toBlocks₂₁ + Lb.toBlocks₂₂ * X) * Ub.toBlocks₁₂ +
              Lb.toBlocks₂₂ * (Ub.toBlocks₂₂ - X * Ub.toBlocks₁₂) =
            Lb.toBlocks₂₁ * Ub.toBlocks₁₂ +
              Lb.toBlocks₂₂ * Ub.toBlocks₂₂ := by
                rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
                abel
        _ = Ab.toBlocks₂₂ := hA22
  have hAlt : Higham13VaryingBlockLUFactSpec (r :: s :: ss) A Lalt Ualt := by
    refine ⟨?_, ?_, hAltProduct⟩
    · change (higham13VaryingToBlocks Lalt).toBlocks₁₁ = 1 ∧
        (higham13VaryingToBlocks Lalt).toBlocks₁₂ = 0 ∧
          Higham13VaryingBlockUnitLower (s :: ss)
            (higham13VaryingToBlocks Lalt).toBlocks₂₂
      rw [hLaltBlocks]
      simpa using hLshape.2.2
    · have hUpdated : Higham13VaryingBlockUpper (s :: ss)
          (Ub.toBlocks₂₂ - X * Ub.toBlocks₁₂) :=
        higham13VaryingBlockUpper_sub_mul_of_rows_zero
          hUshape.2 X Ub.toBlocks₁₂ hXrows
      change (higham13VaryingToBlocks Ualt).toBlocks₂₁ = 0 ∧
        Higham13VaryingBlockUpper (s :: ss)
          (higham13VaryingToBlocks Ualt).toBlocks₂₂
      rw [hUaltBlocks]
      simpa using hUpdated
  have hEq : Lalt = L := (hunique Lalt Ualt hAlt).1
  have hvcoord : ∃ j : Fin r, v j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hvne
    funext j
    exact h j
  rcases hvcoord with ⟨j0, hvj0⟩
  let i0 : Fin (List.foldr (fun r n => r + n) 0 (s :: ss)) :=
    Fin.castAdd (List.foldr (fun r n => r + n) 0 ss) ⟨0, hs⟩
  have htailLshape :
      (higham13VaryingToBlocks Lb.toBlocks₂₂).toBlocks₁₁ = 1 := by
    have h := hLshape.2.2
    simp only [Higham13VaryingBlockUnitLower] at h
    exact h.1
  have hdiag : Lb.toBlocks₂₂ i0 i0 = 1 := by
    have hentry := congr_fun (congr_fun htailLshape
      (⟨0, hs⟩ : Fin s)) (⟨0, hs⟩ : Fin s)
    simpa [i0, Matrix.one_apply] using hentry
  have hmulEntry : (Lb.toBlocks₂₂ * X) i0 j0 = v j0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i0]
    · change Lb.toBlocks₂₂ i0 i0 * v j0 = v j0
      rw [hdiag, one_mul]
    · intro k _hk hk
      have hk0 : k.val ≠ 0 := by
        intro hval
        apply hk
        apply Fin.ext
        simpa [i0] using hval
      simp [X, hk0]
    · intro hnot
      exact (hnot (Finset.mem_univ i0)).elim
  have hblocksEq := congrArg higham13VaryingToBlocks hEq
  have h21eq : Lb.toBlocks₂₁ + Lb.toBlocks₂₂ * X = Lb.toBlocks₂₁ := by
    calc
      _ = (higham13VaryingToBlocks Lalt).toBlocks₂₁ := by
        rw [hLaltBlocks]
        rfl
      _ = Lb.toBlocks₂₁ := congrArg Matrix.toBlocks₂₁ hblocksEq
  have hzero : Lb.toBlocks₂₂ * X = 0 := by
    apply add_left_cancel (a := Lb.toBlocks₂₁)
    exact h21eq.trans (add_zero _).symm
  have hentryZero := congr_fun (congr_fun hzero i0) j0
  rw [hmulEntry] at hentryZero
  exact hvj0 hentryZero

/-- Full uniqueness descends to uniqueness of the unequal-order Schur tail
once the first pivot has been shown nonsingular. -/
theorem Higham13VaryingBlockLUExistsUnique.schurTail_of_det
    {r : ℕ} {rs : List ℕ}
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    (hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0)
    (hExistsUnique : Higham13VaryingBlockLUExistsUnique (r :: rs) A) :
    Higham13VaryingBlockLUExistsUnique rs (higham13VaryingSchur A) := by
  rcases hExistsUnique with ⟨L, U, hLU, hunique⟩
  let Ls := (higham13VaryingToBlocks L).toBlocks₂₂
  let Us := (higham13VaryingToBlocks U).toBlocks₂₂
  have htail : Higham13VaryingBlockLUFactSpec rs
      (higham13VaryingSchur A) Ls Us :=
    Higham13VaryingBlockLUFactSpec.schurTail_of_det hLU hdet
  refine ⟨Ls, Us, htail, ?_⟩
  intro L' U' htail'
  have hfull' : Higham13VaryingBlockLUFactSpec (r :: rs) A
      (higham13VaryingStepL A L') (higham13VaryingStepU A U') :=
    Higham13VaryingBlockLUFactSpec.step A hdet htail'
  rcases hunique (higham13VaryingStepL A L')
      (higham13VaryingStepU A U') hfull' with ⟨hL, hU⟩
  constructor
  · have hb := congrArg higham13VaryingToBlocks hL
    have h22 := congrArg Matrix.toBlocks₂₂ hb
    rw [show higham13VaryingToBlocks (higham13VaryingStepL A L') =
        Matrix.fromBlocks
          (1 : Matrix (Fin r) (Fin r) ℝ)
          (0 : Matrix (Fin r)
            (Fin (List.foldr (fun r n => r + n) 0 rs)) ℝ)
          ((higham13VaryingToBlocks A).toBlocks₂₁ *
            (higham13VaryingToBlocks A).toBlocks₁₁⁻¹) L' by
      simp [higham13VaryingStepL]] at h22
    simpa [Ls] using h22
  · have hb := congrArg higham13VaryingToBlocks hU
    have h22 := congrArg Matrix.toBlocks₂₂ hb
    rw [show higham13VaryingToBlocks (higham13VaryingStepU A U') =
        Matrix.fromBlocks
          (higham13VaryingToBlocks A).toBlocks₁₁
          (higham13VaryingToBlocks A).toBlocks₁₂
          (0 : Matrix
            (Fin (List.foldr (fun r n => r + n) 0 rs)) (Fin r) ℝ) U' by
      simp [higham13VaryingStepU]] at h22
    simpa [Us] using h22

/-- Converse direction of Higham's Theorem 13.2 for unequal positive block
orders. -/
theorem Higham13VaryingLeadingPrincipalNonsingular.of_existsUnique
    (r : ℕ) (rs : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    (hpos : Higham13PositiveBlockOrders (r :: rs))
    (hExistsUnique : Higham13VaryingBlockLUExistsUnique (r :: rs) A) :
    Higham13VaryingLeadingPrincipalNonsingular (r :: rs) A := by
  induction rs generalizing r with
  | nil =>
      intro k hkpos hklt
      simp at hklt
      omega
  | cons s ss ih =>
      have hs : 0 < s := hpos s (by simp)
      have hdet : Matrix.det (higham13VaryingToBlocks A).toBlocks₁₁ ≠ 0 :=
        Higham13VaryingBlockLUExistsUnique.first_block_det_ne_zero
          hs A hExistsUnique
      have htailExistsUnique : Higham13VaryingBlockLUExistsUnique (s :: ss)
          (higham13VaryingSchur A) :=
        Higham13VaryingBlockLUExistsUnique.schurTail_of_det
          A hdet hExistsUnique
      have htailPos : Higham13PositiveBlockOrders (s :: ss) := by
        intro q hq
        exact hpos q (by simp [hq])
      have htailLead : Higham13VaryingLeadingPrincipalNonsingular (s :: ss)
          (higham13VaryingSchur A) :=
        ih s (higham13VaryingSchur A) htailPos htailExistsUnique
      exact Higham13VaryingLeadingPrincipalNonsingular.of_det_of_schur
        hdet htailLead

/-- Higham, 2nd ed., Chapter 13, Theorem 13.2 in its source-strength form:
for a partition into possibly unequal positive block orders, the exact block
LU factorization exists uniquely iff every nonempty proper cumulative leading
principal block submatrix is nonsingular. -/
theorem higham13_varyingBlockLU_existsUnique_iff_leadingPrincipalNonsingular
    (r : ℕ) (rs : List ℕ)
    (A : Matrix (Higham13VaryingBlockIndex (r :: rs))
      (Higham13VaryingBlockIndex (r :: rs)) ℝ)
    (hpos : Higham13PositiveBlockOrders (r :: rs)) :
    Higham13VaryingBlockLUExistsUnique (r :: rs) A ↔
      Higham13VaryingLeadingPrincipalNonsingular (r :: rs) A := by
  constructor
  · exact Higham13VaryingLeadingPrincipalNonsingular.of_existsUnique
      r rs A hpos
  · exact Higham13VaryingBlockLUExistsUnique.of_leadingPrincipalNonsingular
      r rs A

end

end NumStability
