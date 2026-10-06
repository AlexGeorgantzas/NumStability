import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push

/-!
# Chapter 13 block LU with unequal block dimensions

Higham's Theorem 13.2 permits the diagonal blocks to have different positive
orders.  This module gives a global-matrix model for such a partition: a list
`dims = [r₀, ..., rₘ₋₁]` produces the scalar index `Fin (r₀ + ... + rₘ₋₁)`.
The recursive lower/upper shape predicates split at each cumulative block
boundary and express unit block-lower and block-upper triangularity without
imposing a common block order.
-/

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


end

end NumStability
