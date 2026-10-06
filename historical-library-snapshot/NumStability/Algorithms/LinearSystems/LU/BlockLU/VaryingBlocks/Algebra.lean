import NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Basic

/-!
# Algebra for unequal-block LU

Reindexing and block-multiplication identities used by the unequal-order
factorization API.
-/

namespace NumStability

open scoped BigOperators Matrix

noncomputable section

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


end

end NumStability
