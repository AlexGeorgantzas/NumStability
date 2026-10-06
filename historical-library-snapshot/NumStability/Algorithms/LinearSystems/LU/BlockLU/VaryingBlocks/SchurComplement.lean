import NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Algebra

/-!
# Schur complements for unequal-block LU

First-block Schur-complement identities for partitions with varying block
orders.
-/

namespace NumStability

open scoped BigOperators Matrix

noncomputable section

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


end

end NumStability
