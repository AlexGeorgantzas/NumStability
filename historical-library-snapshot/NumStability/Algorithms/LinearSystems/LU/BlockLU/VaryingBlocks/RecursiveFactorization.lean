import NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.SchurComplement

/-!
# Recursive unequal-block LU factorization

Recursive construction and reconstruction results for varying block orders.
-/

namespace NumStability

open scoped BigOperators Matrix

noncomputable section

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


end

end NumStability
