import NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.RecursiveFactorization

/-!
# Uniqueness of unequal-block LU factorization

Existence and uniqueness criteria for the reusable varying-block LU model.
-/

namespace NumStability

open scoped BigOperators Matrix

noncomputable section

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
