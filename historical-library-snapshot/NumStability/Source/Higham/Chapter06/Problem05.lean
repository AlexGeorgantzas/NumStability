-- Source/Higham/Chapter06/Problem05.lean
--
-- Higham Chapter 6, Problem 6.5 source-facing theorem package.

import NumStability.Analysis.MatrixNorms.UnitarilyInvariant

/-!
# Higham Chapter 6, Problem 6.5

Formalizes Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Problem 6.5: its Frobenius/operator product inequality and unitarily invariant
norm argument built from monomial unitary matrices.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Higham Problem 6.5, complex Frobenius/operator-2 product inequality:
    `||ABC||_F <= ||A||_2 ||B||_F ||C||_2`. -/
theorem highamProblem65_complexFrobenius_triple_mul_le
    {m n p q : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) (C : CMatrix p q) :
    complexMatrixFrobenius (complexMatrixMul (complexMatrixMul A B) C) <=
      complexMatrixOp2 A * complexMatrixFrobenius B * complexMatrixOp2 C := by
  have hright :=
    complexMatrixFrobenius_mul_le_mul_op2 (complexMatrixMul A B) C
  have hleft := complexMatrixFrobenius_mul_le_op2_mul A B
  calc
    complexMatrixFrobenius (complexMatrixMul (complexMatrixMul A B) C)
        <= complexMatrixFrobenius (complexMatrixMul A B) * complexMatrixOp2 C := hright
    _ <= (complexMatrixOp2 A * complexMatrixFrobenius B) * complexMatrixOp2 C :=
        mul_le_mul_of_nonneg_right hleft (complexMatrixOp2_nonneg C)
    _ = complexMatrixOp2 A * complexMatrixFrobenius B * complexMatrixOp2 C := by ring

/-- Positive scalar phase used in the square-contraction midpoint route for
    Higham Problem 6.5. If `0 <= s <= 1`, then this complex number is unitary
    and its real midpoint with the negative phase is `s`. -/
noncomputable def highamProblem65PhasePlus (s : ℝ) : ℂ :=
  (s : ℂ) + Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ)

/-- Negative scalar phase paired with `highamProblem65PhasePlus`. -/
noncomputable def highamProblem65PhaseMinus (s : ℝ) : ℂ :=
  (s : ℂ) - Complex.I * (Real.sqrt (1 - s ^ 2) : ℂ)

theorem highamProblem65_phase_midpoint (s : ℝ) :
    (1 / 2 : ℂ) *
        (highamProblem65PhasePlus s + highamProblem65PhaseMinus s) =
      (s : ℂ) := by
  simp [highamProblem65PhasePlus, highamProblem65PhaseMinus]
  ring

theorem highamProblem65_phasePlus_normSq_eq_one
    {s : ℝ} (hs0 : 0 <= s) (hs1 : s <= 1) :
    Complex.normSq (highamProblem65PhasePlus s) = 1 := by
  have hs_sq_le_one : s ^ 2 <= 1 := by nlinarith
  have hrad : 0 <= 1 - s ^ 2 := sub_nonneg.mpr hs_sq_le_one
  calc
    Complex.normSq (highamProblem65PhasePlus s)
        = s ^ 2 + (Real.sqrt (1 - s ^ 2)) ^ 2 := by
          simp [highamProblem65PhasePlus, Complex.normSq_apply, pow_two]
    _ = 1 := by
          rw [Real.sq_sqrt hrad]
          ring

theorem highamProblem65_phaseMinus_normSq_eq_one
    {s : ℝ} (hs0 : 0 <= s) (hs1 : s <= 1) :
    Complex.normSq (highamProblem65PhaseMinus s) = 1 := by
  have hs_sq_le_one : s ^ 2 <= 1 := by nlinarith
  have hrad : 0 <= 1 - s ^ 2 := sub_nonneg.mpr hs_sq_le_one
  calc
    Complex.normSq (highamProblem65PhaseMinus s)
        = s ^ 2 + (Real.sqrt (1 - s ^ 2)) ^ 2 := by
          simp [highamProblem65PhaseMinus, Complex.normSq_apply, pow_two]
    _ = 1 := by
          rw [Real.sq_sqrt hrad]
          ring

theorem highamProblem65_phasePlus_star_mul_self
    {s : ℝ} (hs0 : 0 <= s) (hs1 : s <= 1) :
    star (highamProblem65PhasePlus s) * highamProblem65PhasePlus s = 1 := by
  have hnorm := highamProblem65_phasePlus_normSq_eq_one hs0 hs1
  have hstar :
      star (highamProblem65PhasePlus s) * highamProblem65PhasePlus s =
        (Complex.normSq (highamProblem65PhasePlus s) : ℂ) := by
    simpa using (Complex.normSq_eq_conj_mul_self
      (z := highamProblem65PhasePlus s)).symm
  rw [hstar, hnorm]
  norm_num

theorem highamProblem65_phaseMinus_star_mul_self
    {s : ℝ} (hs0 : 0 <= s) (hs1 : s <= 1) :
    star (highamProblem65PhaseMinus s) * highamProblem65PhaseMinus s = 1 := by
  have hnorm := highamProblem65_phaseMinus_normSq_eq_one hs0 hs1
  have hstar :
      star (highamProblem65PhaseMinus s) * highamProblem65PhaseMinus s =
        (Complex.normSq (highamProblem65PhaseMinus s) : ℂ) := by
    simpa using (Complex.normSq_eq_conj_mul_self
      (z := highamProblem65PhaseMinus s)).symm
  rw [hstar, hnorm]
  norm_num

/-- Monomial matrix with one possibly nonzero unit-modulus phase in each
    column, placed in row `q i`. This is the permutation-aware replacement for
    a literal diagonal phase matrix when the local SVD target basis uses an
    arbitrary left-basis extension. -/
noncomputable def highamProblem65MonomialMatrix
    {ι : Type*} [DecidableEq ι]
    (q : Equiv.Perm ι) (z : ι -> ℂ) : Matrix ι ι ℂ :=
  fun k i => if k = q i then z i else 0

theorem complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_of_perm
    {n : ℕ} (A : CMatrix n n)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin n, b k = complexMatrixLeftSingularVector A i)
    (q : Equiv.Perm (Fin n))
    (hq :
      ∀ i : {i : Fin n // complexMatrixSingularValue A i ≠ 0},
        q i.1 = complexMatrixLeftSingularVectorBasisIndex A b hcontains i) :
    complexMatrixSVDFinDiagonalCoordinateMatrix A b =
      highamProblem65MonomialMatrix q
        (fun i => (complexMatrixSingularValue A i : ℂ)) := by
  classical
  ext k i
  rw [complexMatrixSVDFinDiagonalCoordinateMatrix_apply]
  by_cases hσ : complexMatrixSingularValue A i = 0
  · rw [if_pos hσ]
    simp [highamProblem65MonomialMatrix, hσ]
  · rw [if_neg hσ]
    have hq_i := hq ⟨i, hσ⟩
    have hidx_apply :
        b (complexMatrixLeftSingularVectorBasisIndex A b hcontains ⟨i, hσ⟩) =
          complexMatrixLeftSingularVector A i :=
      complexMatrixLeftSingularVectorBasisIndex_apply A b hcontains ⟨i, hσ⟩
    by_cases hk : b k = complexMatrixLeftSingularVector A i
    · rw [if_pos hk]
      have hb_inj : Function.Injective b :=
        b.orthonormal.linearIndependent.injective
      have hk_idx :
          k = complexMatrixLeftSingularVectorBasisIndex A b hcontains ⟨i, hσ⟩ :=
        hb_inj (hk.trans hidx_apply.symm)
      have hkq : k = q i := hk_idx.trans hq_i.symm
      simp [highamProblem65MonomialMatrix, hkq]
    · rw [if_neg hk]
      have hkq : k ≠ q i := by
        intro hkq
        apply hk
        calc
          b k = b (complexMatrixLeftSingularVectorBasisIndex A b hcontains ⟨i, hσ⟩) := by
            rw [hkq, hq_i]
          _ = complexMatrixLeftSingularVector A i := hidx_apply
      simp [highamProblem65MonomialMatrix, hkq]

theorem complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_basisPerm
    {n : ℕ} (A : CMatrix n n)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin n, b k = complexMatrixLeftSingularVector A i) :
    complexMatrixSVDFinDiagonalCoordinateMatrix A b =
      highamProblem65MonomialMatrix
        (complexMatrixLeftSingularVectorBasisPerm A b hcontains)
        (fun i => (complexMatrixSingularValue A i : ℂ)) :=
  complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_of_perm
    A b hcontains (complexMatrixLeftSingularVectorBasisPerm A b hcontains)
    (fun i => complexMatrixLeftSingularVectorBasisPerm_apply_nonzero A b hcontains i)

theorem highamProblem65_star_mul_monomialMatrix_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Equiv.Perm ι) (z : ι -> ℂ) (i j : ι) :
    (star (highamProblem65MonomialMatrix q z) *
        highamProblem65MonomialMatrix q z) i j =
      if i = j then star (z i) * z i else 0 := by
  classical
  let M : Matrix ι ι ℂ := highamProblem65MonomialMatrix q z
  change (∑ k : ι, (star M) i k * M k j) =
    if i = j then star (z i) * z i else 0
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    calc
      (∑ k : ι, (star M) i k * M k i)
          = ∑ k : ι, if k = q i then star (z i) * z i else 0 := by
            apply Finset.sum_congr rfl
            intro k _hk
            by_cases hk : k = q i
            · simp [M, highamProblem65MonomialMatrix, hk]
            · simp [M, highamProblem65MonomialMatrix, hk]
      _ = star (z i) * z i := by simp
  · rw [if_neg hij]
    refine Finset.sum_eq_zero ?_
    intro k _hk
    have hqij : q i ≠ q j := fun h => hij (q.injective h)
    by_cases hki : k = q i
    · by_cases hkj : k = q j
      · have : i = j := q.injective (by rw [← hki, hkj])
        contradiction
      · simp [M, highamProblem65MonomialMatrix, hki, hqij]
    · simp [M, highamProblem65MonomialMatrix, hki]

theorem highamProblem65MonomialMatrix_mem_unitaryGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Equiv.Perm ι) (z : ι -> ℂ)
    (hz : ∀ i, star (z i) * z i = 1) :
    highamProblem65MonomialMatrix q z ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [highamProblem65_star_mul_monomialMatrix_apply]
  by_cases hij : i = j
  · subst j
    simpa using hz i
  · simp [hij]

theorem highamProblem65MonomialMatrix_midpoint
    {ι : Type*} [DecidableEq ι]
    (q : Equiv.Perm ι) (a b c : ι -> ℂ)
    (h : ∀ i, c i = (1 / 2 : ℂ) * (a i + b i)) :
    highamProblem65MonomialMatrix q c =
      ((1 / 2 : ℂ) •
        ((highamProblem65MonomialMatrix q a :
          Matrix ι ι ℂ) + highamProblem65MonomialMatrix q b)) := by
  ext k i
  by_cases hk : k = q i
  · simp [highamProblem65MonomialMatrix, hk, h i, mul_add]
  · simp [highamProblem65MonomialMatrix, hk]

theorem highamProblem65MonomialPhasePlus_mem_unitaryGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Equiv.Perm ι) (s : ι -> ℝ)
    (hs0 : ∀ i, 0 <= s i) (hs1 : ∀ i, s i <= 1) :
    highamProblem65MonomialMatrix q (fun i => highamProblem65PhasePlus (s i)) ∈
      Matrix.unitaryGroup ι ℂ :=
  highamProblem65MonomialMatrix_mem_unitaryGroup q
    (fun i => highamProblem65PhasePlus (s i))
    (fun i => highamProblem65_phasePlus_star_mul_self (hs0 i) (hs1 i))

theorem highamProblem65MonomialPhaseMinus_mem_unitaryGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Equiv.Perm ι) (s : ι -> ℝ)
    (hs0 : ∀ i, 0 <= s i) (hs1 : ∀ i, s i <= 1) :
    highamProblem65MonomialMatrix q (fun i => highamProblem65PhaseMinus (s i)) ∈
      Matrix.unitaryGroup ι ℂ :=
  highamProblem65MonomialMatrix_mem_unitaryGroup q
    (fun i => highamProblem65PhaseMinus (s i))
    (fun i => highamProblem65_phaseMinus_star_mul_self (hs0 i) (hs1 i))

theorem highamProblem65MonomialPhase_midpoint
    {ι : Type*} [DecidableEq ι]
    (q : Equiv.Perm ι) (s : ι -> ℝ) :
    highamProblem65MonomialMatrix q (fun i => (s i : ℂ)) =
      ((1 / 2 : ℂ) •
        ((highamProblem65MonomialMatrix q
            (fun i => highamProblem65PhasePlus (s i)) :
          Matrix ι ι ℂ) +
          highamProblem65MonomialMatrix q
            (fun i => highamProblem65PhaseMinus (s i)))) :=
  highamProblem65MonomialMatrix_midpoint q
    (fun i => highamProblem65PhasePlus (s i))
    (fun i => highamProblem65PhaseMinus (s i))
    (fun i => (s i : ℂ))
    (fun i => (highamProblem65_phase_midpoint (s i)).symm)

theorem highamProblem65_sandwich_monomialPhase_midpoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (q : Equiv.Perm ι) (s : ι -> ℝ) :
    A * highamProblem65MonomialMatrix q (fun i => (s i : ℂ)) * B =
      ((1 / 2 : ℂ) •
        (A * highamProblem65MonomialMatrix q
            (fun i => highamProblem65PhasePlus (s i)) * B +
          A * highamProblem65MonomialMatrix q
            (fun i => highamProblem65PhaseMinus (s i)) * B)) := by
  rw [highamProblem65MonomialPhase_midpoint q s]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_add, Matrix.add_mul]

theorem highamProblem65_svdMonomial_midpoint
    {n : ℕ} (L : CMatrix n n)
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (Sigma : Matrix (Fin n) (Fin n) ℂ)
    (q : Equiv.Perm (Fin n)) (s : Fin n -> ℝ)
    (hSigma :
      Sigma = highamProblem65MonomialMatrix q (fun i => (s i : ℂ)))
    (hs0 : ∀ i, 0 <= s i) (hs1 : ∀ i, s i <= 1)
    (hfact :
      (U : Matrix (Fin n) (Fin n) ℂ) * Sigma *
          star (V : Matrix (Fin n) (Fin n) ℂ) =
        (L : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ Wp Wm : Matrix.unitaryGroup (Fin n) ℂ,
      L = fun i j =>
        (1 / 2 : ℂ) *
          ((Wp : Matrix (Fin n) (Fin n) ℂ) i j +
            (Wm : Matrix (Fin n) (Fin n) ℂ) i j) := by
  let Zp : Matrix.unitaryGroup (Fin n) ℂ :=
    ⟨highamProblem65MonomialMatrix q
        (fun i => highamProblem65PhasePlus (s i)),
      highamProblem65MonomialPhasePlus_mem_unitaryGroup q s hs0 hs1⟩
  let Zm : Matrix.unitaryGroup (Fin n) ℂ :=
    ⟨highamProblem65MonomialMatrix q
        (fun i => highamProblem65PhaseMinus (s i)),
      highamProblem65MonomialPhaseMinus_mem_unitaryGroup q s hs0 hs1⟩
  let Wp : Matrix.unitaryGroup (Fin n) ℂ := U * Zp * star V
  let Wm : Matrix.unitaryGroup (Fin n) ℂ := U * Zm * star V
  refine ⟨Wp, Wm, ?_⟩
  have hmat :
      (L : Matrix (Fin n) (Fin n) ℂ) =
        ((1 / 2 : ℂ) •
          ((Wp : Matrix (Fin n) (Fin n) ℂ) +
            (Wm : Matrix (Fin n) (Fin n) ℂ))) := by
    calc
      (L : Matrix (Fin n) (Fin n) ℂ)
          = (U : Matrix (Fin n) (Fin n) ℂ) * Sigma *
              star (V : Matrix (Fin n) (Fin n) ℂ) := hfact.symm
      _ = (U : Matrix (Fin n) (Fin n) ℂ) *
            highamProblem65MonomialMatrix q (fun i => (s i : ℂ)) *
              star (V : Matrix (Fin n) (Fin n) ℂ) := by
            rw [hSigma]
      _ = ((1 / 2 : ℂ) •
          ((U : Matrix (Fin n) (Fin n) ℂ) *
              highamProblem65MonomialMatrix q
                (fun i => highamProblem65PhasePlus (s i)) *
                star (V : Matrix (Fin n) (Fin n) ℂ) +
            (U : Matrix (Fin n) (Fin n) ℂ) *
              highamProblem65MonomialMatrix q
                (fun i => highamProblem65PhaseMinus (s i)) *
                star (V : Matrix (Fin n) (Fin n) ℂ))) :=
            highamProblem65_sandwich_monomialPhase_midpoint
              (U : Matrix (Fin n) (Fin n) ℂ)
              (star (V : Matrix (Fin n) (Fin n) ℂ)) q s
      _ = ((1 / 2 : ℂ) •
          ((Wp : Matrix (Fin n) (Fin n) ℂ) +
            (Wm : Matrix (Fin n) (Fin n) ℂ))) := by
            rfl
  ext i j
  simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hmat

theorem highamProblem65_svdBasisPerm_midpoint
    {n : ℕ} (L : CMatrix n n)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue L i ≠ 0 →
        ∃ k : Fin n, b k = complexMatrixLeftSingularVector L i)
    (q : Equiv.Perm (Fin n))
    (hq :
      ∀ i : {i : Fin n // complexMatrixSingularValue L i ≠ 0},
        q i.1 = complexMatrixLeftSingularVectorBasisIndex L b hcontains i)
    (hL : complexMatrixOp2 L <= 1) :
    ∃ Wp Wm : Matrix.unitaryGroup (Fin n) ℂ,
      L = fun i j =>
        (1 / 2 : ℂ) *
          ((Wp : Matrix (Fin n) (Fin n) ℂ) i j +
            (Wm : Matrix (Fin n) (Fin n) ℂ) i j) :=
  highamProblem65_svdMonomial_midpoint L
    (complexMatrixSVDLeftUnitary b) (complexMatrixSVDRightUnitary L)
    (complexMatrixSVDFinDiagonalCoordinateMatrix L b) q
    (fun i => complexMatrixSingularValue L i)
    (complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_of_perm
      L b hcontains q hq)
    (fun i => complexMatrixSingularValue_nonneg L i)
    (fun i => (complexMatrixSingularValue_le_complexMatrixOp2 L i).trans hL)
    (complexMatrixSVDUnitary_diagonal_eq L b hcontains)

theorem highamProblem65_svdBasis_midpoint
    {n : ℕ} (L : CMatrix n n)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue L i ≠ 0 →
        ∃ k : Fin n, b k = complexMatrixLeftSingularVector L i)
    (hL : complexMatrixOp2 L <= 1) :
    ∃ Wp Wm : Matrix.unitaryGroup (Fin n) ℂ,
      L = fun i j =>
        (1 / 2 : ℂ) *
          ((Wp : Matrix (Fin n) (Fin n) ℂ) i j +
            (Wm : Matrix (Fin n) (Fin n) ℂ) i j) :=
  highamProblem65_svdBasisPerm_midpoint L b hcontains
    (complexMatrixLeftSingularVectorBasisPerm L b hcontains)
    (fun i => complexMatrixLeftSingularVectorBasisPerm_apply_nonzero L b hcontains i)
    hL

theorem highamProblem65_complexSquareContractionMidpointProperty (n : ℕ) :
    ComplexSquareContractionMidpointProperty n := by
  intro L hL
  obtain ⟨b, hcontains⟩ :=
    exists_complexMatrixLeftSingularVector_fin_orthonormalBasis_extension L
  exact highamProblem65_svdBasis_midpoint L b hcontains hL

/-- A bare fixed-shape unitarily invariant norm is a fixed-shape
    operator-ideal norm, using the checked SVD midpoint theorem above. -/
noncomputable def ComplexMatrixFixedUnitaryInvariantNorm.toOperatorIdealNormOfSVD
    {m n : ℕ} (ξ : ComplexMatrixFixedUnitaryInvariantNorm m n) :
    ComplexMatrixFixedOperatorIdealNorm m n :=
  ξ.toOperatorIdealNorm
    (highamProblem65_complexSquareContractionMidpointProperty m)
    (highamProblem65_complexSquareContractionMidpointProperty n)

/-- Higham Problem 6.5 in the fixed-shape operator-ideal API:
    `|||A B C||| <= ||A||_2 |||B||| ||C||_2` for
    `A : m x m`, `B : m x n`, and `C : n x n`. -/
theorem highamProblem65_fixedOperatorIdealNorm_triple_mul_le
    {m n : ℕ} (xi : ComplexMatrixFixedOperatorIdealNorm m n)
    (A : CMatrix m m) (B : CMatrix m n) (C : CMatrix n n) :
    xi.norm (complexMatrixMul (complexMatrixMul A B) C) <=
      complexMatrixOp2 A * xi.norm B * complexMatrixOp2 C := by
  have hright :
      xi.norm (complexMatrixMul (complexMatrixMul A B) C) <=
        xi.norm (complexMatrixMul A B) * complexMatrixOp2 C :=
    xi.right_mul_le (complexMatrixMul A B) C
  have hleft :
      xi.norm (complexMatrixMul A B) <= complexMatrixOp2 A * xi.norm B :=
    xi.left_mul_le A B
  calc
    xi.norm (complexMatrixMul (complexMatrixMul A B) C)
        <= xi.norm (complexMatrixMul A B) * complexMatrixOp2 C := hright
    _ <= (complexMatrixOp2 A * xi.norm B) * complexMatrixOp2 C :=
        mul_le_mul_of_nonneg_right hleft (complexMatrixOp2_nonneg C)
    _ = complexMatrixOp2 A * xi.norm B * complexMatrixOp2 C := by ring

/-- Higham Problem 6.5 for a bare fixed-shape unitarily invariant norm:
    `|||A B C||| <= ||A||_2 |||B||| ||C||_2`. -/
theorem highamProblem65_fixedUnitaryInvariantNorm_triple_mul_le
    {m n : ℕ} (ξ : ComplexMatrixFixedUnitaryInvariantNorm m n)
    (A : CMatrix m m) (B : CMatrix m n) (C : CMatrix n n) :
    ξ.norm (complexMatrixMul (complexMatrixMul A B) C) <=
      complexMatrixOp2 A * ξ.norm B * complexMatrixOp2 C :=
  highamProblem65_fixedOperatorIdealNorm_triple_mul_le
    (ξ.toOperatorIdealNormOfSVD) A B C

/-- Higham Problem 6.5 in the explicit shape-changing operator-ideal
    norm-family API:
    `|||ABC||| <= ||A||_2 |||B||| ||C||_2`.

    For a bare fixed-shape unitarily invariant norm, use the fixed-shape API
    above. For a dimension-uniform family, the missing mathematical foundation
    is a padding-coherence theorem plus the fixed-shape contraction argument. -/
theorem highamProblem65_operatorIdealNorm_triple_mul_le
    (ξ : ComplexMatrixOperatorIdealNormFamily) {m n p q : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) (C : CMatrix p q) :
    ξ.norm (complexMatrixMul (complexMatrixMul A B) C) <=
      complexMatrixOp2 A * ξ.norm B * complexMatrixOp2 C := by
  have hright :
      ξ.norm (complexMatrixMul (complexMatrixMul A B) C) <=
        ξ.norm (complexMatrixMul A B) * complexMatrixOp2 C :=
    ξ.right_mul_le (complexMatrixMul A B) C
  have hleft :
      ξ.norm (complexMatrixMul A B) <= complexMatrixOp2 A * ξ.norm B :=
    ξ.left_mul_le A B
  calc
    ξ.norm (complexMatrixMul (complexMatrixMul A B) C)
        <= ξ.norm (complexMatrixMul A B) * complexMatrixOp2 C := hright
    _ <= (complexMatrixOp2 A * ξ.norm B) * complexMatrixOp2 C :=
        mul_le_mul_of_nonneg_right hleft (complexMatrixOp2_nonneg C)
    _ = complexMatrixOp2 A * ξ.norm B * complexMatrixOp2 C := by ring
end NumStability
