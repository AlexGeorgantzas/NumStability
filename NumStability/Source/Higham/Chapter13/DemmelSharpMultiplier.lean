/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.LU.BlockLUSPDSourceClosure

/-!
# Higham Chapter 13: Demmel's sharp SPD block-multiplier bound

Higham's notes after Lemma 13.9 state the attainable strengthening

`‖A₂₁ A₁₁⁻¹‖₂ ≤ (√κ₂(A) - 1 / √κ₂(A)) / 2`.

The proof below does not assume this estimate.  Its algebraic core starts
from an actual spectral interval `α I ≤ A ≤ β I`.  Positivity of
`(β I - A)(A - α I)` gives the energy inequality used to control the angle
between a coordinate subspace and its image under `A`.  The source-facing
wrapper obtains `α = ‖A⁻¹‖₂⁻¹` and `β = ‖A‖₂` from the repository's exact
operator norm and canonical inverse.
-/

namespace NumStability

open scoped MatrixOrder

set_option maxHeartbeats 1000000 in
private theorem higham13_rectOpNorm2_le_of_rectOpNorm2Le {m n : ℕ}
    (M : Fin m → Fin n → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hM : rectOpNorm2Le M c) :
    rectOpNorm2 M ≤ c := by
  unfold rectOpNorm2
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc ?_
  intro x
  let y : Fin n → ℝ := WithLp.ofLp x
  have hxnorm : ‖x‖ = vecNorm2 y := by
    unfold vecNorm2 vecNorm2Sq y
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hynorm :
      ‖((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
          ((M : Matrix (Fin m) (Fin n) ℝ))) x‖ =
        vecNorm2 (rectMatMulVec M y) := by
    unfold vecNorm2 vecNorm2Sq rectMatMulVec y
    rw [EuclideanSpace.norm_eq]
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs]
  calc
    ‖((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
          ((M : Matrix (Fin m) (Fin n) ℝ))) x‖
        = vecNorm2 (rectMatMulVec M y) := hynorm
    _ ≤ c * vecNorm2 y := hM y
    _ = c * ‖x‖ := by rw [hxnorm]

private theorem higham13_opNorm2_eq_of_orthogonal_eigenbasis_attained {n : ℕ}
    (M Q : RSqMat n) (d : Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (heig : ∀ k : Fin n,
      Matrix.mulVec M (fun i => Q i k) = d k • (fun i => Q i k))
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ k, |d k| ≤ L)
    (kmax : Fin n) (hkmax : |d kmax| = L) :
    opNorm2 M = L := by
  have hdiag :
      M = finiteMatMul Q
        (finiteMatMul (finiteDiagonal d) (matTranspose Q)) := by
    apply finiteMatrix_eq_orthogonal_diagonalization_of_eigenvector_columns hQ
    intro k
    simpa [finiteMatVec, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul] using heig k
  apply le_antisymm
  · exact opNorm2_le_of_isOrthogonal_diagonalization hdiag hQ hL hbound
  · let x : RVec n := fun i => Q i kmax
    have hx : vecNorm2 x = 1 := by
      simpa [x] using hQ.column_vecNorm2_eq_one kmax
    have hop := opNorm2Le_opNorm2 M x
    have hMx : matMulVec n M x = d kmax • x := by
      simpa [x, matMulVec, Matrix.mulVec, dotProduct] using heig kmax
    rw [hMx] at hop
    change vecNorm2 (fun i => d kmax * x i) ≤ opNorm2 M * vecNorm2 x at hop
    rw [vecNorm2_smul] at hop
    simp only [hx, mul_one] at hop
    simpa [hkmax] using hop

/-- Leading principal block in the source ordering used around Lemma 13.9. -/
noncomputable def higham13DemmelLeadingBlock {r s : ℕ}
    (A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
    (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))

/-- Lower-left block in the source ordering used around Lemma 13.9. -/
noncomputable def higham13DemmelLowerLeftBlock {r s : ℕ}
    (A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) :
    Matrix (Fin s) (Fin r) ℝ :=
  fun i j => A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
    (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))

/-- Trailing principal block in the source ordering used around Lemma 13.9. -/
noncomputable def higham13DemmelTrailingBlock {r s : ℕ}
    (A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  fun i j => A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
    (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))

private theorem higham13_demmel_energy_inequality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) (hA : IsSymmetricFiniteMatrix A)
    {α β : ℝ}
    (hLower : finiteLoewnerLe
      (fun i j : ι => α * finiteIdMatrix i j) A)
    (hUpper : finiteLoewnerLe A
      (fun i j : ι => β * finiteIdMatrix i j))
    (x : ι → ℝ) :
    finiteVecNorm2Sq (finiteMatVec A x) ≤
      (α + β) * finiteQuadraticForm A x -
        α * β * finiteVecNorm2Sq x := by
  let Am : Matrix ι ι ℝ := A
  let L : Matrix ι ι ℝ :=
    (fun i j => A i j - α * finiteIdMatrix i j)
  let U : Matrix ι ι ℝ :=
    (fun i j => β * finiteIdMatrix i j - A i j)
  have hScalarSym (c : ℝ) :
      IsSymmetricFiniteMatrix (fun i j : ι => c * finiteIdMatrix i j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · simp [finiteIdMatrix, hij, Ne.symm hij]
  have hL : Matrix.PosSemidef L := by
    simpa [L] using
      (finiteLoewnerLe.to_matrix_posSemidef_sub
        (fun i j : ι => α * finiteIdMatrix i j) A
        (hScalarSym α) hA hLower)
  have hU : Matrix.PosSemidef U := by
    simpa [U] using
      (finiteLoewnerLe.to_matrix_posSemidef_sub
        A (fun i j : ι => β * finiteIdMatrix i j)
        hA (hScalarSym β) hUpper)
  have hLexpr : L = Am - α • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [L, Am, finiteIdMatrix]
    · simp [L, Am, finiteIdMatrix, hij]
  have hUexpr : U = β • (1 : Matrix ι ι ℝ) - Am := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [U, Am, finiteIdMatrix]
    · simp [U, Am, finiteIdMatrix, hij]
  have hcomm : Commute U L := by
    rw [hLexpr, hUexpr]
    have hbA : Commute (β • (1 : Matrix ι ι ℝ)) Am :=
      (Commute.one_left Am).smul_left β
    have hUA : Commute (β • (1 : Matrix ι ι ℝ) - Am) Am :=
      hbA.sub_left (Commute.refl Am)
    have hUaI :
        Commute (β • (1 : Matrix ι ι ℝ) - Am)
          (α • (1 : Matrix ι ι ℝ)) :=
      (Commute.one_right (β • (1 : Matrix ι ι ℝ) - Am)).smul_right α
    exact hUA.sub_right hUaI
  have hUL : Matrix.PosSemidef (U * L) :=
    (Matrix.PosSemidef.commute_iff hU hL).mp hcomm
  have hpoly :
      U * L =
        (α + β) • Am - Am * Am - (α * β) • (1 : Matrix ι ι ℝ) := by
    rw [hLexpr, hUexpr]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  have hULfinite : finitePSD (fun i j => (U * L) i j) :=
    Matrix_posSemidef.to_finitePSD (fun i j => (U * L) i j) hUL
  have hx := hULfinite x
  have hfun :
      (fun i j => (U * L) i j) =
        (fun i j =>
          ((α + β) * A i j - finiteMatMul A A i j) -
            α * β * finiteIdMatrix i j) := by
    ext i j
    have hp := congrArg (fun M : Matrix ι ι ℝ => M i j) hpoly
    simpa [Am, finiteMatMul] using hp
  rw [hfun, finiteQuadraticForm_sub, finiteQuadraticForm_sub,
    finiteQuadraticForm_smul,
    finiteQuadraticForm_finiteMatMul_self_of_symmetric A hA,
    finiteQuadraticForm_smul_finiteIdMatrix] at hx
  linarith

/-- Demmel's sharp block-multiplier estimate in spectral-interval form.

This is the mathematical core of the Chapter 13 notes claim.  The hypotheses
`α I ≤ A ≤ β I` are genuine spectral information about the displayed block
matrix, not a multiplier-norm or target-bound assumption. -/
theorem higham13_demmel_sharp_multiplier_of_spectral_interval
    {r s : ℕ} [Nonempty (Fin r)]
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (A21 : Matrix (Fin s) (Fin r) ℝ)
    (A22 : Matrix (Fin s) (Fin s) ℝ)
    (A11inv : Matrix (Fin r) (Fin r) ℝ)
    {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hA11inv : IsRightInverse r A11 A11inv)
    (hSym : IsSymmetricFiniteMatrix
      (Matrix.fromBlocks A11 A21.transpose A21 A22))
    (hLower : finiteLoewnerLe
      (fun i j : Fin r ⊕ Fin s => α * finiteIdMatrix i j)
      (Matrix.fromBlocks A11 A21.transpose A21 A22))
    (hUpper : finiteLoewnerLe
      (Matrix.fromBlocks A11 A21.transpose A21 A22)
      (fun i j : Fin r ⊕ Fin s => β * finiteIdMatrix i j)) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      ((β - α) / (2 * Real.sqrt (α * β))) := by
  classical
  let A : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ :=
    Matrix.fromBlocks A11 A21.transpose A21 A22
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hαβpos : 0 < α * β := mul_pos hα hβ
  let C : ℝ := (β - α) / (2 * Real.sqrt (α * β))
  have hC : 0 ≤ C := by
    exact div_nonneg (sub_nonneg.mpr hαβ)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  intro x
  let z : Fin r → ℝ := matMulVec r A11inv x
  let w : Fin r ⊕ Fin s → ℝ := Sum.elim z (fun _ => 0)
  let y : Fin s → ℝ := rectMatMulVec A21 z
  have hA11z : Matrix.mulVec A11 z = x := by
    simpa [z, matMulVec, Matrix.mulVec, dotProduct] using
      (matMulVec_of_isRightInverse A11 A11inv hA11inv x)
  have hAw : finiteMatVec A w = Sum.elim x y := by
    rw [show finiteMatVec A w = Matrix.mulVec A w by rfl]
    rw [show A = Matrix.fromBlocks A11 A21.transpose A21 A22 by rfl,
      Matrix.fromBlocks_mulVec]
    ext i
    cases i with
    | inl i =>
        change
          (A11.mulVec z +
            A21.transpose.mulVec (0 : Fin s → ℝ)) i = x i
        rw [Pi.add_apply, hA11z,
          congrFun (Matrix.mulVec_zero A21.transpose) i]
        simp only [Pi.zero_apply, add_zero]
    | inr i =>
        simp [w, y, rectMatMulVec, Matrix.mulVec, dotProduct]
  let X2 : ℝ := vecNorm2Sq x
  let Z2 : ℝ := vecNorm2Sq z
  let Y2 : ℝ := vecNorm2Sq y
  let q : ℝ := ∑ i : Fin r, z i * x i
  have hWnorm : finiteVecNorm2Sq w = Z2 := by
    simp [w, Z2, finiteVecNorm2Sq, vecNorm2Sq, Fintype.sum_sum_type]
  have hAwnorm : finiteVecNorm2Sq (finiteMatVec A w) = X2 + Y2 := by
    rw [hAw]
    simp [X2, Y2, finiteVecNorm2Sq, vecNorm2Sq, Fintype.sum_sum_type]
  have hq : finiteQuadraticForm A w = q := by
    unfold finiteQuadraticForm
    rw [hAw]
    simp [w, q, Fintype.sum_sum_type]
  have henergy :=
    higham13_demmel_energy_inequality A hSym hLower hUpper w
  rw [hAwnorm, hq, hWnorm] at henergy
  have hcs : q ^ 2 ≤ Z2 * X2 := by
    simpa [q, Z2, X2, vecNorm2Sq] using
      (vecInnerProduct_sq_le z x)
  have hX2 : 0 ≤ X2 := vecNorm2Sq_nonneg x
  have hZ2 : 0 ≤ Z2 := vecNorm2Sq_nonneg z
  have hY2 : 0 ≤ Y2 := vecNorm2Sq_nonneg y
  have hqle : q ≤ Real.sqrt Z2 * Real.sqrt X2 := by
    have habs := abs_vecInnerProduct_le_vecNorm2_mul z x
    exact le_trans (le_abs_self q) (by simpa [q, Z2, X2, vecNorm2] using habs)
  have hsZ : (Real.sqrt Z2) ^ 2 = Z2 := Real.sq_sqrt hZ2
  have hsX : (Real.sqrt X2) ^ 2 = X2 := Real.sq_sqrt hX2
  have hscaled :
      4 * α * β * Y2 ≤ (β - α) ^ 2 * X2 := by
    have hcoef : 0 ≤ 4 * α * β := by positivity
    have hcoef' : 0 ≤ 4 * α * β * (α + β) := by positivity
    have henergyscaled := mul_le_mul_of_nonneg_left henergy hcoef
    have hqscaled := mul_le_mul_of_nonneg_left hqle hcoef'
    have hstep :
        4 * α * β * Y2 ≤
          4 * α * β * (α + β) * Real.sqrt Z2 * Real.sqrt X2 -
            4 * α ^ 2 * β ^ 2 * Z2 - 4 * α * β * X2 := by
      nlinarith
    have hsquare :
        0 ≤ ((α + β) * Real.sqrt X2 -
          2 * α * β * Real.sqrt Z2) ^ 2 := sq_nonneg _
    have hsquare_expand :
        ((α + β) * Real.sqrt X2 -
            2 * α * β * Real.sqrt Z2) ^ 2 =
          (α + β) ^ 2 * X2 + 4 * α ^ 2 * β ^ 2 * Z2 -
            4 * α * β * (α + β) * Real.sqrt Z2 * Real.sqrt X2 := by
      calc
        ((α + β) * Real.sqrt X2 -
            2 * α * β * Real.sqrt Z2) ^ 2 =
            (α + β) ^ 2 * (Real.sqrt X2) ^ 2 +
              4 * α ^ 2 * β ^ 2 * (Real.sqrt Z2) ^ 2 -
                4 * α * β * (α + β) * Real.sqrt Z2 * Real.sqrt X2 := by
                  ring
        _ = (α + β) ^ 2 * X2 + 4 * α ^ 2 * β ^ 2 * Z2 -
              4 * α * β * (α + β) * Real.sqrt Z2 * Real.sqrt X2 := by
                rw [hsX, hsZ]
    rw [hsquare_expand] at hsquare
    have hcross :
        4 * α * β * (α + β) * Real.sqrt Z2 * Real.sqrt X2 -
            4 * α ^ 2 * β ^ 2 * Z2 ≤
          (α + β) ^ 2 * X2 := by
      linarith
    calc
      4 * α * β * Y2
          ≤ 4 * α * β * (α + β) * Real.sqrt Z2 * Real.sqrt X2 -
              4 * α ^ 2 * β ^ 2 * Z2 - 4 * α * β * X2 := hstep
      _ ≤ (α + β) ^ 2 * X2 - 4 * α * β * X2 :=
        sub_le_sub_right hcross _
      _ = (β - α) ^ 2 * X2 := by ring
  have hC2 : C ^ 2 = (β - α) ^ 2 / (4 * α * β) := by
    dsimp [C]
    rw [div_pow]
    field_simp [Real.sqrt_ne_zero'.mpr hαβpos]
    rw [Real.sq_sqrt (by positivity : 0 ≤ β * α)]
    ring
  have hY2bound : Y2 ≤ C ^ 2 * X2 := by
    rw [hC2]
    have hden : 0 < 4 * α * β := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith
  calc
    vecNorm2 (rectMatMulVec (rectMatMul A21 A11inv) x)
        = vecNorm2 y := by
            apply congrArg vecNorm2
            rw [rectMatMulVec_rectMatMul]
            change rectMatMulVec A21 z = y
            rfl
    _ = Real.sqrt Y2 := rfl
    _ ≤ Real.sqrt (C ^ 2 * X2) := Real.sqrt_le_sqrt hY2bound
    _ = C * vecNorm2 x := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hC]
      rfl
    _ = ((β - α) / (2 * Real.sqrt (α * β))) * vecNorm2 x := rfl

/-- Higham, 2nd ed., Chapter 13 notes (Demmel's strengthened Lemma 13.9).

For an SPD matrix in the displayed `r`-by-`s` block ordering, this is the
exact source claim

`‖A₂₁ A₁₁⁻¹‖₂ ≤ (√κ₂(A) - 1/√κ₂(A))/2`.

Both norms in `κ₂` are the repository's exact Euclidean operator norms and
both inverses are canonical `nonsingInv`s.  No multiplier bound is assumed. -/
theorem higham13_notes_demmel_sharp_multiplier
    {r s : ℕ} [Nonempty (Fin r)]
    (A : Matrix (Fin (r + s)) (Fin (r + s)) ℝ)
    (hSPD : IsSymPosDef (r + s) A) :
    rectOpNorm2
        (rectMatMul (higham13DemmelLowerLeftBlock A)
          (nonsingInv r (higham13DemmelLeadingBlock A))) ≤
      (Real.sqrt (kappa2 A (nonsingInv (r + s) A)) -
          (Real.sqrt (kappa2 A (nonsingInv (r + s) A)))⁻¹) / 2 := by
  classical
  let e : (Fin r ⊕ Fin s) ≃ Fin (r + s) := finSumFinEquiv
  let A11 : Matrix (Fin r) (Fin r) ℝ := higham13DemmelLeadingBlock A
  let A21 : Matrix (Fin s) (Fin r) ℝ := higham13DemmelLowerLeftBlock A
  let A22 : Matrix (Fin s) (Fin s) ℝ := higham13DemmelTrailingBlock A
  let F : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ :=
    Matrix.fromBlocks A11 A21.transpose A21 A22
  let Ainv : Matrix (Fin (r + s)) (Fin (r + s)) ℝ :=
    nonsingInv (r + s) A
  let β : ℝ := opNorm2 A
  let c : ℝ := opNorm2 Ainv
  let α : ℝ := c⁻¹
  have hRight : IsRightInverse (r + s) A Ainv := by
    exact isRightInverse_nonsingInv_of_isSymPosDef A hSPD
  let i0 : Fin r := Classical.choice (inferInstance : Nonempty (Fin r))
  let j0 : Fin (r + s) := e (Sum.inl i0)
  letI : Nonempty (Fin (r + s)) := ⟨j0⟩
  have hc : 0 < c := by
    exact opNorm2_pos_of_right_inverse_at j0 A Ainv hRight
  have hα : 0 < α := inv_pos.mpr hc
  have hF_eq : F = fun i j => A (e i) (e j) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change
          A (e (Sum.inr j)) (e (Sum.inl i)) =
            A (e (Sum.inl i)) (e (Sum.inr j))
        exact hSPD.1 _ _
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j => rfl
  have hFSym : IsSymmetricFiniteMatrix F := by
    intro i j
    rw [hF_eq]
    exact hSPD.1 _ _
  have hPSD : finitePSD A := finitePSD_of_isSymPosDef A hSPD
  have hASym : IsSymmetricFiniteMatrix A :=
    isSymPosDef_to_IsSymmetricFiniteMatrix A hSPD
  have hLowerA : finiteLoewnerLe
      (fun i j : Fin (r + s) => α * finiteIdMatrix i j) A := by
    exact finiteLoewnerLe_smul_id_le_of_right_inverse_opNorm2Le
      A Ainv hc hPSD hASym hRight (opNorm2Le_opNorm2 Ainv)
  have hUpperA : finiteLoewnerLe A
      (fun i j : Fin (r + s) => β * finiteIdMatrix i j) := by
    exact finiteLoewnerLe_smul_id_of_opNorm2Le A (opNorm2Le_opNorm2 A)
  have hLowerF : finiteLoewnerLe
      (fun i j : Fin r ⊕ Fin s => α * finiteIdMatrix i j) F := by
    have h := finiteLoewnerLe_reindex_equiv e hLowerA
    rw [hF_eq]
    simpa [e, finiteIdMatrix] using h
  have hUpperF : finiteLoewnerLe F
      (fun i j : Fin r ⊕ Fin s => β * finiteIdMatrix i j) := by
    have h := finiteLoewnerLe_reindex_equiv e hUpperA
    rw [hF_eq]
    simpa [e, finiteIdMatrix] using h
  have hαβ : α ≤ β := by
    let v : Fin (r + s) → ℝ := finiteBasisVec j0
    have hv : vecNorm2 v = 1 := vecNorm2_finiteBasisVec j0
    have hlo : α ≤ vecNorm2 (matMulVec (r + s) A v) := by
      simpa [α, c, Ainv] using
        (opNorm2_inv_recip_le_vecNorm2_matMulVec_of_isRightInverse
          A Ainv hRight hv)
    have hup : vecNorm2 (matMulVec (r + s) A v) ≤ β := by
      have h := opNorm2Le_opNorm2 A v
      simpa [β, hv] using h
    exact hlo.trans hup
  have hFPos : Matrix.PosDef F := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · apply Matrix.IsHermitian.ext
      intro i j
      simpa using (hFSym i j).symm
    · intro x hx
      have hxexists : ∃ i, x i ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        funext i
        exact h i
      obtain ⟨i, hi⟩ := hxexists
      have hsqpos : 0 < finiteVecNorm2Sq x := by
        unfold finiteVecNorm2Sq
        have hterm : 0 < x i ^ 2 := sq_pos_of_ne_zero hi
        have hsingle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (x j))
            (Finset.mem_univ i)
        exact hterm.trans_le hsingle
      have hlower := hLowerF x
      have hqpos : 0 < finiteQuadraticForm F x := by
        rw [finiteQuadraticForm_smul_finiteIdMatrix] at hlower
        nlinarith
      simpa [finiteQuadraticForm, finiteMatVec, dotProduct,
        Matrix.mulVec] using hqpos
  have hA11Pos : Matrix.PosDef A11 := by
    exact higham13_spd_leadingBlock_posDef A11 A21.transpose A22
      (by simpa [F] using hFPos)
  have hA11Right : IsRightInverse r A11 (nonsingInv r A11) := by
    exact isRightInverse_nonsingInv_of_isSymPosDef A11
      (matrix_posDef_to_isSymPosDef A11 hA11Pos)
  let C : ℝ := (β - α) / (2 * Real.sqrt (α * β))
  have hCnonneg : 0 ≤ C := by
    exact div_nonneg (sub_nonneg.mpr hαβ)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hcore : rectOpNorm2Le (rectMatMul A21 (nonsingInv r A11)) C := by
    exact higham13_demmel_sharp_multiplier_of_spectral_interval
      A11 A21 A22 (nonsingInv r A11) hα hαβ hA11Right
      (by simpa [F] using hFSym)
      (by simpa [F] using hLowerF)
      (by simpa [F] using hUpperF)
  have hnorm : rectOpNorm2 (rectMatMul A21 (nonsingInv r A11)) ≤ C :=
    higham13_rectOpNorm2_le_of_rectOpNorm2Le _ hCnonneg hcore
  let κ : ℝ := β * c
  have hκ : 1 ≤ κ := by
    calc
      (1 : ℝ) = c⁻¹ * c := by field_simp [hc.ne']
      _ ≤ β * c := mul_le_mul_of_nonneg_right hαβ (le_of_lt hc)
      _ = κ := rfl
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  let t : ℝ := Real.sqrt κ
  have ht : 0 < t := Real.sqrt_pos.2 hκpos
  have ht2 : t ^ 2 = κ := Real.sq_sqrt (le_of_lt hκpos)
  have hsqrtαβ : Real.sqrt (α * β) = t / c := by
    have harg : α * β = (t / c) ^ 2 := by
      dsimp [α, β, κ] at ht2 ⊢
      field_simp [hc.ne'] at ht2 ⊢
      nlinarith
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos ht hc)]
  have hCeq : C = (t - t⁻¹) / 2 := by
    dsimp [C]
    rw [hsqrtαβ]
    dsimp [α, κ] at ht2 ⊢
    field_simp [hc.ne', ht.ne'] at ht2 ⊢
    nlinarith
  have hκdef : kappa2 A (nonsingInv (r + s) A) = κ := by
    rfl
  rw [show higham13DemmelLowerLeftBlock A = A21 by rfl,
    show higham13DemmelLeadingBlock A = A11 by rfl]
  calc
    rectOpNorm2 (rectMatMul A21 (nonsingInv r A11)) ≤ C := hnorm
    _ = (t - t⁻¹) / 2 := hCeq
    _ = (Real.sqrt (kappa2 A (nonsingInv (r + s) A)) -
        (Real.sqrt (kappa2 A (nonsingInv (r + s) A)))⁻¹) / 2 := by
      rw [hκdef]

/-! ## Attainment

The rational matrix below is an SPD rotation of `diag(1, 16/9)`.  Its
`1`-by-`1` leading-block multiplier is `7/24`, exactly the notes bound.
Thus the constant in `higham13_notes_demmel_sharp_multiplier` cannot be
reduced.
-/

/-- A rational SPD matrix attaining Demmel's Chapter 13 notes bound. -/
noncomputable def higham13DemmelSharpWitness : RSqMat 2 :=
  !![(32 / 25 : ℝ), 28 / 75;
     28 / 75, 337 / 225]

/-- The explicit inverse of `higham13DemmelSharpWitness`. -/
noncomputable def higham13DemmelSharpWitnessInv : RSqMat 2 :=
  !![(337 / 400 : ℝ), -21 / 100;
     -21 / 100, 18 / 25]

private noncomputable def higham13DemmelSharpWitnessQ : RSqMat 2 :=
  !![(4 / 5 : ℝ), 3 / 5;
     -3 / 5, 4 / 5]

private noncomputable def higham13DemmelSharpWitnessEigenvalue : Fin 2 → ℝ :=
  ![(1 : ℝ), 16 / 9]

private noncomputable def higham13DemmelSharpWitnessInvEigenvalue : Fin 2 → ℝ :=
  ![(1 : ℝ), 9 / 16]

private theorem higham13DemmelSharpWitnessQ_orthogonal :
    IsOrthogonal 2 higham13DemmelSharpWitnessQ := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higham13DemmelSharpWitnessQ]
  all_goals rfl

private theorem higham13DemmelSharpWitness_eigenvectors :
    ∀ k : Fin 2,
      Matrix.mulVec higham13DemmelSharpWitness
          (fun i => higham13DemmelSharpWitnessQ i k) =
        higham13DemmelSharpWitnessEigenvalue k •
          (fun i => higham13DemmelSharpWitnessQ i k) := by
  intro k
  funext i
  fin_cases k <;> fin_cases i <;>
    norm_num [higham13DemmelSharpWitness,
      higham13DemmelSharpWitnessQ,
      higham13DemmelSharpWitnessEigenvalue,
      Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]

private theorem higham13DemmelSharpWitnessInv_eigenvectors :
    ∀ k : Fin 2,
      Matrix.mulVec higham13DemmelSharpWitnessInv
          (fun i => higham13DemmelSharpWitnessQ i k) =
        higham13DemmelSharpWitnessInvEigenvalue k •
          (fun i => higham13DemmelSharpWitnessQ i k) := by
  intro k
  funext i
  fin_cases k <;> fin_cases i <;>
    norm_num [higham13DemmelSharpWitnessInv,
      higham13DemmelSharpWitnessQ,
      higham13DemmelSharpWitnessInvEigenvalue,
      Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]

theorem higham13DemmelSharpWitness_opNorm2 :
    opNorm2 higham13DemmelSharpWitness = 16 / 9 := by
  refine higham13_opNorm2_eq_of_orthogonal_eigenbasis_attained
    higham13DemmelSharpWitness higham13DemmelSharpWitnessQ
    higham13DemmelSharpWitnessEigenvalue
    higham13DemmelSharpWitnessQ_orthogonal
    higham13DemmelSharpWitness_eigenvectors (16 / 9) (by norm_num) ?_
    (1 : Fin 2) ?_
  · intro k
    fin_cases k <;>
      norm_num [higham13DemmelSharpWitnessEigenvalue]
  · norm_num [higham13DemmelSharpWitnessEigenvalue]

theorem higham13DemmelSharpWitnessInv_opNorm2 :
    opNorm2 higham13DemmelSharpWitnessInv = 1 := by
  refine higham13_opNorm2_eq_of_orthogonal_eigenbasis_attained
    higham13DemmelSharpWitnessInv higham13DemmelSharpWitnessQ
    higham13DemmelSharpWitnessInvEigenvalue
    higham13DemmelSharpWitnessQ_orthogonal
    higham13DemmelSharpWitnessInv_eigenvectors 1 (by norm_num) ?_
    (0 : Fin 2) ?_
  · intro k
    fin_cases k <;>
      norm_num [higham13DemmelSharpWitnessInvEigenvalue]
  · norm_num [higham13DemmelSharpWitnessInvEigenvalue]

theorem higham13DemmelSharpWitness_rightInverse :
    IsRightInverse 2 higham13DemmelSharpWitness
      higham13DemmelSharpWitnessInv := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higham13DemmelSharpWitness,
      higham13DemmelSharpWitnessInv, Matrix.mul_apply]
  all_goals rfl

theorem higham13DemmelSharpWitness_isSymPosDef :
    IsSymPosDef 2 higham13DemmelSharpWitness := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham13DemmelSharpWitness]
  · intro x hx
    let u : ℝ := (4 / 5 : ℝ) * x 0 - (3 / 5 : ℝ) * x 1
    let v : ℝ := (3 / 5 : ℝ) * x 0 + (4 / 5 : ℝ) * x 1
    have hform :
        ∑ i : Fin 2, ∑ j : Fin 2,
            x i * higham13DemmelSharpWitness i j * x j =
          u ^ 2 + (16 / 9 : ℝ) * v ^ 2 := by
      simp [higham13DemmelSharpWitness, Fin.sum_univ_two, u, v]
      ring
    have hnorm : x 0 ^ 2 + x 1 ^ 2 = u ^ 2 + v ^ 2 := by
      dsimp [u, v]
      ring
    have hxpos : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      obtain ⟨i, hi⟩ := hx
      fin_cases i
      · have hi0 : x 0 ≠ 0 := by simpa using hi
        nlinarith [sq_pos_of_ne_zero hi0, sq_nonneg (x 1)]
      · have hi1 : x 1 ≠ 0 := by simpa using hi
        nlinarith [sq_pos_of_ne_zero hi1, sq_nonneg (x 0)]
    rw [hform]
    nlinarith [sq_nonneg u, sq_nonneg v]

private noncomputable def higham13DemmelSharpLeadingInv : RSqMat 1 :=
  !![(25 / 32 : ℝ)]

private theorem higham13DemmelSharpLeadingInv_rightInverse :
    IsRightInverse 1
      (higham13DemmelLeadingBlock (r := 1) (s := 1)
        higham13DemmelSharpWitness)
      higham13DemmelSharpLeadingInv := by
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp only [Fin.sum_univ_one, if_pos]
  have hcast : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := by rfl
  rw [show
      higham13DemmelLeadingBlock (r := 1) (s := 1)
          higham13DemmelSharpWitness 0 0 = 32 / 25 by
        unfold higham13DemmelLeadingBlock
        rw [finSumFinEquiv_apply_left, hcast]
        rfl]
  rw [show higham13DemmelSharpLeadingInv 0 0 = 25 / 32 by
    rfl]
  norm_num

private theorem higham13_rectOpNorm2_singleton
    (M : Matrix (Fin 1) (Fin 1) ℝ) :
    rectOpNorm2 M = |M 0 0| := by
  change opNorm2 M = |M 0 0|
  let Q : RSqMat 1 := 1
  let d : Fin 1 → ℝ := fun _ => M 0 0
  have hQ : IsOrthogonal 1 Q := by
    apply IsOrthogonal.of_col_orthonormal
    intro i j
    fin_cases i <;> fin_cases j
    simp [Q]
  have heig : ∀ k : Fin 1,
      Matrix.mulVec M (fun i => Q i k) = d k • (fun i => Q i k) := by
    intro k
    funext i
    fin_cases k <;> fin_cases i
    simp [Q, d, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  apply higham13_opNorm2_eq_of_orthogonal_eigenbasis_attained
    M Q d hQ heig |M 0 0| (abs_nonneg _) (fun k => by
      fin_cases k
      rfl) (0 : Fin 1)
  rfl

theorem higham13DemmelSharpWitness_multiplierNorm :
    rectOpNorm2
        (rectMatMul
          (higham13DemmelLowerLeftBlock (r := 1) (s := 1)
            higham13DemmelSharpWitness)
          (nonsingInv 1
            (higham13DemmelLeadingBlock (r := 1) (s := 1)
              higham13DemmelSharpWitness))) =
      7 / 24 := by
  rw [nonsingInv_eq_of_isRightInverse _ _
    higham13DemmelSharpLeadingInv_rightInverse]
  rw [higham13_rectOpNorm2_singleton]
  unfold rectMatMul
  rw [Fin.sum_univ_one]
  have hleft : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := by rfl
  have hright : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := by rfl
  rw [show
      higham13DemmelLowerLeftBlock (r := 1) (s := 1)
          higham13DemmelSharpWitness 0 0 = 28 / 75 by
        unfold higham13DemmelLowerLeftBlock
        rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
          hright, hleft]
        rfl]
  rw [show higham13DemmelSharpLeadingInv 0 0 = 25 / 32 by
    rfl]
  change |(28 / 75 : ℝ) * (25 / 32)| = 7 / 24
  norm_num

theorem higham13DemmelSharpWitness_kappa2 :
    kappa2 higham13DemmelSharpWitness
        (nonsingInv 2 higham13DemmelSharpWitness) =
      16 / 9 := by
  rw [nonsingInv_eq_of_isRightInverse _ _
    higham13DemmelSharpWitness_rightInverse]
  rw [kappa2, higham13DemmelSharpWitness_opNorm2,
    higham13DemmelSharpWitnessInv_opNorm2]
  norm_num

/-- The strengthened Chapter 13 notes constant is attained exactly. -/
theorem higham13_notes_demmel_sharp_multiplier_attained :
    rectOpNorm2
        (rectMatMul
          (higham13DemmelLowerLeftBlock (r := 1) (s := 1)
            higham13DemmelSharpWitness)
          (nonsingInv 1
            (higham13DemmelLeadingBlock (r := 1) (s := 1)
              higham13DemmelSharpWitness))) =
      (Real.sqrt
            (kappa2 higham13DemmelSharpWitness
              (nonsingInv 2 higham13DemmelSharpWitness)) -
          (Real.sqrt
            (kappa2 higham13DemmelSharpWitness
              (nonsingInv 2 higham13DemmelSharpWitness)))⁻¹) / 2 := by
  rw [higham13DemmelSharpWitness_multiplierNorm,
    higham13DemmelSharpWitness_kappa2]
  have hsqrt : Real.sqrt (16 / 9 : ℝ) = 4 / 3 := by
    rw [show (16 / 9 : ℝ) = (4 / 3 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
  rw [hsqrt]
  norm_num

end NumStability
