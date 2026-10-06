/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED94 contributors
-/
import NumStability.Algorithms.Cholesky.HighamMathiasFirstBreakdown

/-!
# Source-side ingredients for the Higham--Mathias LU success theorem

This module records the condition number that actually occurs in Mathias'
analysis and completes the noncircular Schur-complement induction for the
literal rounded arithmetic.  In particular, `higham10_mathias_f` is

`f(A) = Aᵀ sym(A)⁻¹ A = sym(A) + skew(A)ᵀ sym(A)⁻¹ skew(A)`,

not `A` itself.  Its perturbation and child-condition bridges feed the final
no-zero-pivot execution theorem at the end of this module.
-/

namespace NumStability

open scoped BigOperators

/-- Mathias' positive-definite source matrix
`f(A) = sym(A) + skew(A)ᵀ sym(A)⁻¹ skew(A)`. -/
noncomputable def higham10_mathias_f {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  higham10_29_sourceMatrix A Hinv

/-- The condition number used in Mathias' LU-success theorem:
`κ_H(A) = ‖f(A)‖₂ ‖sym(A)⁻¹‖₂`. -/
noncomputable def higham10_mathias_kappaH {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ) : ℝ :=
  opNorm2 (higham10_mathias_f A Hinv) * opNorm2 Hinv

/-- The real-valued `n^(3/2)` factor, written without real powers. -/
noncomputable def higham10_mathias_nThreeHalves (n : ℕ) : ℝ :=
  (n : ℝ) * Real.sqrt n

/-- The non-strict source condition in Mathias' Theorem 4.1. -/
def higham10_mathias_sourceCondition {n : ℕ} (fp : FPModel)
    (A Hinv : Fin n → Fin n → ℝ) : Prop :=
  24 * higham10_mathias_nThreeHalves n *
      higham10_mathias_kappaH A Hinv * fp.u ≤ 1

theorem higham10_mathias_kappaH_nonneg {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ) :
    0 ≤ higham10_mathias_kappaH A Hinv := by
  exact mul_nonneg (opNorm2_nonneg _) (opNorm2_nonneg _)

/-- The source matrix is exactly the Gram form used by the stage-decrease
theory in equation (10.29). -/
theorem higham10_mathias_gram_eq_f {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    matMul n (matMul n (fun i j => A j i) Hinv) A =
      higham10_mathias_f A Hinv := by
  exact higham10_29_gram_eq_sourceMatrix A Hinv hRight hLeft

/-- `f(A)` is positive semidefinite when the symmetric part of `A` is positive
definite and `Hinv` is its inverse. -/
theorem higham10_mathias_f_finitePSD {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    finitePSD (higham10_mathias_f A Hinv) := by
  rw [← higham10_mathias_gram_eq_f A Hinv hRight hLeft]
  intro x
  change 0 ≤ ∑ i : Fin n, x i *
    matMulVec n (matMul n (matMul n (fun a b => A b a) Hinv) A) x i
  rw [quadForm_gram_conj]
  exact spd_inv_quadForm_nonneg (symmetricPart n A) Hinv
    ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA) hRight
    (matMulVec n A x)

/-- The symmetric part is PSD (indeed SPD) on admissible Mathias data. -/
theorem higham10_mathias_symPart_finitePSD {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A) :
    finitePSD (symmetricPart n A) := by
  intro x
  rw [finiteQuadraticForm_eq_sum_sum]
  by_cases hx : ∃ i : Fin n, x i ≠ 0
  · exact le_of_lt
      (((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA).2 x hx)
  · push_neg at hx
    simp [hx]

/-- The inverse of the positive-definite symmetric part is PSD. -/
theorem higham10_mathias_symPartInv_finitePSD {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv) :
    finitePSD Hinv := by
  intro x
  change 0 ≤ ∑ i : Fin n, x i * matMulVec n Hinv x i
  exact spd_inv_quadForm_nonneg (symmetricPart n A) Hinv
    ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA) hRight x

/-- The defining decomposition `f(A) = H + KᵀH⁻¹K` gives the Loewner
inequality `H ≤ f(A)`. -/
theorem higham10_mathias_symPart_finiteLoewnerLe_f {n : ℕ}
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv) :
    finiteLoewnerLe (symmetricPart n A) (higham10_mathias_f A Hinv) := by
  intro x
  let K : Fin n → Fin n → ℝ := skewSymmetricPart n A
  let G : Fin n → Fin n → ℝ :=
    matMul n (matMul n (fun i j => K j i) Hinv) K
  have hG0 : 0 ≤ finiteQuadraticForm G x := by
    change 0 ≤ ∑ i : Fin n, x i * matMulVec n G x i
    rw [show G = matMul n (matMul n (fun i j => K j i) Hinv) K by rfl,
      quadForm_gram_conj]
    exact spd_inv_quadForm_nonneg (symmetricPart n A) Hinv
      ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA) hRight
      (matMulVec n K x)
  change finiteQuadraticForm (symmetricPart n A) x ≤
    finiteQuadraticForm
      (fun i j => symmetricPart n A i j + G i j) x
  rw [finiteQuadraticForm_add]
  exact le_add_of_nonneg_right hG0

/-- For a nonempty symmetric PSD matrix, the repository's exact operator
2-norm is its largest Hermitian eigenvalue.  This is the spectral adapter that
turns the existing equation-(10.29) eigenvalue estimates into Mathias' norm. -/
theorem opNorm2_eq_finiteMaxEigenvalue_of_finitePSD {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (hPSD : finitePSD M) :
    opNorm2 M = finiteMaxEigenvalue hn M hM := by
  have hEigNonneg :=
    (finitePSD_iff_finiteHermitianEigenvalues_nonneg M hM).mp hPSD
  obtain ⟨a0, ha0⟩ := exists_finiteMaxEigenvalue_eq hn M hM
  have hMaxNonneg : 0 ≤ finiteMaxEigenvalue hn M hM := by
    rw [← ha0]
    exact hEigNonneg a0
  apply le_antisymm
  · exact opNorm2_le_of_opNorm2Le M hMaxNonneg
      (opNorm2Le_of_finitePSD_of_finiteHermitianEigenvalues_le
        M hMaxNonneg hM hPSD (le_finiteMaxEigenvalue hn M hM))
  · have hOp := finiteOpNorm2Le_of_opNorm2Le M (opNorm2Le_opNorm2 M)
    rw [← ha0]
    exact finiteHermitianEigenvalues_le_of_nonneg_of_finiteOpNorm2Le
      M hM hOp a0 (hEigNonneg a0)

/-- `finiteMaxEigenvalue` is invariant under equality of its matrix argument;
the symmetry certificates are propositionally irrelevant. -/
theorem finiteMaxEigenvalue_congr_matrix {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (hA : IsSymmetricFiniteMatrix A) (hB : IsSymmetricFiniteMatrix B)
    (hAB : A = B) :
    finiteMaxEigenvalue hn A hA = finiteMaxEigenvalue hn B hB := by
  subst B
  rfl

/-- Loewner monotonicity specialized to the two positive-semidefinite matrices
in Mathias' definition: `‖sym(A)‖₂ ≤ ‖f(A)‖₂`. -/
theorem higham10_mathias_opNorm2_symPart_le_f {n : ℕ} (hn : 0 < n)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    opNorm2 (symmetricPart n A) ≤ opNorm2 (higham10_mathias_f A Hinv) := by
  let hHsym : IsSymmetricFiniteMatrix (symmetricPart n A) :=
    ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA).1
  let hFsym : IsSymmetricFiniteMatrix (higham10_mathias_f A Hinv) :=
    higham10_29_sourceMatrix_isSymm A Hinv hHinvSym hRight hLeft
  have hmono : finiteMaxEigenvalue hn (symmetricPart n A) hHsym ≤
      finiteMaxEigenvalue hn (higham10_mathias_f A Hinv) hFsym := by
    apply finiteMaxEigenvalue_mono_of_quadForm_le hn _ _ hHsym hFsym
    intro x
    simpa only [← finiteQuadraticForm_eq_sum_sum] using
      higham10_mathias_symPart_finiteLoewnerLe_f A Hinv hA hRight x
  calc
    opNorm2 (symmetricPart n A) =
        finiteMaxEigenvalue hn (symmetricPart n A) hHsym :=
      opNorm2_eq_finiteMaxEigenvalue_of_finitePSD hn _ hHsym
        (higham10_mathias_symPart_finitePSD A hA)
    _ ≤ finiteMaxEigenvalue hn (higham10_mathias_f A Hinv) hFsym := hmono
    _ = opNorm2 (higham10_mathias_f A Hinv) :=
      (opNorm2_eq_finiteMaxEigenvalue_of_finitePSD hn _ hFsym
        (higham10_mathias_f_finitePSD A Hinv hA hRight hLeft)).symm

/-- The remaining first-stage source inequality from Mathias' analysis:
`‖A‖₂ ≤ ‖f(A)‖₂`.

The proof applies the inverse Loewner bound
`‖H‖₂⁻¹ I ≤ H⁻¹` to `Ax`, identifies
`(Ax)ᵀH⁻¹(Ax) = xᵀf(A)x`, and uses `H ≤ f(A)`. -/
theorem higham10_mathias_opNorm2_le_opNorm2_f {n : ℕ} (hn : 0 < n)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    opNorm2 A ≤ opNorm2 (higham10_mathias_f A Hinv) := by
  let H : Fin n → Fin n → ℝ := symmetricPart n A
  let F : Fin n → Fin n → ℝ := higham10_mathias_f A Hinv
  have hHpos : 0 < opNorm2 H := by
    exact opNorm2_pos_of_right_inverse_at ⟨0, hn⟩ Hinv H hLeft
  have hLower : finiteLoewnerLe
      (fun i j : Fin n => (opNorm2 H)⁻¹ * finiteIdMatrix i j) Hinv := by
    exact finiteLoewnerLe_smul_id_le_of_right_inverse_opNorm2Le
      Hinv H hHpos
      (higham10_mathias_symPartInv_finitePSD A Hinv hA hRight)
      hHinvSym hLeft (opNorm2Le_opNorm2 H)
  have hHF : opNorm2 H ≤ opNorm2 F := by
    exact higham10_mathias_opNorm2_symPart_le_f hn A Hinv hA
      hHinvSym hRight hLeft
  have hF0 : 0 ≤ opNorm2 F := opNorm2_nonneg F
  have hFpsd : finitePSD F :=
    higham10_mathias_f_finitePSD A Hinv hA hRight hLeft
  have hcert : opNorm2Le A (opNorm2 F) := by
    intro x
    let z : Fin n → ℝ := matMulVec n A x
    have hzLower := hLower z
    rw [finiteQuadraticForm_smul_finiteIdMatrix,
      finiteVecNorm2Sq_fin] at hzLower
    have hzLower' : vecNorm2Sq z ≤
        opNorm2 H * finiteQuadraticForm Hinv z := by
      have hmul := mul_le_mul_of_nonneg_left hzLower hHpos.le
      calc
        vecNorm2Sq z = opNorm2 H * ((opNorm2 H)⁻¹ * vecNorm2Sq z) := by
          field_simp [hHpos.ne']
        _ ≤ opNorm2 H * finiteQuadraticForm Hinv z := hmul
    have hgram : finiteQuadraticForm F x = finiteQuadraticForm Hinv z := by
      have hg := quadForm_gram_conj Hinv A x
      rw [higham10_mathias_gram_eq_f A Hinv hRight hLeft] at hg
      simpa [F, z, finiteQuadraticForm, finiteMatVec] using hg
    have hqF : finiteQuadraticForm F x ≤ opNorm2 F * vecNorm2Sq x := by
      have habs := abs_vecInnerProduct_matMulVec_le_of_opNorm2Le
        F (opNorm2Le_opNorm2 F) x
      have hq0 : 0 ≤ finiteQuadraticForm F x := hFpsd x
      have hsum0 : 0 ≤ ∑ i : Fin n, x i * matMulVec n F x i := by
        simpa [finiteQuadraticForm, finiteMatVec] using hq0
      change (∑ i : Fin n, x i * matMulVec n F x i) ≤
        opNorm2 F * vecNorm2Sq x
      simpa [abs_of_nonneg hsum0] using habs
    have hzsq : vecNorm2Sq z ≤ opNorm2 F ^ 2 * vecNorm2Sq x := by
      calc
        vecNorm2Sq z ≤ opNorm2 H * finiteQuadraticForm Hinv z := hzLower'
        _ = opNorm2 H * finiteQuadraticForm F x := by rw [hgram]
        _ ≤ opNorm2 H * (opNorm2 F * vecNorm2Sq x) :=
          mul_le_mul_of_nonneg_left hqF hHpos.le
        _ ≤ opNorm2 F * (opNorm2 F * vecNorm2Sq x) := by
          exact mul_le_mul_of_nonneg_right hHF
            (mul_nonneg hF0 (vecNorm2Sq_nonneg x))
        _ = opNorm2 F ^ 2 * vecNorm2Sq x := by ring
    change vecNorm2 z ≤ opNorm2 F * vecNorm2 x
    unfold vecNorm2
    calc
      Real.sqrt (vecNorm2Sq z) ≤
          Real.sqrt (opNorm2 F ^ 2 * vecNorm2Sq x) :=
        Real.sqrt_le_sqrt hzsq
      _ = opNorm2 F * Real.sqrt (vecNorm2Sq x) := by
        rw [Real.sqrt_mul (sq_nonneg (opNorm2 F)),
          Real.sqrt_sq hF0]
  exact opNorm2_le_of_opNorm2Le A hF0 hcert

/-- A matrix and a right inverse on a nonempty square domain have operator-norm
product at least one. -/
theorem one_le_opNorm2_mul_opNorm2_of_isRightInverse {n : ℕ} (hn : 0 < n)
    (M Minv : Fin n → Fin n → ℝ) (hRight : IsRightInverse n M Minv) :
    1 ≤ opNorm2 M * opNorm2 Minv := by
  let i0 : Fin n := ⟨0, hn⟩
  let e : Fin n → ℝ := finiteBasisVec i0
  have he : vecNorm2 e = 1 := by
    simpa [e] using vecNorm2_finiteBasisVec i0
  have haction : matMulVec n M (matMulVec n Minv e) = e :=
    matMulVec_of_isRightInverse M Minv hRight e
  have hM := opNorm2Le_opNorm2 M (matMulVec n Minv e)
  have hMinv := opNorm2Le_opNorm2 Minv e
  calc
    1 = vecNorm2 e := he.symm
    _ = vecNorm2 (matMulVec n M (matMulVec n Minv e)) := by rw [haction]
    _ ≤ opNorm2 M * vecNorm2 (matMulVec n Minv e) := hM
    _ ≤ opNorm2 M * (opNorm2 Minv * vecNorm2 e) :=
      mul_le_mul_of_nonneg_left hMinv (opNorm2_nonneg M)
    _ = opNorm2 M * opNorm2 Minv := by rw [he]; ring

/-- Mathias' condition number is at least one. -/
theorem higham10_mathias_one_le_kappaH {n : ℕ} (hn : 0 < n)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    1 ≤ higham10_mathias_kappaH A Hinv := by
  have hInvProd := one_le_opNorm2_mul_opNorm2_of_isRightInverse hn
    (symmetricPart n A) Hinv hRight
  have hHf := higham10_mathias_opNorm2_symPart_le_f hn A Hinv hA
    hHinvSym hRight hLeft
  unfold higham10_mathias_kappaH
  exact hInvProd.trans
    (mul_le_mul_of_nonneg_right hHf (opNorm2_nonneg Hinv))

/-- A nonzero dimension contributes at least one to `n^(3/2)`. -/
theorem higham10_mathias_one_le_nThreeHalves {n : ℕ} (hn : 0 < n) :
    1 ≤ higham10_mathias_nThreeHalves n := by
  have hn1 : 1 ≤ n := hn
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hs2 : Real.sqrt n ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by nlinarith
  unfold higham10_mathias_nThreeHalves
  calc
    1 = (1 : ℝ) * 1 := by ring
    _ ≤ (n : ℝ) * Real.sqrt n :=
      mul_le_mul hn1r hs1 (by norm_num) (Nat.cast_nonneg n)

/-- The source condition itself implies the small-unit-roundoff cap used by
the first-stage arithmetic; no separate numerical-format assumption is needed. -/
theorem higham10_mathias_sourceCondition_u_le_one_div_twentyFour {n : ℕ}
    (hn : 0 < n) (fp : FPModel)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv)
    (hsource : higham10_mathias_sourceCondition fp A Hinv) :
    fp.u ≤ (1 : ℝ) / 24 := by
  have hnfac := higham10_mathias_one_le_nThreeHalves hn
  have hk := higham10_mathias_one_le_kappaH hn A Hinv hA hHinvSym hRight hLeft
  have hfac : 1 ≤ higham10_mathias_nThreeHalves n *
      higham10_mathias_kappaH A Hinv := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ higham10_mathias_nThreeHalves n *
          higham10_mathias_kappaH A Hinv :=
        mul_le_mul hnfac hk (by norm_num)
          (le_trans (by norm_num) hnfac)
  have hscaled : 24 * fp.u ≤
      24 * higham10_mathias_nThreeHalves n *
        higham10_mathias_kappaH A Hinv * fp.u := by
    have hu := mul_le_mul_of_nonneg_right hfac fp.u_nonneg
    calc
      24 * fp.u = 24 * (1 * fp.u) := by ring
      _ ≤ 24 * ((higham10_mathias_nThreeHalves n *
          higham10_mathias_kappaH A Hinv) * fp.u) :=
        mul_le_mul_of_nonneg_left hu (by norm_num)
      _ = 24 * higham10_mathias_nThreeHalves n *
          higham10_mathias_kappaH A Hinv * fp.u := by ring
  unfold higham10_mathias_sourceCondition at hsource
  have h24 : 24 * fp.u ≤ 1 := hscaled.trans hsource
  linarith

/-- On Mathias' admissible source data, the norm of `f(A)` is precisely the
largest eigenvalue already controlled by the equation-(10.29) development. -/
theorem higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue {n : ℕ} (hn : 0 < n)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv) :
    opNorm2 (higham10_mathias_f A Hinv) =
      finiteMaxEigenvalue hn (higham10_mathias_f A Hinv)
        (higham10_29_sourceMatrix_isSymm A Hinv hHinvSym hRight hLeft) := by
  exact opNorm2_eq_finiteMaxEigenvalue_of_finitePSD hn _ _
    (higham10_mathias_f_finitePSD A Hinv hA hRight hLeft)

/-- **Higham equation (10.29), literal operator-norm form.**  The source-facing
LU growth theorem constructs the symmetric-part inverse internally; positivity
of the resulting Gram/source matrix then converts its largest eigenvalue to the
printed operator `2`-norm. -/
theorem higham10_29_source_lu_growth_bound_opNorm2 (n : ℕ) (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hLU : LUFactSpec n A L U) :
    ∃ (Hinv : Fin n → Fin n → ℝ)
      (_hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
      (_hHinvRight : IsRightInverse n (symmetricPart n A) Hinv)
      (_hHinvLeft : IsLeftInverse n (symmetricPart n A) Hinv),
      frobNorm (higham10_29_absLUProduct L U) ≤
        (n : ℝ) * opNorm2 (higham10_29_sourceMatrix A Hinv) := by
  obtain ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft, hbound⟩ :=
    higham10_29_source_lu_growth_bound n hn A L U hA hLU
  refine ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft, ?_⟩
  have hnorm := higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue hn
    A Hinv hA hHinvSym hHinvRight hHinvLeft
  change opNorm2 (higham10_29_sourceMatrix A Hinv) = _ at hnorm
  rw [hnorm]
  exact hbound

/-! ## Literal first rounded Schur step -/

/-- Entrywise perturbation between the literal rounded first Schur update and
the exact no-pivot LU Schur complement. -/
noncomputable def higham10_mathiasFirstSchurError {m : ℕ} (fp : FPModel)
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => flSchurCompl m fp A i j - luFirstSchurComplement A i j

/-- The exact trailing block before its rank-one Schur update. -/
def higham10_mathiasFirstTail {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => A i.succ j.succ

/-- Absolute value of the exact rank-one term removed at the first LU step. -/
noncomputable def higham10_mathiasFirstRankAbs {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => |A i.succ 0 / A 0 0| * |A 0 j.succ|

/-- Sharp componentwise split for the literal first rounded Schur update.

The unchanged trailing entry receives only one subtraction rounding, hence its
coefficient is `u`; only the multiplier/product chain carries `γ₃`.  Keeping
this split is what permits Mathias' `4 u √n ‖f(A)‖₂` first-stage constant. -/
theorem higham10_mathias_firstSchurError_entry_le {m : ℕ} (fp : FPModel)
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hpivot : A 0 0 ≠ 0) (hval : gammaValid fp 3)
    (i j : Fin m) :
    |higham10_mathiasFirstSchurError fp A i j| ≤
      fp.u * |higham10_mathiasFirstTail A i j| +
        gamma fp 3 * higham10_mathiasFirstRankAbs A i j := by
  let a := A i.succ j.succ
  let e := A 0 0
  let c1 := A i.succ 0
  let c2 := A 0 j.succ
  obtain ⟨δ1, hδ1, hm⟩ := fp.model_div c1 e (by simpa [e] using hpivot)
  obtain ⟨δ2, hδ2, hp⟩ := fp.model_mul (fp.fl_div c1 e) c2
  obtain ⟨δ3, hδ3, hs⟩ := fp.model_sub a (fp.fl_mul (fp.fl_div c1 e) c2)
  obtain ⟨θ, hθ, hprod⟩ :=
    prod_error_bound fp 3 ![δ1, δ2, δ3]
      (by intro k; fin_cases k <;> simp_all) hval
  have hfactor : (1 + δ1) * (1 + δ2) * (1 + δ3) = 1 + θ := by
    rw [Fin.prod_univ_three] at hprod
    simpa using hprod
  have hs_eq : fp.fl_sub a (fp.fl_mul (fp.fl_div c1 e) c2) =
      a * (1 + δ3) - (c1 * c2 / e) * (1 + θ) := by
    rw [hs, hp, hm, ← hfactor]
    ring
  have herr : fp.fl_sub a (fp.fl_mul (fp.fl_div c1 e) c2) -
      (a - c1 * c2 / e) = a * δ3 - (c1 * c2 / e) * θ := by
    rw [hs_eq]
    ring
  have htri : |a * δ3 - (c1 * c2 / e) * θ| ≤
      |a * δ3| + |(c1 * c2 / e) * θ| := by
    simpa [sub_eq_add_neg] using abs_add_le (a * δ3) (-((c1 * c2 / e) * θ))
  have hmain : |a * δ3 - (c1 * c2 / e) * θ| ≤
      fp.u * |a| + gamma fp 3 * (|c1 / e| * |c2|) := by
    calc
      |a * δ3 - (c1 * c2 / e) * θ|
          ≤ |a * δ3| + |(c1 * c2 / e) * θ| := htri
      _ = |a| * |δ3| + |c1 * c2 / e| * |θ| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * fp.u + |c1 * c2 / e| * gamma fp 3 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hδ3 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hθ (abs_nonneg _))
      _ = fp.u * |a| + gamma fp 3 * (|c1 / e| * |c2|) := by
        rw [show c1 * c2 / e = (c1 / e) * c2 by ring, abs_mul]
        ring
  change |fp.fl_sub a (fp.fl_mul (fp.fl_div c1 e) c2) -
      (a - c1 * c2 / e)| ≤ fp.u * |a| +
        gamma fp 3 * (|c1 / e| * |c2|)
  rw [herr]
  exact hmain

/-- Frobenius form of the sharp first-step split.  This theorem is entirely
about the literal `fl_div`/`fl_mul`/`fl_sub` executor and introduces no
backward-error or successful-factorization hypothesis. -/
theorem higham10_mathias_firstSchurError_frob_le_split {m : ℕ} (fp : FPModel)
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hpivot : A 0 0 ≠ 0) (hval : gammaValid fp 3) :
    frobNorm (higham10_mathiasFirstSchurError fp A) ≤
      fp.u * frobNorm (higham10_mathiasFirstTail A) +
        gamma fp 3 * frobNorm (higham10_mathiasFirstRankAbs A) := by
  let B : Fin m → Fin m → ℝ := fun i j =>
    fp.u * |higham10_mathiasFirstTail A i j| +
      gamma fp 3 * higham10_mathiasFirstRankAbs A i j
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  have hB0 : ∀ i j, 0 ≤ B i j := by
    intro i j
    exact add_nonneg
      (mul_nonneg fp.u_nonneg (abs_nonneg _))
      (mul_nonneg hγ0 (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  calc
    frobNorm (higham10_mathiasFirstSchurError fp A)
        = frobNormRect (higham10_mathiasFirstSchurError fp A) :=
          (frobNormRect_eq_frobNorm _).symm
    _ ≤ frobNormRect B := frobNormRect_le_of_entry_abs_le _ _ hB0
      (higham10_mathias_firstSchurError_entry_le fp A hpivot hval)
    _ ≤ frobNormRect
          (fun i j => fp.u * |higham10_mathiasFirstTail A i j|) +
        frobNormRect
          (fun i j => gamma fp 3 * higham10_mathiasFirstRankAbs A i j) :=
      frobNormRect_add_le _ _
    _ = fp.u * frobNorm (higham10_mathiasFirstTail A) +
        gamma fp 3 * frobNorm (higham10_mathiasFirstRankAbs A) := by
      rw [frobNormRect_smul, frobNormRect_smul,
        abs_of_nonneg fp.u_nonneg, abs_of_nonneg hγ0,
        frobNormRect_abs, frobNormRect_eq_frobNorm,
        frobNormRect_eq_frobNorm]

/-- The rank-one part of the first rounded Schur-step perturbation is bounded
by the parent Mathias source norm.  This is equation (10.29)'s first-border
estimate restricted to the trailing block, with `λmax(f(A))` translated to
the exact source-facing `opNorm2`. -/
theorem higham10_mathias_firstRank_frob_le_opNorm2_f {m : ℕ}
    (A Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hA : higham10_4_IsNonsymPosDef (m + 1) A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse (m + 1) (symmetricPart (m + 1) A) Hinv)
    (hLeft : IsLeftInverse (m + 1) (symmetricPart (m + 1) A) Hinv) :
    frobNorm (higham10_mathiasFirstRankAbs A) ≤
      opNorm2 (higham10_mathias_f A Hinv) := by
  let R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
    |A i 0 / A 0 0| * |A 0 j|
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ :=
    matMul (m + 1) (matMul (m + 1) (fun i j => A j i) Hinv) A
  let hQsym : IsSymmetricFiniteMatrix Q := gram_conj_isSymm Hinv A hHinvSym
  let hFsym : IsSymmetricFiniteMatrix (higham10_mathias_f A Hinv) :=
    higham10_29_sourceMatrix_isSymm A Hinv hHinvSym hRight hLeft
  have htail : frobNorm (higham10_mathiasFirstRankAbs A) ≤ frobNorm R := by
    calc
      frobNorm (higham10_mathiasFirstRankAbs A)
          = frobNormRect (fun i j : Fin m => R i.succ j.succ) := by
            rw [frobNormRect_eq_frobNorm]
            rfl
      _ ≤ frobNormRect R := frobNormRect_tail_le R
      _ = frobNorm R := frobNormRect_eq_frobNorm R
  have hborder : frobNorm R ≤ finiteMaxEigenvalue (Nat.succ_pos m) Q hQsym := by
    simpa [R, Q, hQsym] using
      higham10_29_firstRank_frob_le (Nat.succ_pos m) A Hinv hA
        hHinvSym hRight hLeft
  have hQF : Q = higham10_mathias_f A Hinv := by
    exact higham10_mathias_gram_eq_f A Hinv hRight hLeft
  have hmax : finiteMaxEigenvalue (Nat.succ_pos m) Q hQsym =
      finiteMaxEigenvalue (Nat.succ_pos m) (higham10_mathias_f A Hinv) hFsym :=
    finiteMaxEigenvalue_congr (Nat.succ_pos m) Q _ hQsym hFsym hQF
  calc
    frobNorm (higham10_mathiasFirstRankAbs A) ≤ frobNorm R := htail
    _ ≤ finiteMaxEigenvalue (Nat.succ_pos m) Q hQsym := hborder
    _ = finiteMaxEigenvalue (Nat.succ_pos m)
        (higham10_mathias_f A Hinv) hFsym := hmax
    _ = opNorm2 (higham10_mathias_f A Hinv) :=
      (higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue
        (Nat.succ_pos m) A Hinv hA hHinvSym hRight hLeft).symm

/-- Standard finite-dimensional comparison `‖A‖F ≤ √n ‖A‖₂`, stated for the
repository's exact source-facing operator norm. -/
theorem frobNorm_le_sqrt_nat_mul_opNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    frobNorm A ≤ Real.sqrt n * opNorm2 A := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  calc
    Real.sqrt (frobNormSq A)
        ≤ Real.sqrt ((n : ℝ) * opNorm2 A ^ 2) :=
      Real.sqrt_le_sqrt
        (frobNormSq_le_of_opNorm2Le n A (opNorm2 A) (opNorm2Le_opNorm2 A))
    _ = Real.sqrt n * opNorm2 A := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n),
        Real.sqrt_sq (opNorm2_nonneg A)]

/-- The untouched trailing block has Frobenius norm at most `√n ‖f(A)‖₂`
whenever an operator-norm comparison is available. -/
theorem higham10_mathias_firstTail_frob_le_sqrt_mul_opNorm2_f {m : ℕ}
    (A Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hAop : opNorm2 A ≤ opNorm2 (higham10_mathias_f A Hinv)) :
    frobNorm (higham10_mathiasFirstTail A) ≤
      Real.sqrt (↑(m + 1) : ℝ) * opNorm2 (higham10_mathias_f A Hinv) := by
  calc
    frobNorm (higham10_mathiasFirstTail A)
        = frobNormRect (fun i j : Fin m => A i.succ j.succ) := by
          rw [frobNormRect_eq_frobNorm]
          rfl
    _ ≤ frobNormRect A := frobNormRect_tail_le A
    _ = frobNorm A := frobNormRect_eq_frobNorm A
    _ ≤ Real.sqrt (↑(m + 1) : ℝ) * opNorm2 A :=
      frobNorm_le_sqrt_nat_mul_opNorm2 A
    _ ≤ Real.sqrt (↑(m + 1) : ℝ) * opNorm2 (higham10_mathias_f A Hinv) :=
      mul_le_mul_of_nonneg_left hAop (Real.sqrt_nonneg _)

/-- Under the small-unit-roundoff consequence `u ≤ 1/24`, the three-operation
constant satisfies the rational bound used in the first-stage bootstrap. -/
theorem higham10_mathias_gamma_three_le_twentyFour_sevenths
    (fp : FPModel) (hu24 : fp.u ≤ (1 : ℝ) / 24) :
    gamma fp 3 ≤ (24 : ℝ) / 7 * fp.u := by
  have hden : 0 < 1 - 3 * fp.u := by
    linarith [fp.u_nonneg]
  unfold gamma
  norm_num
  rw [div_le_iff₀ hden]
  nlinarith [fp.u_nonneg]

/-- For a parent matrix of order at least two, the preceding rational bound is
at most `3 u √n`. -/
theorem higham10_mathias_gamma_three_le_three_u_sqrt {m : ℕ}
    (hm : 1 ≤ m) (fp : FPModel) (hu24 : fp.u ≤ (1 : ℝ) / 24) :
    gamma fp 3 ≤ 3 * fp.u * Real.sqrt (↑(m + 1) : ℝ) := by
  have hn2 : 2 ≤ m + 1 := by omega
  have hn2r : (2 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast hn2
  have hs0 : 0 ≤ Real.sqrt (↑(m + 1) : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (↑(m + 1) : ℝ) ^ 2 = (↑(m + 1) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hs : (8 : ℝ) / 7 ≤ Real.sqrt (↑(m + 1) : ℝ) := by
    nlinarith
  have hmul := mul_nonneg fp.u_nonneg (sub_nonneg.mpr hs)
  calc
    gamma fp 3 ≤ (24 : ℝ) / 7 * fp.u :=
      higham10_mathias_gamma_three_le_twentyFour_sevenths fp hu24
    _ ≤ 3 * fp.u * Real.sqrt (↑(m + 1) : ℝ) := by
      nlinarith

/-- Mathias' literal first-stage perturbation estimate
`‖E‖F ≤ 4 u √n ‖f(A)‖₂` for a parent order `n = m+1 ≥ 2`.
Everything involving rounded arithmetic and the source norm comparison is
discharged internally. -/
theorem higham10_mathias_firstSchurError_frob_le_four {m : ℕ}
    (hm : 1 ≤ m) (fp : FPModel)
    (A Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hA : higham10_4_IsNonsymPosDef (m + 1) A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse (m + 1) (symmetricPart (m + 1) A) Hinv)
    (hLeft : IsLeftInverse (m + 1) (symmetricPart (m + 1) A) Hinv)
    (hu24 : fp.u ≤ (1 : ℝ) / 24) :
    frobNorm (higham10_mathiasFirstSchurError fp A) ≤
      4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
        opNorm2 (higham10_mathias_f A Hinv) := by
  have hpivot : A 0 0 ≠ 0 :=
    ne_of_gt (nonsymPosDef_diag_pos hA 0)
  have hval : gammaValid fp 3 := by
    unfold gammaValid
    norm_num
    linarith [fp.u_nonneg]
  have hsplit :=
    higham10_mathias_firstSchurError_frob_le_split fp A hpivot hval
  have hAop := higham10_mathias_opNorm2_le_opNorm2_f
    (Nat.succ_pos m) A Hinv hA hHinvSym hRight hLeft
  have htail :=
    higham10_mathias_firstTail_frob_le_sqrt_mul_opNorm2_f A Hinv hAop
  have hrank := higham10_mathias_firstRank_frob_le_opNorm2_f A Hinv hA
    hHinvSym hRight hLeft
  have hγ := higham10_mathias_gamma_three_le_three_u_sqrt hm fp hu24
  have hF0 : 0 ≤ opNorm2 (higham10_mathias_f A Hinv) := opNorm2_nonneg _
  calc
    frobNorm (higham10_mathiasFirstSchurError fp A)
        ≤ fp.u * frobNorm (higham10_mathiasFirstTail A) +
          gamma fp 3 * frobNorm (higham10_mathiasFirstRankAbs A) := hsplit
    _ ≤ fp.u *
          (Real.sqrt (↑(m + 1) : ℝ) * opNorm2 (higham10_mathias_f A Hinv)) +
        gamma fp 3 * opNorm2 (higham10_mathias_f A Hinv) :=
      add_le_add
        (mul_le_mul_of_nonneg_left htail fp.u_nonneg)
        (mul_le_mul_of_nonneg_left hrank (gamma_nonneg fp hval))
    _ ≤ fp.u *
          (Real.sqrt (↑(m + 1) : ℝ) * opNorm2 (higham10_mathias_f A Hinv)) +
        (3 * fp.u * Real.sqrt (↑(m + 1) : ℝ)) *
          opNorm2 (higham10_mathias_f A Hinv) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hγ hF0)
    _ = 4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
        opNorm2 (higham10_mathias_f A Hinv) := by ring

/-- Source-condition form of the literal first-stage Mathias bound.  The
condition supplies `u ≤ 1/24` through `κ_H(A) ≥ 1`. -/
theorem higham10_mathias_firstSchurError_frob_le_four_of_sourceCondition
    {m : ℕ} (hm : 1 ≤ m) (fp : FPModel)
    (A Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hA : higham10_4_IsNonsymPosDef (m + 1) A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse (m + 1) (symmetricPart (m + 1) A) Hinv)
    (hLeft : IsLeftInverse (m + 1) (symmetricPart (m + 1) A) Hinv)
    (hsource : higham10_mathias_sourceCondition fp A Hinv) :
    frobNorm (higham10_mathiasFirstSchurError fp A) ≤
      4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
        opNorm2 (higham10_mathias_f A Hinv) := by
  exact higham10_mathias_firstSchurError_frob_le_four hm fp A Hinv hA
    hHinvSym hRight hLeft
    (higham10_mathias_sourceCondition_u_le_one_div_twentyFour
      (Nat.succ_pos m) fp A Hinv hA hHinvSym hRight hLeft hsource)

/-! ## Scalar child-condition bridge -/

/-- Scalar arithmetic behind Mathias' induction step.

If the parent order is `m+1`, its source condition holds, and the perturbed
child condition number has the factor supplied by Mathias' perturbation lemma,
then the child of order `m` again satisfies the same `24 n^(3/2) κ u ≤ 1`
condition.  This theorem contains no matrix or executor assumption; it cleanly
separates the remaining perturbation theorem from the induction arithmetic. -/
theorem higham10_mathias_child_source_scalar {m : ℕ} (hm : 1 ≤ m)
    (κ κchild u : ℝ) (hκ0 : 0 ≤ κ) (hu0 : 0 ≤ u)
    (hparent :
      24 * (↑(m + 1) : ℝ) * Real.sqrt (↑(m + 1) : ℝ) * κ * u ≤ 1)
    (hchild :
      κchild ≤ κ *
        ((1 + 12 * (Real.sqrt (↑(m + 1) : ℝ) * κ * u)) /
          (1 - 4 * (Real.sqrt (↑(m + 1) : ℝ) * κ * u)))) :
    24 * (m : ℝ) * Real.sqrt m * κchild * u ≤ 1 := by
  let N : ℝ := (m + 1 : ℕ)
  let M : ℝ := m
  let sN : ℝ := Real.sqrt N
  let sM : ℝ := Real.sqrt M
  let t : ℝ := sN * κ * u
  have hN0 : 0 ≤ N := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hMN : M ≤ N := by
    dsimp [M, N]
    exact_mod_cast Nat.le_succ m
  have hsN0 : 0 ≤ sN := by simp [sN]
  have hsM0 : 0 ≤ sM := by simp [sM]
  have ht0 : 0 ≤ t := by
    exact mul_nonneg (mul_nonneg hsN0 hκ0) hu0
  have hparent' : 24 * N * t ≤ 1 := by
    dsimp [N, t, sN]
    convert hparent using 1
    ring
  have h24t : 24 * t ≤ 1 := by
    have hNt : t ≤ N * t := by
      have hN1 : (1 : ℝ) ≤ N := by
        dsimp [N]
        exact_mod_cast (show 1 ≤ m + 1 by omega)
      simpa using mul_le_mul_of_nonneg_right hN1 ht0
    calc
      24 * t ≤ 24 * (N * t) :=
        mul_le_mul_of_nonneg_left hNt (by norm_num)
      _ = 24 * N * t := by ring
      _ ≤ 1 := hparent'
  have ht12 : 12 * t ≤ 1 := by linarith
  have hden : 0 < 1 - 4 * t := by linarith
  have hratio : (1 + 12 * t) / (1 - 4 * t) ≤ 1 + 24 * t := by
    rw [div_le_iff₀ hden]
    have hprod : 0 ≤ t * (1 - 12 * t) :=
      mul_nonneg ht0 (sub_nonneg.mpr ht12)
    nlinarith
  have hchild' : κchild ≤ κ * (1 + 24 * t) := by
    calc
      κchild ≤ κ * ((1 + 12 * t) / (1 - 4 * t)) := by
        simpa [t, sN, N] using hchild
      _ ≤ κ * (1 + 24 * t) :=
        mul_le_mul_of_nonneg_left hratio hκ0
  have hsMN : sM ≤ sN := by
    exact Real.sqrt_le_sqrt hMN
  have hMt : 24 * M * t ≤ 24 * N * t := by
    have hcoeff : 24 * M ≤ 24 * N :=
      mul_le_mul_of_nonneg_left hMN (by norm_num)
    exact mul_le_mul_of_nonneg_right hcoeff ht0
  have hMfactor : M * (1 + 24 * t) ≤ N := by
    have hMt1 : 24 * M * t ≤ 1 := hMt.trans hparent'
    have hNM : N = M + 1 := by
      simp [N, M]
    rw [hNM]
    nlinarith
  have hfactor0 : 0 ≤ 1 + 24 * t := by positivity
  have hdim : M * sM * (1 + 24 * t) ≤ N * sN := by
    calc
      M * sM * (1 + 24 * t) ≤ M * sN * (1 + 24 * t) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsMN hM0) hfactor0
      _ = (M * (1 + 24 * t)) * sN := by ring
      _ ≤ N * sN := mul_le_mul_of_nonneg_right hMfactor hsN0
  have hκu0 : 0 ≤ κ * u := mul_nonneg hκ0 hu0
  calc
    24 * (m : ℝ) * Real.sqrt m * κchild * u
        = 24 * (M * sM) * (κchild * u) := by simp [M, sM]; ring
    _ ≤ 24 * (M * sM) * (κ * (1 + 24 * t) * u) := by
      have hMu0 : 0 ≤ 24 * (M * sM) := by positivity
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hchild' hu0) hMu0
    _ = 24 * (M * sM * (1 + 24 * t)) * (κ * u) := by ring
    _ ≤ 24 * (N * sN) * (κ * u) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdim (by norm_num)) hκu0
    _ = 24 * N * t := by simp [t]; ring
    _ ≤ 1 := hparent'

/-! ## Perturbation machinery -/

/-- Relative inverse monotonicity in finite quadratic-form order.

If `α M ≤ N`, `α > 0`, `M` is symmetric PSD, and both displayed inverse
candidates are right inverses, then `N⁻¹ ≤ α⁻¹ M⁻¹`.  This is the relative
version of `finiteLoewnerLe_right_inverse_upper_of_smul_id_le`. -/
theorem finiteLoewnerLe_rightInverses_anti_of_smul_left {n : ℕ}
    (M Minv N Ninv : Fin n → Fin n → ℝ) (α : ℝ)
    (hα : 0 < α) (hMpsd : finitePSD M)
    (hMsym : IsSymmetricFiniteMatrix M)
    (hLower : finiteLoewnerLe (fun i j => α * M i j) N)
    (hMright : IsRightInverse n M Minv)
    (hNright : IsRightInverse n N Ninv) :
    finiteLoewnerLe Ninv (fun i j => α⁻¹ * Minv i j) := by
  intro x
  let y : Fin n → ℝ := finiteMatVec Ninv x
  let v : Fin n → ℝ := finiteMatVec Minv x
  let q : ℝ := finiteQuadraticForm N y
  let qy : ℝ := finiteQuadraticForm M y
  let qv : ℝ := finiteQuadraticForm M v
  have hNN : finiteMatMul N Ninv = finiteIdMatrix := by
    ext i j
    exact hNright i j
  have hMM : finiteMatMul M Minv = finiteIdMatrix := by
    ext i j
    exact hMright i j
  have hNy : finiteMatVec N y = x := by
    calc
      finiteMatVec N y = finiteMatVec N (finiteMatVec Ninv x) := rfl
      _ = finiteMatVec (finiteMatMul N Ninv) x := by
        rw [finiteMatVec_finiteMatMul]
      _ = finiteMatVec finiteIdMatrix x := by rw [hNN]
      _ = x := finiteMatVec_finiteIdMatrix x
  have hMv : finiteMatVec M v = x := by
    calc
      finiteMatVec M v = finiteMatVec M (finiteMatVec Minv x) := rfl
      _ = finiteMatVec (finiteMatMul M Minv) x := by
        rw [finiteMatVec_finiteMatMul]
      _ = finiteMatVec finiteIdMatrix x := by rw [hMM]
      _ = x := finiteMatVec_finiteIdMatrix x
  have hNinvQ : finiteQuadraticForm Ninv x = q := by
    unfold q y finiteQuadraticForm
    rw [hNy]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hMinvQ : finiteQuadraticForm Minv x = qv := by
    unfold qv v finiteQuadraticForm
    rw [hMv]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hLowerY : α * qy ≤ q := by
    have h := hLower y
    rw [finiteQuadraticForm_smul] at h
    simpa [q, qy] using h
  have hqy0 : 0 ≤ qy := hMpsd y
  have hq0 : 0 ≤ q :=
    (mul_nonneg hα.le hqy0).trans hLowerY
  have hcross : q = ∑ i : Fin n, v i * finiteMatVec M y i := by
    calc
      q = ∑ i : Fin n, x i * y i := by
        unfold q finiteQuadraticForm
        rw [hNy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i : Fin n, finiteMatVec M v i * y i := by rw [hMv]
      _ = ∑ i : Fin n, v i * finiteMatVec M y i :=
        (finiteVecInnerProduct_finiteMatVec_left_eq_right_of_symmetric
          M hMsym v y).symm
  have hcs : q ^ 2 ≤ qv * qy := by
    rw [hcross]
    simpa [qv, qy] using finitePSD_cauchy_schwarz M hMpsd hMsym v y
  have hqle : q ≤ α⁻¹ * qv := by
    by_cases hqyZero : qy = 0
    · have hqSq : q ^ 2 ≤ 0 := by simpa [hqyZero] using hcs
      have hqEq : q = 0 := by nlinarith [sq_nonneg q]
      rw [hqEq]
      exact mul_nonneg (inv_nonneg.mpr hα.le) (hMpsd v)
    · have hqyPos : 0 < qy := lt_of_le_of_ne hqy0 (Ne.symm hqyZero)
      have hmulLower : α * qy * q ≤ q ^ 2 := by
        calc
          α * qy * q ≤ q * q := mul_le_mul_of_nonneg_right hLowerY hq0
          _ = q ^ 2 := by ring
      have hαq : α * q ≤ qv := by
        exact le_of_mul_le_mul_right (by nlinarith) hqyPos
      rw [show α⁻¹ * qv = qv / α by rw [div_eq_inv_mul]]
      exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hαq)
  rw [hNinvQ, finiteQuadraticForm_smul, hMinvQ]
  exact hqle

/-- Taking the symmetric part does not increase the exact operator-2 norm. -/
theorem higham10_mathias_symmetricPart_opNorm2Le {n : ℕ}
    (E : Fin n → Fin n → ℝ) :
    opNorm2Le (symmetricPart n E) (opNorm2 E) := by
  have hE : opNorm2Le E (opNorm2 E) := opNorm2Le_opNorm2 E
  have hET : opNorm2Le (matTranspose E) (opNorm2 E) :=
    opNorm2Le_transpose E (opNorm2_nonneg E) hE
  have hadd : opNorm2Le (fun i j => E i j + matTranspose E i j)
      (opNorm2 E + opNorm2 E) := opNorm2Le_add E (matTranspose E)
        (opNorm2 E) (opNorm2 E) hE hET
  have hhalf := opNorm2Le_smul n
    (fun i j => E i j + matTranspose E i j)
    (opNorm2 E + opNorm2 E) ((1 : ℝ) / 2) (by norm_num) hadd
  convert hhalf using 1
  · funext i j
    simp [symmetricPart, matTranspose]
    ring
  · ring

/-- Relative lower bound for the perturbed symmetric part.

Writing `H = sym(A)`, `F = sym(E)`, and
`a = ‖E‖₂ ‖H⁻¹‖₂`, the smallness condition gives
`(1-a) H ≤ H+F = sym(A+E)`. -/
theorem higham10_mathias_perturbedSymPart_relative_lower {n : ℕ} (hn : 0 < n)
    (A E Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv) :
    finiteLoewnerLe
      (fun i j => (1 - opNorm2 E * opNorm2 Hinv) * symmetricPart n A i j)
      (symmetricPart n (fun i j => A i j + E i j)) := by
  let H : Fin n → Fin n → ℝ := symmetricPart n A
  let F : Fin n → Fin n → ℝ := symmetricPart n E
  let ε : ℝ := opNorm2 E
  let h : ℝ := opNorm2 Hinv
  have hε0 : 0 ≤ ε := opNorm2_nonneg E
  have hh0 : 0 ≤ h := opNorm2_nonneg Hinv
  have hhpos : 0 < h :=
    opNorm2_pos_of_right_inverse_at ⟨0, hn⟩ H Hinv hRight
  have hHpsd : finitePSD H := higham10_mathias_symPart_finitePSD A hA
  have hHsym : IsSymmetricFiniteMatrix H :=
    ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA).1
  have hIdLower : finiteLoewnerLe
      (fun i j : Fin n => h⁻¹ * finiteIdMatrix i j) H := by
    exact finiteLoewnerLe_smul_id_le_of_right_inverse_opNorm2Le
      H Hinv hhpos hHpsd hHsym hRight (opNorm2Le_opNorm2 Hinv)
  intro x
  have hIdX := hIdLower x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteVecNorm2Sq_fin] at hIdX
  have hnormH : vecNorm2Sq x ≤ h * finiteQuadraticForm H x := by
    have hmul := mul_le_mul_of_nonneg_left hIdX hhpos.le
    calc
      vecNorm2Sq x = h * (h⁻¹ * vecNorm2Sq x) := by
        field_simp [hhpos.ne']
      _ ≤ h * finiteQuadraticForm H x := hmul
  have hFcert : opNorm2Le F ε := by
    simpa [F, ε] using higham10_mathias_symmetricPart_opNorm2Le E
  have hFabs : |finiteQuadraticForm F x| ≤ ε * vecNorm2Sq x := by
    have habs := abs_vecInnerProduct_matMulVec_le_of_opNorm2Le F hFcert x
    simpa [finiteQuadraticForm, finiteMatVec] using habs
  have hFneg : -(ε * vecNorm2Sq x) ≤ finiteQuadraticForm F x := by
    calc
      -(ε * vecNorm2Sq x) ≤ -|finiteQuadraticForm F x| := neg_le_neg hFabs
      _ ≤ finiteQuadraticForm F x := neg_abs_le _
  have hscaled : ε * vecNorm2Sq x ≤
      ε * (h * finiteQuadraticForm H x) :=
    mul_le_mul_of_nonneg_left hnormH hε0
  have hkey : (1 - ε * h) * finiteQuadraticForm H x ≤
      finiteQuadraticForm H x + finiteQuadraticForm F x := by
    nlinarith
  have hpert : symmetricPart n (fun i j => A i j + E i j) =
      fun i j => H i j + F i j := by
    funext i j
    simp [H, F, symmetricPart]
    ring
  rw [hpert, finiteQuadraticForm_smul, finiteQuadraticForm_add]
  simpa [H, ε, h] using hkey

/-- A perturbation satisfying `‖E‖₂ ‖H⁻¹‖₂ ≤ 1/2` preserves positive
definiteness of the symmetric part. -/
theorem higham10_mathias_perturbed_isNonsymPosDef {n : ℕ} (hn : 0 < n)
    (A E Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hsmall : opNorm2 E * opNorm2 Hinv ≤ (1 : ℝ) / 2) :
    higham10_4_IsNonsymPosDef n (fun i j => A i j + E i j) := by
  rw [higham10_29_nonsymPosDef_iff_symPartSPD]
  constructor
  · exact symmetricPart_symmetric n (fun i j => A i j + E i j)
  · intro x hx
    have hrel := higham10_mathias_perturbedSymPart_relative_lower
      hn A E Hinv hA hRight x
    rw [finiteQuadraticForm_smul] at hrel
    have hα : 0 < 1 - opNorm2 E * opNorm2 Hinv := by
      linarith
    have hHpos :=
      ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA).2 x hx
    rw [← finiteQuadraticForm_eq_sum_sum] at hHpos ⊢
    exact (mul_pos hα hHpos).trans_le hrel

/-- Polarization of a symmetric finite quadratic form at a vector sum. -/
theorem finiteQuadraticForm_vec_add_of_symmetric
    {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (x y : ι → ℝ) :
    finiteQuadraticForm M (fun i => x i + y i) =
      finiteQuadraticForm M x +
        2 * (∑ i : ι, x i * finiteMatVec M y i) +
          finiteQuadraticForm M y := by
  have hcross : (∑ i : ι, y i * finiteMatVec M x i) =
      ∑ i : ι, x i * finiteMatVec M y i := by
    calc
      (∑ i : ι, y i * finiteMatVec M x i) =
          ∑ i : ι, finiteMatVec M y i * x i :=
        finiteVecInnerProduct_finiteMatVec_left_eq_right_of_symmetric
          M hM y x
      _ = ∑ i : ι, x i * finiteMatVec M y i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  unfold finiteQuadraticForm
  rw [finiteMatVec_add]
  simp_rw [add_mul, mul_add]
  repeat' rw [Finset.sum_add_distrib]
  rw [hcross]
  ring

/-- The inverse of the perturbed symmetric part exists and satisfies the
relative inverse estimate
`H̄⁻¹ ≤ (1 - ‖E‖₂ ‖H⁻¹‖₂)⁻¹ H⁻¹`, both in Loewner order and operator norm.

This is the inverse half of the Mathias perturbation argument, derived from
the preceding relative lower bound rather than supplied by the caller. -/
theorem higham10_mathias_perturbed_symPart_inverse_exists_relative
    {n : ℕ} (hn : 0 < n)
    (A E Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hsmall : opNorm2 E * opNorm2 Hinv ≤ (1 : ℝ) / 2) :
    ∃ Hbarinv : Fin n → Fin n → ℝ,
      (∀ i j, Hbarinv i j = Hbarinv j i) ∧
      IsRightInverse n
        (symmetricPart n (fun i j => A i j + E i j)) Hbarinv ∧
      IsLeftInverse n
        (symmetricPart n (fun i j => A i j + E i j)) Hbarinv ∧
      finiteLoewnerLe Hbarinv
        (fun i j =>
          (1 - opNorm2 E * opNorm2 Hinv)⁻¹ * Hinv i j) ∧
      opNorm2 Hbarinv ≤
        (1 - opNorm2 E * opNorm2 Hinv)⁻¹ * opNorm2 Hinv := by
  let B : Fin n → Fin n → ℝ := fun i j => A i j + E i j
  let H : Fin n → Fin n → ℝ := symmetricPart n A
  let Hbar : Fin n → Fin n → ℝ := symmetricPart n B
  let α : ℝ := 1 - opNorm2 E * opNorm2 Hinv
  have hα : 0 < α := by
    dsimp [α]
    linarith
  have hB : higham10_4_IsNonsymPosDef n B := by
    exact higham10_mathias_perturbed_isNonsymPosDef hn A E Hinv hA hRight hsmall
  have hHbarSPD : IsSymPosDef n Hbar :=
    (higham10_29_nonsymPosDef_iff_symPartSPD n B).mp hB
  obtain ⟨Hbarinv, hHbarinvSym, hHbarRight, hHbarLeft⟩ :=
    spd_inverse_exists Hbar hHbarSPD
  have hLower : finiteLoewnerLe (fun i j => α * H i j) Hbar := by
    simpa [α, H, Hbar, B] using
      higham10_mathias_perturbedSymPart_relative_lower hn A E Hinv hA hRight
  have hHpsd : finitePSD H := higham10_mathias_symPart_finitePSD A hA
  have hHsym : IsSymmetricFiniteMatrix H :=
    ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA).1
  have hInvLoewner : finiteLoewnerLe Hbarinv
      (fun i j => α⁻¹ * Hinv i j) :=
    finiteLoewnerLe_rightInverses_anti_of_smul_left
      H Hinv Hbar Hbarinv α hα hHpsd hHsym hLower hRight hHbarRight
  have hHbarInvPSD : finitePSD Hbarinv := by
    exact higham10_mathias_symPartInv_finitePSD B Hbarinv hB hHbarRight
  have hαinv0 : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
  have hscaled : finiteOpNorm2Le (fun i j => α⁻¹ * Hinv i j)
      (α⁻¹ * opNorm2 Hinv) := by
    exact finiteOpNorm2Le_of_opNorm2Le _
      (opNorm2Le_smul n Hinv (opNorm2 Hinv) α⁻¹ hαinv0
        (opNorm2Le_opNorm2 Hinv))
  have hcoef0 : 0 ≤ α⁻¹ * opNorm2 Hinv :=
    mul_nonneg hαinv0 (opNorm2_nonneg Hinv)
  have hHbarInvCert : finiteOpNorm2Le Hbarinv
      (α⁻¹ * opNorm2 Hinv) :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_of_finiteOpNorm2Le
      Hbarinv (fun i j => α⁻¹ * Hinv i j) hcoef0 hHbarinvSym
      hHbarInvPSD hInvLoewner hscaled
  have hHbarInvNorm : opNorm2 Hbarinv ≤ α⁻¹ * opNorm2 Hinv :=
    opNorm2_le_of_finiteOpNorm2Le Hbarinv hcoef0 hHbarInvCert
  refine ⟨Hbarinv, hHbarinvSym, ?_, ?_, ?_, ?_⟩
  · simpa [Hbar, B] using hHbarRight
  · simpa [Hbar, B] using hHbarLeft
  · simpa [α] using hInvLoewner
  · simpa [α] using hHbarInvNorm

/-- One-sided Mathias perturbation bound for the source Gram matrix.

If `a = ‖E‖₂ ‖H⁻¹‖₂ ≤ 1/2`, the relative inverse estimate implies
`‖f(A+E)‖₂ ≤ (1+7a) ‖f(A)‖₂`.  The constant seven is obtained directly by
expanding the `H⁻¹` quadratic form and using its Cauchy--Schwarz inequality. -/
theorem higham10_mathias_perturbed_f_opNorm2_le_seven
    {n : ℕ} (hn : 0 < n)
    (A E Hinv Hbarinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv)
    (hHbarinvSym : ∀ i j, Hbarinv i j = Hbarinv j i)
    (hHbarRight : IsRightInverse n
      (symmetricPart n (fun i j => A i j + E i j)) Hbarinv)
    (hHbarLeft : IsLeftInverse n
      (symmetricPart n (fun i j => A i j + E i j)) Hbarinv)
    (hInvLoewner : finiteLoewnerLe Hbarinv
      (fun i j =>
        (1 - opNorm2 E * opNorm2 Hinv)⁻¹ * Hinv i j))
    (hsmall : opNorm2 E * opNorm2 Hinv ≤ (1 : ℝ) / 2) :
    opNorm2
        (higham10_mathias_f (fun i j => A i j + E i j) Hbarinv) ≤
      (1 + 7 * (opNorm2 E * opNorm2 Hinv)) *
        opNorm2 (higham10_mathias_f A Hinv) := by
  let B : Fin n → Fin n → ℝ := fun i j => A i j + E i j
  let F : Fin n → Fin n → ℝ := higham10_mathias_f A Hinv
  let Fbar : Fin n → Fin n → ℝ := higham10_mathias_f B Hbarinv
  let ε : ℝ := opNorm2 E
  let h : ℝ := opNorm2 Hinv
  let a : ℝ := ε * h
  let α : ℝ := 1 - a
  let f : ℝ := opNorm2 F
  have hε0 : 0 ≤ ε := opNorm2_nonneg E
  have hh0 : 0 ≤ h := opNorm2_nonneg Hinv
  have ha0 : 0 ≤ a := mul_nonneg hε0 hh0
  have hf0 : 0 ≤ f := opNorm2_nonneg F
  have hα : 0 < α := by
    dsimp [α, a, ε, h]
    linarith
  have hαinv0 : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
  have hB : higham10_4_IsNonsymPosDef n B := by
    exact higham10_mathias_perturbed_isNonsymPosDef hn A E Hinv hA hRight
      (by simpa [a, ε, h] using hsmall)
  have hHinvPSD : finitePSD Hinv :=
    higham10_mathias_symPartInv_finitePSD A Hinv hA hRight
  have hFPSD : finitePSD F :=
    higham10_mathias_f_finitePSD A Hinv hA hRight hLeft
  have hFbarPSD : finitePSD Fbar :=
    higham10_mathias_f_finitePSD B Hbarinv hB
      (by simpa [B] using hHbarRight) (by simpa [B] using hHbarLeft)
  have hFbarSym : IsSymmetricFiniteMatrix Fbar :=
    higham10_29_sourceMatrix_isSymm B Hbarinv hHbarinvSym
      (by simpa [B] using hHbarRight) (by simpa [B] using hHbarLeft)
  have hkappa : 1 ≤ f * h := by
    simpa [f, h, F, higham10_mathias_kappaH] using
      higham10_mathias_one_le_kappaH hn A Hinv hA hHinvSym hRight hLeft
  have hratio : α⁻¹ * (1 + a) ^ 2 ≤ 1 + 7 * a := by
    have haHalf : a ≤ (1 : ℝ) / 2 := by
      simpa [a, ε, h] using hsmall
    have hfactor : 0 ≤ a * (1 - 2 * a) :=
      mul_nonneg ha0 (by linarith)
    rw [show α⁻¹ * (1 + a) ^ 2 = (1 + a) ^ 2 / α by
      rw [div_eq_inv_mul]]
    rw [div_le_iff₀ hα]
    dsimp [α]
    nlinarith
  have hquad : ∀ x : Fin n → ℝ,
      finiteQuadraticForm Fbar x ≤
        ((1 + 7 * a) * f) * vecNorm2Sq x := by
    intro x
    let z : Fin n → ℝ := finiteMatVec A x
    let w : Fin n → ℝ := finiteMatVec E x
    let r : ℝ := vecNorm2Sq x
    let qz : ℝ := finiteQuadraticForm Hinv z
    let qw : ℝ := finiteQuadraticForm Hinv w
    let cross : ℝ := ∑ i : Fin n, z i * finiteMatVec Hinv w i
    have hr0 : 0 ≤ r := vecNorm2Sq_nonneg x
    have hqz0 : 0 ≤ qz := hHinvPSD z
    have hqw0 : 0 ≤ qw := hHinvPSD w
    have hgramA : finiteQuadraticForm F x = qz := by
      have hg := quadForm_gram_conj Hinv A x
      rw [higham10_mathias_gram_eq_f A Hinv hRight hLeft] at hg
      simpa [F, qz, z, finiteQuadraticForm, finiteMatVec] using hg
    have hgramB : finiteQuadraticForm Fbar x =
        finiteQuadraticForm Hbarinv (finiteMatVec B x) := by
      have hg := quadForm_gram_conj Hbarinv B x
      rw [higham10_mathias_gram_eq_f B Hbarinv
        (by simpa [B] using hHbarRight) (by simpa [B] using hHbarLeft)] at hg
      simpa [Fbar, finiteQuadraticForm, finiteMatVec] using hg
    have hBx : finiteMatVec B x = fun i => z i + w i := by
      funext i
      unfold B z w finiteMatVec
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hqF : finiteQuadraticForm F x ≤ f * r := by
      have hu := finiteLoewnerLe_smul_id_of_opNorm2Le F
        (opNorm2Le_opNorm2 F) x
      rw [finiteQuadraticForm_smul_finiteIdMatrix,
        finiteVecNorm2Sq_fin] at hu
      simpa [f, r] using hu
    have hqz : qz ≤ f * r := by simpa [hgramA] using hqF
    have hwNorm : vecNorm2 w ≤ ε * vecNorm2 x := by
      simpa [w, ε, finiteMatVec, matMulVec] using opNorm2Le_opNorm2 E x
    have hwSq : vecNorm2Sq w ≤ ε ^ 2 * r := by
      have habs : |vecNorm2 w| ≤ |ε * vecNorm2 x| := by
        simpa [abs_of_nonneg (vecNorm2_nonneg w),
          abs_of_nonneg (mul_nonneg hε0 (vecNorm2_nonneg x))] using hwNorm
      have hsquares := (sq_le_sq).mpr habs
      calc
        vecNorm2Sq w = vecNorm2 w ^ 2 := (vecNorm2_sq w).symm
        _ ≤ (ε * vecNorm2 x) ^ 2 := hsquares
        _ = ε ^ 2 * vecNorm2 x ^ 2 := by ring
        _ = ε ^ 2 * r := by rw [vecNorm2_sq]
    have hqwOp : qw ≤ h * vecNorm2Sq w := by
      have hu := finiteLoewnerLe_smul_id_of_opNorm2Le Hinv
        (opNorm2Le_opNorm2 Hinv) w
      rw [finiteQuadraticForm_smul_finiteIdMatrix,
        finiteVecNorm2Sq_fin] at hu
      simpa [h, qw] using hu
    have hqwRaw : qw ≤ h * ε ^ 2 * r := by
      calc
        qw ≤ h * vecNorm2Sq w := hqwOp
        _ ≤ h * (ε ^ 2 * r) := mul_le_mul_of_nonneg_left hwSq hh0
        _ = h * ε ^ 2 * r := by ring
    have hcoef : h * ε ^ 2 ≤ f * a ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hkappa
        (mul_nonneg hh0 (sq_nonneg ε))
      dsimp [a]
      nlinarith
    have hqw : qw ≤ f * a ^ 2 * r := by
      calc
        qw ≤ h * ε ^ 2 * r := hqwRaw
        _ ≤ (f * a ^ 2) * r := mul_le_mul_of_nonneg_right hcoef hr0
    have hcs : cross ^ 2 ≤ qz * qw := by
      simpa [cross, qz, qw] using
        finitePSD_cauchy_schwarz Hinv hHinvPSD hHinvSym z w
    have hprod : qz * qw ≤ (f * r) * (f * a ^ 2 * r) :=
      mul_le_mul hqz hqw hqw0 (mul_nonneg hf0 hr0)
    have hcrossSq : cross ^ 2 ≤ (f * a * r) ^ 2 := by
      calc
        cross ^ 2 ≤ qz * qw := hcs
        _ ≤ (f * r) * (f * a ^ 2 * r) := hprod
        _ = (f * a * r) ^ 2 := by ring
    have hfar0 : 0 ≤ f * a * r :=
      mul_nonneg (mul_nonneg hf0 ha0) hr0
    have hcross : |cross| ≤ f * a * r := by
      have habs := (sq_le_sq).mp hcrossSq
      simpa [abs_of_nonneg hfar0] using habs
    have hsum : finiteQuadraticForm Hinv (fun i => z i + w i) ≤
        f * (1 + a) ^ 2 * r := by
      rw [finiteQuadraticForm_vec_add_of_symmetric Hinv hHinvSym z w]
      change qz + 2 * cross + qw ≤ f * (1 + a) ^ 2 * r
      have hcrossLe : cross ≤ f * a * r :=
        (le_abs_self cross).trans hcross
      nlinarith [hqz, hqw]
    have hrel : finiteQuadraticForm Hbarinv (fun i => z i + w i) ≤
        α⁻¹ * finiteQuadraticForm Hinv (fun i => z i + w i) := by
      have hlo := hInvLoewner (fun i => z i + w i)
      rw [finiteQuadraticForm_smul] at hlo
      simpa [α, a, ε, h] using hlo
    calc
      finiteQuadraticForm Fbar x =
          finiteQuadraticForm Hbarinv (fun i => z i + w i) := by
        rw [hgramB, hBx]
      _ ≤ α⁻¹ * finiteQuadraticForm Hinv (fun i => z i + w i) := hrel
      _ ≤ α⁻¹ * (f * (1 + a) ^ 2 * r) :=
        mul_le_mul_of_nonneg_left hsum hαinv0
      _ = (α⁻¹ * (1 + a) ^ 2) * (f * r) := by ring
      _ ≤ (1 + 7 * a) * (f * r) :=
        mul_le_mul_of_nonneg_right hratio (mul_nonneg hf0 hr0)
      _ = ((1 + 7 * a) * f) * r := by ring
  have hcoef0 : 0 ≤ (1 + 7 * a) * f := by positivity
  have hLoewner : finiteLoewnerLe Fbar
      (fun i j => ((1 + 7 * a) * f) * finiteIdMatrix i j) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix, finiteVecNorm2Sq_fin]
    exact hquad x
  have hcert : finiteOpNorm2Le Fbar ((1 + 7 * a) * f) :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
      Fbar hcoef0 hFbarSym hFbarPSD hLoewner
  have hnorm : opNorm2 Fbar ≤ (1 + 7 * a) * f :=
    opNorm2_le_of_finiteOpNorm2Le Fbar hcoef0 hcert
  simpa [Fbar, B, a, ε, h, f, F] using hnorm

/-- Source-faithful condition-number perturbation theorem.

The inverse is constructed from the perturbed SPD symmetric part.  With
`a = ‖E‖₂ ‖H⁻¹‖₂ ≤ 1/2`, the resulting Mathias condition number obeys
`κ_H(A+E) ≤ κ_H(A) (1+7a)/(1-a)`. -/
theorem higham10_mathias_perturbed_kappaH_exists
    {n : ℕ} (hn : 0 < n)
    (A E Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hLeft : IsLeftInverse n (symmetricPart n A) Hinv)
    (hsmall : opNorm2 E * opNorm2 Hinv ≤ (1 : ℝ) / 2) :
    ∃ Hbarinv : Fin n → Fin n → ℝ,
      (∀ i j, Hbarinv i j = Hbarinv j i) ∧
      IsRightInverse n
        (symmetricPart n (fun i j => A i j + E i j)) Hbarinv ∧
      IsLeftInverse n
        (symmetricPart n (fun i j => A i j + E i j)) Hbarinv ∧
      higham10_mathias_kappaH (fun i j => A i j + E i j) Hbarinv ≤
        higham10_mathias_kappaH A Hinv *
          ((1 + 7 * (opNorm2 E * opNorm2 Hinv)) /
            (1 - opNorm2 E * opNorm2 Hinv)) := by
  obtain ⟨Hbarinv, hHbarSym, hHbarRight, hHbarLeft,
      hInvLoewner, hInvNorm⟩ :=
    higham10_mathias_perturbed_symPart_inverse_exists_relative
      hn A E Hinv hA hRight hsmall
  have hF := higham10_mathias_perturbed_f_opNorm2_le_seven
    hn A E Hinv Hbarinv hA hHinvSym hRight hLeft hHbarSym
      hHbarRight hHbarLeft hInvLoewner hsmall
  let a : ℝ := opNorm2 E * opNorm2 Hinv
  let f : ℝ := opNorm2 (higham10_mathias_f A Hinv)
  let h : ℝ := opNorm2 Hinv
  have ha0 : 0 ≤ a :=
    mul_nonneg (opNorm2_nonneg E) (opNorm2_nonneg Hinv)
  have hf0 : 0 ≤ f := opNorm2_nonneg _
  have hh0 : 0 ≤ h := opNorm2_nonneg _
  have hα : 0 < 1 - a := by
    dsimp [a]
    linarith
  have hfactor0 : 0 ≤ (1 + 7 * a) * f := by positivity
  have hprod :
      opNorm2 (higham10_mathias_f (fun i j => A i j + E i j) Hbarinv) *
          opNorm2 Hbarinv ≤
        ((1 + 7 * a) * f) * ((1 - a)⁻¹ * h) := by
    apply mul_le_mul
    · simpa [a, f] using hF
    · simpa [a, h] using hInvNorm
    · exact opNorm2_nonneg Hbarinv
    · exact hfactor0
  refine ⟨Hbarinv, hHbarSym, hHbarRight, hHbarLeft, ?_⟩
  unfold higham10_mathias_kappaH
  calc
    opNorm2 (higham10_mathias_f (fun i j => A i j + E i j) Hbarinv) *
        opNorm2 Hbarinv ≤
      ((1 + 7 * a) * f) * ((1 - a)⁻¹ * h) := hprod
    _ = (f * h) * ((1 + 7 * a) / (1 - a)) := by
      rw [div_eq_mul_inv]
      ring
    _ = opNorm2 (higham10_mathias_f A Hinv) * opNorm2 Hinv *
        ((1 + 7 * (opNorm2 E * opNorm2 Hinv)) /
          (1 - opNorm2 E * opNorm2 Hinv)) := by
      rfl

/-- Scalar child-condition propagation for the proved seven-constant
perturbation theorem.

After the first-stage estimate gives `a ≤ 4t`, the perturbation factor is
`(1+28t)/(1-4t)`.  The exact loss from replacing order `m+1` by `m` absorbs
this factor under the parent source condition. -/
theorem higham10_mathias_child_source_scalar_seven {m : ℕ} (hm : 1 ≤ m)
    (κ κchild u : ℝ) (hκ0 : 0 ≤ κ) (hu0 : 0 ≤ u)
    (hparent :
      24 * (↑(m + 1) : ℝ) * Real.sqrt (↑(m + 1) : ℝ) * κ * u ≤ 1)
    (hchild :
      κchild ≤ κ *
        ((1 + 28 * (Real.sqrt (↑(m + 1) : ℝ) * κ * u)) /
          (1 - 4 * (Real.sqrt (↑(m + 1) : ℝ) * κ * u)))) :
    24 * (m : ℝ) * Real.sqrt m * κchild * u ≤ 1 := by
  let N : ℝ := (m + 1 : ℕ)
  let M : ℝ := m
  let sN : ℝ := Real.sqrt N
  let sM : ℝ := Real.sqrt M
  let t : ℝ := sN * κ * u
  have hM0 : 0 ≤ M := by positivity
  have hN0 : 0 ≤ N := by positivity
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact_mod_cast hm
  have hN2 : 2 ≤ N := by
    dsimp [N]
    exact_mod_cast (show 2 ≤ m + 1 by omega)
  have hNM : N = M + 1 := by simp [N, M]
  have hsM0 : 0 ≤ sM := Real.sqrt_nonneg _
  have hsN0 : 0 ≤ sN := Real.sqrt_nonneg _
  have hsMsq : sM ^ 2 = M := by
    dsimp [sM]
    exact Real.sq_sqrt hM0
  have hsNsq : sN ^ 2 = N := by
    dsimp [sN]
    exact Real.sq_sqrt hN0
  have ht0 : 0 ≤ t := mul_nonneg (mul_nonneg hsN0 hκ0) hu0
  have hparent' : 24 * N * t ≤ 1 := by
    dsimp [N, t, sN]
    convert hparent using 1
    ring
  have h24t : 24 * t ≤ 1 := by
    have hN1 : 1 ≤ N := hN2.trans' (by norm_num)
    have htNt : t ≤ N * t := by
      simpa using mul_le_mul_of_nonneg_right hN1 ht0
    calc
      24 * t ≤ 24 * (N * t) :=
        mul_le_mul_of_nonneg_left htNt (by norm_num)
      _ = 24 * N * t := by ring
      _ ≤ 1 := hparent'
  have hden : 0 < 1 - 4 * t := by linarith
  have hdimDen : 0 < 6 * N - 1 := by linarith
  have hratioN : (1 + 28 * t) / (1 - 4 * t) ≤
      (6 * N + 7) / (6 * N - 1) := by
    rw [div_le_div_iff₀ hden hdimDen]
    nlinarith
  have hpoly : 0 ≤
      12 * M ^ 4 + 144 * M ^ 3 + 291 * M ^ 2 + 135 * M + 25 := by
    positivity
  have hdimPoly : M ^ 3 * (6 * N + 7) ^ 2 ≤
      N ^ 3 * (6 * N - 1) ^ 2 := by
    rw [hNM]
    nlinarith [hpoly]
  have hdimSq : (M * sM * (6 * N + 7)) ^ 2 ≤
      (N * sN * (6 * N - 1)) ^ 2 := by
    calc
      (M * sM * (6 * N + 7)) ^ 2 =
          M ^ 2 * sM ^ 2 * (6 * N + 7) ^ 2 := by ring
      _ = M ^ 3 * (6 * N + 7) ^ 2 := by rw [hsMsq]; ring
      _ ≤ N ^ 3 * (6 * N - 1) ^ 2 := hdimPoly
      _ = N ^ 2 * sN ^ 2 * (6 * N - 1) ^ 2 := by rw [hsNsq]; ring
      _ = (N * sN * (6 * N - 1)) ^ 2 := by ring
  have hleft0 : 0 ≤ M * sM * (6 * N + 7) := by positivity
  have hright0 : 0 ≤ N * sN * (6 * N - 1) := by positivity
  have hdimCross : M * sM * (6 * N + 7) ≤
      N * sN * (6 * N - 1) := by
    have habs := (sq_le_sq).mp hdimSq
    simpa [abs_of_nonneg hleft0, abs_of_nonneg hright0] using habs
  have hdimN : M * sM * ((6 * N + 7) / (6 * N - 1)) ≤ N * sN := by
    calc
      M * sM * ((6 * N + 7) / (6 * N - 1)) =
          (M * sM * (6 * N + 7)) / (6 * N - 1) := by ring
      _ ≤ N * sN := (div_le_iff₀ hdimDen).2 (by
        simpa [mul_assoc] using hdimCross)
  have hdim : M * sM * ((1 + 28 * t) / (1 - 4 * t)) ≤ N * sN := by
    calc
      M * sM * ((1 + 28 * t) / (1 - 4 * t)) ≤
          M * sM * ((6 * N + 7) / (6 * N - 1)) :=
        mul_le_mul_of_nonneg_left hratioN (mul_nonneg hM0 hsM0)
      _ ≤ N * sN := hdimN
  have hchild' : κchild ≤ κ * ((1 + 28 * t) / (1 - 4 * t)) := by
    simpa [t, sN, N] using hchild
  have hκu0 : 0 ≤ κ * u := mul_nonneg hκ0 hu0
  calc
    24 * (m : ℝ) * Real.sqrt m * κchild * u
        = 24 * (M * sM) * (κchild * u) := by simp [M, sM]; ring
    _ ≤ 24 * (M * sM) *
        (κ * ((1 + 28 * t) / (1 - 4 * t)) * u) := by
      have hdim0 : 0 ≤ 24 * (M * sM) := by positivity
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hchild' hu0) hdim0
    _ = 24 * (M * sM * ((1 + 28 * t) / (1 - 4 * t))) *
        (κ * u) := by ring
    _ ≤ 24 * (N * sN) * (κ * u) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdim (by norm_num)) hκu0
    _ = 24 * N * t := by simp [t]; ring
    _ ≤ 1 := hparent'

/-- The inverse norm of the symmetric part cannot increase at an exact
no-pivot LU Schur step.

Writing `H = sym(S)`, its SPD Schur complement as `Z`, and
`Ĥ = sym(luFirstSchurComplement S)`, one has `Z ≤ Ĥ`, hence
`Ĥ⁻¹ ≤ Z⁻¹`.  The quadratic form of `Z⁻¹` is the trailing principal
quadratic form of `H⁻¹`, so its operator norm is bounded by `‖H⁻¹‖₂`. -/
theorem higham10_mathias_luSchur_symPartInv_opNorm2_le
    {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHinvLeft : IsLeftInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i)
    (hHhatinvRight : IsRightInverse m
      (symmetricPart m (luFirstSchurComplement S)) Hhatinv) :
    opNorm2 Hhatinv ≤ opNorm2 Hinv := by
  let H : Fin (m + 1) → Fin (m + 1) → ℝ := symmetricPart (m + 1) S
  let Hhat : Fin m → Fin m → ℝ :=
    symmetricPart m (luFirstSchurComplement S)
  let α : ℝ := S 0 0
  let fvec : Fin m → ℝ := fun i => H 0 i.succ
  let G : Fin m → Fin m → ℝ := fun i j => H i.succ j.succ
  let Z : Fin m → Fin m → ℝ :=
    fun i j => G i j - fvec i * fvec j / α
  let k : Fin m → ℝ := fun i => (S 0 i.succ - S i.succ 0) / 2
  let uvec : Fin m → ℝ := fun i => k i / Real.sqrt α
  have hα : 0 < α := by
    exact nonsymPosDef_diag_pos hS 0
  have hHspd : IsSymPosDef (m + 1) H :=
    (higham10_29_nonsymPosDef_iff_symPartSPD (m + 1) S).mp hS
  have hHsym : IsSymmetricFiniteMatrix H := hHspd.1
  have hZspd : IsSymPosDef m Z := by
    have hz := spd_schur_complement_isSymPosDef H hHspd
    have h00 : H 0 0 = α := by
      dsimp [H, α]
      unfold symmetricPart
      ring
    simp only [h00] at hz
    simpa [Z, G, fvec] using hz
  obtain ⟨Zinv, hZinvSym, hZinvRight, hZinvLeft⟩ :=
    spd_inverse_exists Z hZspd
  have hsqrt : Real.sqrt α * Real.sqrt α = α :=
    Real.mul_self_sqrt hα.le
  have huProd : ∀ i j : Fin m,
      uvec i * uvec j = k i * k j / α := by
    intro i j
    dsimp [uvec]
    rw [div_mul_div_comm, hsqrt]
  have hHhatEq : Hhat = fun i j => Z i j + uvec i * uvec j := by
    funext i j
    rw [show Hhat i j = symmetricPart m (luFirstSchurComplement S) i j by rfl,
      higham10_29_symPart_luSchur_eq]
    rw [huProd]
    dsimp [Z, G, fvec, H, α, k]
    rw [symmetricPart_symmetric (m + 1) S i.succ 0]
  have hRankPSD : finitePSD (fun i j => uvec i * uvec j) := by
    intro x
    have hrank : finiteQuadraticForm (fun i j => uvec i * uvec j) x =
        (∑ i : Fin m, uvec i * x i) ^ 2 := by
      unfold finiteQuadraticForm finiteMatVec
      calc
        (∑ i : Fin m, x i * ∑ j : Fin m, (uvec i * uvec j) * x j) =
            ∑ i : Fin m, ∑ j : Fin m,
              (x i * uvec i) * (uvec j * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ i : Fin m, (x i * uvec i) *
              (∑ j : Fin m, uvec j * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ = (∑ i : Fin m, x i * uvec i) *
            (∑ j : Fin m, uvec j * x j) := by rw [Finset.sum_mul]
        _ = (∑ i : Fin m, uvec i * x i) ^ 2 := by
          have hcomm : (∑ i : Fin m, x i * uvec i) =
              ∑ i : Fin m, uvec i * x i := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [hcomm]
          ring
    rw [hrank]
    exact sq_nonneg _
  have hLower : finiteLoewnerLe Z Hhat := by
    intro x
    rw [hHhatEq, finiteQuadraticForm_add]
    exact le_add_of_nonneg_right (hRankPSD x)
  have hZinvPSD : finitePSD Zinv := by
    intro x
    simpa [finiteQuadraticForm, finiteMatVec, matMulVec] using
      spd_inv_quadForm_nonneg Z Zinv hZspd hZinvRight x
  have hZPSD : finitePSD Z := by
    intro x
    by_cases hx : ∃ i : Fin m, x i ≠ 0
    · rw [finiteQuadraticForm_eq_sum_sum]
      exact le_of_lt (hZspd.2 x hx)
    · push_neg at hx
      simp [finiteQuadraticForm, finiteMatVec, hx]
  have hInvLoewner : finiteLoewnerLe Hhatinv Zinv := by
    have h := finiteLoewnerLe_rightInverses_anti_of_smul_left
      Z Zinv Hhat Hhatinv 1 (by norm_num) hZPSD hZspd.1
      (by simpa using hLower) hZinvRight
      (by simpa [Hhat] using hHhatinvRight)
    simpa using h
  have hZupper : finiteLoewnerLe Zinv
      (fun i j => opNorm2 Hinv * finiteIdMatrix i j) := by
    intro x
    have hZinvAct : ∀ v : Fin m → ℝ,
        matMulVec m Zinv (matMulVec m Z v) = v :=
      fun v => matMulVec_of_isRightInverse Zinv Z hZinvLeft v
    have hHinvAct : matMulVec (m + 1) H
        (matMulVec (m + 1) Hinv (Fin.cons 0 x)) = Fin.cons 0 x :=
      matMulVec_of_isRightInverse H Hinv
        (by simpa [H] using hHinvRight) (Fin.cons 0 x)
    have hblock := block_quadForm_schur_eq α hα.ne' fvec G H Hinv Z Zinv
      (by dsimp [H, α]; unfold symmetricPart; ring)
      (fun _ => rfl) (fun i => hHsym i.succ 0) (fun _ _ => rfl)
      (fun _ _ => rfl) hZinvAct 0 x hHinvAct
    have hblock' : finiteQuadraticForm Hinv (Fin.cons 0 x) =
        finiteQuadraticForm Zinv x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec] using hblock
    have hu := finiteLoewnerLe_smul_id_of_opNorm2Le Hinv
      (opNorm2Le_opNorm2 Hinv) (Fin.cons 0 x)
    rw [finiteQuadraticForm_smul_finiteIdMatrix] at hu ⊢
    have hpad : finiteVecNorm2Sq (Fin.cons 0 x) = finiteVecNorm2Sq x := by
      unfold finiteVecNorm2Sq
      rw [Fin.sum_univ_succ]
      simp
    rw [hblock', hpad] at hu
    exact hu
  have hZcert : finiteOpNorm2Le Zinv (opNorm2 Hinv) :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
      Zinv (opNorm2_nonneg Hinv) hZinvSym hZinvPSD hZupper
  have hChild : higham10_4_IsNonsymPosDef m (luFirstSchurComplement S) :=
    higham10_29_luFirstSchurComplement_isNonsymPosDef S hS
  have hHhatinvPSD : finitePSD Hhatinv :=
    higham10_mathias_symPartInv_finitePSD
      (luFirstSchurComplement S) Hhatinv hChild hHhatinvRight
  have hHhatCert : finiteOpNorm2Le Hhatinv (opNorm2 Hinv) :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_of_finiteOpNorm2Le
      Hhatinv Zinv (opNorm2_nonneg Hinv) hHhatinvSym hHhatinvPSD
      hInvLoewner hZcert
  exact opNorm2_le_of_finiteOpNorm2Le Hhatinv
    (opNorm2_nonneg Hinv) hHhatCert

/-- The exact LU Schur step decreases Mathias' full condition number. -/
theorem higham10_mathias_luSchur_kappaH_le
    {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHinvLeft : IsLeftInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i)
    (hHhatinvRight : IsRightInverse m
      (symmetricPart m (luFirstSchurComplement S)) Hhatinv)
    (hHhatinvLeft : IsLeftInverse m
      (symmetricPart m (luFirstSchurComplement S)) Hhatinv) :
    higham10_mathias_kappaH (luFirstSchurComplement S) Hhatinv ≤
      higham10_mathias_kappaH S Hinv := by
  let Shat : Fin m → Fin m → ℝ := luFirstSchurComplement S
  have hShat : higham10_4_IsNonsymPosDef m Shat :=
    higham10_29_luFirstSchurComplement_isNonsymPosDef S hS
  have hstage := higham10_29_stage_operator_le hm S hS Hinv Hhatinv
    hHinvSym hHhatinvSym hHinvRight hHhatinvRight
  have hf : opNorm2 (higham10_mathias_f Shat Hhatinv) ≤
      opNorm2 (higham10_mathias_f S Hinv) := by
    let rawChild : Fin m → Fin m → ℝ :=
      matMul m (matMul m (fun a b => Shat b a) Hhatinv) Shat
    let rawParent : Fin (m + 1) → Fin (m + 1) → ℝ :=
      matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S
    let hRawChild : IsSymmetricFiniteMatrix rawChild :=
      gram_conj_isSymm Hhatinv Shat hHhatinvSym
    let hRawParent : IsSymmetricFiniteMatrix rawParent :=
      gram_conj_isSymm Hinv S hHinvSym
    let hFChild : IsSymmetricFiniteMatrix (higham10_mathias_f Shat Hhatinv) :=
      higham10_29_sourceMatrix_isSymm Shat Hhatinv hHhatinvSym
        hHhatinvRight hHhatinvLeft
    let hFParent : IsSymmetricFiniteMatrix (higham10_mathias_f S Hinv) :=
      higham10_29_sourceMatrix_isSymm S Hinv hHinvSym hHinvRight hHinvLeft
    have hChildEq : finiteMaxEigenvalue hm rawChild hRawChild =
        finiteMaxEigenvalue hm (higham10_mathias_f Shat Hhatinv) hFChild :=
      finiteMaxEigenvalue_congr_matrix hm rawChild
        (higham10_mathias_f Shat Hhatinv) hRawChild hFChild
        (higham10_mathias_gram_eq_f Shat Hhatinv
          hHhatinvRight hHhatinvLeft)
    have hParentEq : finiteMaxEigenvalue (Nat.succ_pos m) rawParent hRawParent =
        finiteMaxEigenvalue (Nat.succ_pos m)
          (higham10_mathias_f S Hinv) hFParent :=
      finiteMaxEigenvalue_congr_matrix (Nat.succ_pos m) rawParent
        (higham10_mathias_f S Hinv) hRawParent hFParent
        (higham10_mathias_gram_eq_f S Hinv hHinvRight hHinvLeft)
    have hstage' : finiteMaxEigenvalue hm rawChild hRawChild ≤
        finiteMaxEigenvalue (Nat.succ_pos m) rawParent hRawParent := by
      simpa [rawChild, rawParent, Shat, hRawChild, hRawParent] using hstage
    calc
      opNorm2 (higham10_mathias_f Shat Hhatinv) =
          finiteMaxEigenvalue hm (higham10_mathias_f Shat Hhatinv) hFChild :=
        higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue hm
          Shat Hhatinv hShat hHhatinvSym hHhatinvRight hHhatinvLeft
      _ = finiteMaxEigenvalue hm rawChild hRawChild := hChildEq.symm
      _ ≤ finiteMaxEigenvalue (Nat.succ_pos m) rawParent hRawParent := hstage'
      _ = finiteMaxEigenvalue (Nat.succ_pos m)
          (higham10_mathias_f S Hinv) hFParent := hParentEq
      _ = opNorm2 (higham10_mathias_f S Hinv) :=
        (higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue (Nat.succ_pos m)
          S Hinv hS hHinvSym hHinvRight hHinvLeft).symm
  have hinv : opNorm2 Hhatinv ≤ opNorm2 Hinv :=
    higham10_mathias_luSchur_symPartInv_opNorm2_le hm S Hinv Hhatinv
      hS hHinvSym hHinvRight hHinvLeft hHhatinvSym hHhatinvRight
  unfold higham10_mathias_kappaH
  exact mul_le_mul hf hinv (opNorm2_nonneg Hhatinv)
    (opNorm2_nonneg (higham10_mathias_f S Hinv))

/-- One literal rounded Schur step preserves the full Mathias source
condition, with all child inverse and positive-definiteness data constructed
from the parent source hypotheses. -/
theorem higham10_mathias_firstRoundedSchur_sourceCondition_exists
    {m : ℕ} (hm : 1 ≤ m) (fp : FPModel)
    (A Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hA : higham10_4_IsNonsymPosDef (m + 1) A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse (m + 1)
      (symmetricPart (m + 1) A) Hinv)
    (hHinvLeft : IsLeftInverse (m + 1)
      (symmetricPart (m + 1) A) Hinv)
    (hsource : higham10_mathias_sourceCondition fp A Hinv) :
    ∃ Hchildinv : Fin m → Fin m → ℝ,
      higham10_4_IsNonsymPosDef m (flSchurCompl m fp A) ∧
      (∀ i j, Hchildinv i j = Hchildinv j i) ∧
      IsRightInverse m (symmetricPart m (flSchurCompl m fp A)) Hchildinv ∧
      IsLeftInverse m (symmetricPart m (flSchurCompl m fp A)) Hchildinv ∧
      higham10_mathias_sourceCondition fp (flSchurCompl m fp A) Hchildinv := by
  let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
  let E : Fin m → Fin m → ℝ := higham10_mathiasFirstSchurError fp A
  let B : Fin m → Fin m → ℝ := fun i j => S i j + E i j
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hS : higham10_4_IsNonsymPosDef m S :=
    higham10_29_luFirstSchurComplement_isNonsymPosDef A hA
  obtain ⟨HSinv, hHSinvSym, hHSinvRight, hHSinvLeft⟩ :=
    spd_inverse_exists (symmetricPart m S)
      ((higham10_29_nonsymPosDef_iff_symPartSPD m S).mp hS)
  have hInvExact : opNorm2 HSinv ≤ opNorm2 Hinv :=
    higham10_mathias_luSchur_symPartInv_opNorm2_le hm0 A Hinv HSinv
      hA hHinvSym hHinvRight hHinvLeft hHSinvSym hHSinvRight
  have hKappaExact : higham10_mathias_kappaH S HSinv ≤
      higham10_mathias_kappaH A Hinv :=
    higham10_mathias_luSchur_kappaH_le hm0 A Hinv HSinv hA
      hHinvSym hHinvRight hHinvLeft hHSinvSym hHSinvRight hHSinvLeft
  have hEfrob : frobNorm E ≤
      4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
        opNorm2 (higham10_mathias_f A Hinv) := by
    simpa [E] using
      higham10_mathias_firstSchurError_frob_le_four_of_sourceCondition
        hm fp A Hinv hA hHinvSym hHinvRight hHinvLeft hsource
  have hEop : opNorm2 E ≤
      4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
        opNorm2 (higham10_mathias_f A Hinv) :=
    (opNorm2_le_frobNorm E).trans hEfrob
  let κ : ℝ := higham10_mathias_kappaH A Hinv
  let t : ℝ := Real.sqrt (↑(m + 1) : ℝ) * κ * fp.u
  let a : ℝ := opNorm2 E * opNorm2 HSinv
  have hκ0 : 0 ≤ κ := higham10_mathias_kappaH_nonneg A Hinv
  have ht0 : 0 ≤ t := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hκ0) fp.u_nonneg
  have ha0 : 0 ≤ a :=
    mul_nonneg (opNorm2_nonneg E) (opNorm2_nonneg HSinv)
  have hparent :
      24 * (↑(m + 1) : ℝ) * Real.sqrt (↑(m + 1) : ℝ) * κ * fp.u ≤ 1 := by
    convert hsource using 1 <;>
      simp [higham10_mathias_sourceCondition,
        higham10_mathias_nThreeHalves, κ] <;> ring
  have hparentT : 24 * (↑(m + 1) : ℝ) * t ≤ 1 := by
    convert hparent using 1 <;> simp [t] <;> ring
  have h24t : 24 * t ≤ 1 := by
    have hN1 : (1 : ℝ) ≤ (↑(m + 1) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + 1 by omega)
    have htN : t ≤ (↑(m + 1) : ℝ) * t := by
      simpa using mul_le_mul_of_nonneg_right hN1 ht0
    calc
      24 * t ≤ 24 * ((↑(m + 1) : ℝ) * t) :=
        mul_le_mul_of_nonneg_left htN (by norm_num)
      _ = 24 * (↑(m + 1) : ℝ) * t := by ring
      _ ≤ 1 := hparentT
  have ha4t : a ≤ 4 * t := by
    calc
      a ≤ (4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
          opNorm2 (higham10_mathias_f A Hinv)) * opNorm2 HSinv :=
        mul_le_mul_of_nonneg_right hEop (opNorm2_nonneg HSinv)
      _ ≤ (4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
          opNorm2 (higham10_mathias_f A Hinv)) * opNorm2 Hinv :=
        mul_le_mul_of_nonneg_left hInvExact
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg)
              (Real.sqrt_nonneg _))
            (opNorm2_nonneg _))
      _ = 4 * t := by
        simp [t, κ, higham10_mathias_kappaH]
        ring
  have h4tHalf : 4 * t ≤ (1 : ℝ) / 2 := by linarith
  have haHalf : a ≤ (1 : ℝ) / 2 := ha4t.trans h4tHalf
  have hBpos : higham10_4_IsNonsymPosDef m B :=
    higham10_mathias_perturbed_isNonsymPosDef hm0 S E HSinv hS hHSinvRight
      (by simpa [a] using haHalf)
  obtain ⟨Hchildinv, hHchildSym, hHchildRight, hHchildLeft, hKappaPert⟩ :=
    higham10_mathias_perturbed_kappaH_exists hm0 S E HSinv hS
      hHSinvSym hHSinvRight hHSinvLeft (by simpa [a] using haHalf)
  have hdenA : 0 < 1 - a := by linarith
  have hdenT : 0 < 1 - 4 * t := by linarith
  have hratio : (1 + 7 * a) / (1 - a) ≤
      (1 + 28 * t) / (1 - 4 * t) := by
    rw [div_le_div_iff₀ hdenA hdenT]
    nlinarith
  have hratioA0 : 0 ≤ (1 + 7 * a) / (1 - a) :=
    div_nonneg (by positivity) hdenA.le
  have hKappaChild : higham10_mathias_kappaH B Hchildinv ≤
      κ * ((1 + 28 * t) / (1 - 4 * t)) := by
    calc
      higham10_mathias_kappaH B Hchildinv ≤
          higham10_mathias_kappaH S HSinv * ((1 + 7 * a) / (1 - a)) := by
        simpa [B, a] using hKappaPert
      _ ≤ κ * ((1 + 7 * a) / (1 - a)) :=
        mul_le_mul_of_nonneg_right (by simpa [κ] using hKappaExact) hratioA0
      _ ≤ κ * ((1 + 28 * t) / (1 - 4 * t)) :=
        mul_le_mul_of_nonneg_left hratio hκ0
  have hchildScalar :
      24 * (m : ℝ) * Real.sqrt m *
          higham10_mathias_kappaH B Hchildinv * fp.u ≤ 1 := by
    apply higham10_mathias_child_source_scalar_seven hm κ
      (higham10_mathias_kappaH B Hchildinv) fp.u hκ0 fp.u_nonneg hparent
    simpa [t] using hKappaChild
  have hsourceB : higham10_mathias_sourceCondition fp B Hchildinv := by
    convert hchildScalar using 1 <;>
      simp [higham10_mathias_sourceCondition,
        higham10_mathias_nThreeHalves] <;> ring
  have hBEq : B = flSchurCompl m fp A := by
    funext i j
    simp [B, S, E, higham10_mathiasFirstSchurError]
  refine ⟨Hchildinv, ?_, hHchildSym, ?_, ?_, ?_⟩
  · rw [← hBEq]
    exact hBpos
  · rw [← hBEq]
    exact hHchildRight
  · rw [← hBEq]
    exact hHchildLeft
  · rw [← hBEq]
    exact hsourceB

/-! ## Literal rounded right-looking GE completion -/

/-- Execution-success predicate for the literal right-looking rounded
Gaussian-elimination recurrence.  At each nonempty stage the executor uses
the current `(0,0)` entry as pivot and replaces the active matrix by the
literal `flSchurCompl` update.  Thus the predicate states that every division
pivot encountered by this concrete rounded recurrence is positive. -/
def higham10_mathias_flSchurPivotsPositive (fp : FPModel) :
    {n : ℕ} → (Fin n → Fin n → ℝ) → Prop
  | 0, _ => True
  | n + 1, A =>
      0 < A 0 0 ∧
        higham10_mathias_flSchurPivotsPositive fp (flSchurCompl n fp A)

/-- **Higham--Mathias rounded GE success theorem.**

Under the source condition `24 n^(3/2) κ_H(A) u ≤ 1`, the literal
right-looking rounded Schur executor has a positive pivot at every stage and
therefore runs to completion.  No pivot-success or child-condition hypothesis
is supplied by the caller. -/
theorem higham10_mathias_flSchur_runsToCompletion
    {n : ℕ} (fp : FPModel)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hHinvLeft : IsLeftInverse n (symmetricPart n A) Hinv)
    (hsource : higham10_mathias_sourceCondition fp A Hinv) :
    higham10_mathias_flSchurPivotsPositive fp A := by
  induction n with
  | zero =>
      trivial
  | succ m ih =>
      rw [higham10_mathias_flSchurPivotsPositive]
      refine ⟨nonsymPosDef_diag_pos hA 0, ?_⟩
      by_cases hm0 : m = 0
      · subst m
        trivial
      · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        obtain ⟨Hchildinv, hChildPos, hChildSym,
            hChildRight, hChildLeft, hChildSource⟩ :=
          higham10_mathias_firstRoundedSchur_sourceCondition_exists
            hm fp A Hinv hA hHinvSym hHinvRight hHinvLeft hsource
        exact ih (flSchurCompl m fp A) Hchildinv hChildPos hChildSym
          hChildRight hChildLeft hChildSource

end NumStability
