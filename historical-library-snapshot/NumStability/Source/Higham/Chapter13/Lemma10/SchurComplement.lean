import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter13.Lemma10.SchurComplement

This module formalizes the source-facing Chapter 13 statements for
`Lemma10.SchurComplement`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.2  SPD symmetric partition display
-- ============================================================

/-- Higham, 2nd ed., Chapter 13, Section 13.3.2, p.255:
    symmetric positive definite matrices are partitioned as
    `[[A₁₁, A₂₁ᵀ], [A₂₁, A₂₂]]`.

    This theorem records the exact symmetric block-matrix part of that display:
    if the diagonal blocks are symmetric, then the displayed `fromBlocks`
    matrix is symmetric.  Positive definiteness and the Cholesky/condition-number
    bounds used in Lemmas 13.9 and 13.10 remain separate obligations. -/
theorem higham13_spd_symmetric_partition_isSymm {r s α : Type*}
    [CommSemiring α]
    (A11 : Matrix r r α) (A21 : Matrix s r α) (A22 : Matrix s s α)
    (h11 : A11.IsSymm) (h22 : A22.IsSymm) :
    (Matrix.fromBlocks A11 A21ᵀ A21 A22).IsSymm := by
  exact Matrix.IsSymm.fromBlocks h11 rfl h22

/-- The leading diagonal block in the Hermitian two-by-two SPD partition is
    positive definite.  This is the principal-submatrix step used before forming
    the Schur complement in the proof route for Lemma 13.10. -/
theorem higham13_spd_leadingBlock_posDef {r s : Type*}
    [Fintype r] [Fintype s]
    (A11 : Matrix r r ℝ) (A12 : Matrix r s ℝ) (A22 : Matrix s s ℝ)
    (hFull : (Matrix.fromBlocks A11 A12 A12ᴴ A22).PosDef) :
    A11.PosDef := by
  simpa [Matrix.fromBlocks] using
    matrix_posDef_submatrix_of_injective hFull Sum.inl
      (fun _ _ h => Sum.inl.inj h)

/-- Strict positive definiteness descends to the Schur complement in the
    Hermitian two-by-two partition used for Higham's Lemma 13.10.  Taking
    `A12 = A21ᵀ` gives the source display
    `S = A₂₂ - A₂₁ A₁₁⁻¹ A₂₁ᵀ`.  This records the SPD part of the source proof
    route; the condition-number comparison `κ₂(S) ≤ κ₂(A)` is a separate
    spectral-norm dependency. -/
theorem higham13_spd_schurComplement_posDef {r s : Type*}
    [Fintype r] [Fintype s] [DecidableEq r]
    (A11 : Matrix r r ℝ) (A12 : Matrix r s ℝ) (A22 : Matrix s s ℝ)
    (hA11 : A11.PosDef) [Invertible A11]
    (hFull : (Matrix.fromBlocks A11 A12 A12ᴴ A22).PosDef) :
    (A22 - A12ᴴ * A11⁻¹ * A12).PosDef := by
  classical
  have hSpsd : (A22 - A12ᴴ * A11⁻¹ * A12).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ A12 A22 hA11).mp hFull.posSemidef
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hSpsd.1 ?_
  intro x hx
  let y : r ⊕ s → ℝ := -((A11⁻¹ * A12) *ᵥ x) ⊕ᵥ x
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    funext j
    have hentry := congr_fun hy0 (Sum.inr j)
    simpa [y] using hentry
  have hpos := hFull.dotProduct_mulVec_pos hy
  rw [Matrix.dotProduct_mulVec, Matrix.schur_complement_eq₁₁ A12 A22 _ _ hA11.1,
    neg_add_cancel, dotProduct_zero, zero_add, ← Matrix.dotProduct_mulVec] at hpos
  simpa [y] using hpos

/-- Source-shaped SPD Schur-complement dependency for Higham's Lemma 13.10.
    From positive definiteness of the Hermitian block matrix alone, the leading
    block is positive definite and therefore nonsingular, so the Schur
    complement `A22 - A12ᴴ A11⁻¹ A12` is positive definite.  The remaining
    Lemma 13.10 work is the condition-number inequality, not this SPD fact. -/
theorem higham13_spd_schurComplement_posDef_of_full {r s : Type*}
    [Fintype r] [Fintype s] [DecidableEq r]
    (A11 : Matrix r r ℝ) (A12 : Matrix r s ℝ) (A22 : Matrix s s ℝ)
    (hFull : (Matrix.fromBlocks A11 A12 A12ᴴ A22).PosDef) :
    (A22 - A12ᴴ * A11⁻¹ * A12).PosDef := by
  have hA11 : A11.PosDef :=
    higham13_spd_leadingBlock_posDef A11 A12 A22 hFull
  letI : Invertible A11 :=
    Matrix.invertibleOfIsUnitDet A11
      (isUnit_iff_ne_zero.mpr (ne_of_gt (Matrix.PosDef.det_pos hA11)))
  exact higham13_spd_schurComplement_posDef A11 A12 A22 hA11 hFull

/-- Source-display specialization of
    `higham13_spd_schurComplement_posDef_of_full` for the real SPD partition
    `[[A11, A21ᵀ], [A21, A22]]` printed before Lemma 13.10. -/
theorem higham13_spd_schurComplement_source_posDef {r s : Type*}
    [Fintype r] [Fintype s] [DecidableEq r]
    (A11 : Matrix r r ℝ) (A21 : Matrix s r ℝ) (A22 : Matrix s s ℝ)
    (hFull : (Matrix.fromBlocks A11 A21ᵀ A21 A22).PosDef) :
    (A22 - A21 * A11⁻¹ * A21ᵀ).PosDef := by
  have hFull' : (Matrix.fromBlocks A11 A21ᵀ (A21ᵀ)ᴴ A22).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hFull
  have h :=
    higham13_spd_schurComplement_posDef_of_full A11 A21ᵀ A22 hFull'
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- Higham, 2nd ed., Chapter 13, Lemma 13.10 proof route:
    the Schur complement in the SPD source partition is Loewner-bounded by
    the trailing principal block.

    Algebraically, `A22 - S = A21 A11^{-1} A21^T`, and this Gram-type term is
    positive semidefinite because the SPD leading block has PSD inverse. -/
theorem higham13_spd_schurComplement_source_loewnerLe_A22 {r s : Type*}
    [Fintype r] [Fintype s] [DecidableEq r]
    (A11 : Matrix r r ℝ) (A21 : Matrix s r ℝ) (A22 : Matrix s s ℝ)
    (hA11 : A11.PosDef) :
    finiteLoewnerLe
      (fun i j : s => (A22 - A21 * A11⁻¹ * A21.transpose) i j)
      (fun i j : s => A22 i j) := by
  classical
  have hInvPSD : (A11⁻¹).PosSemidef := hA11.posSemidef.inv
  have hGram : (A21 * A11⁻¹ * A21.transpose).PosSemidef := by
    have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hInvPSD A21
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using h
  refine Matrix_posSemidef_sub.to_finiteLoewnerLe
    (fun i j : s => (A22 - A21 * A11⁻¹ * A21.transpose) i j)
    (fun i j : s => A22 i j) ?_
  simpa [Matrix.sub_apply] using hGram

/-- Source-shaped full-SPD specialization of
    `higham13_spd_schurComplement_source_loewnerLe_A22`. -/
theorem higham13_spd_schurComplement_source_loewnerLe_A22_of_full
    {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r]
    (A11 : Matrix r r ℝ) (A21 : Matrix s r ℝ) (A22 : Matrix s s ℝ)
    (hFull : (Matrix.fromBlocks A11 A21ᵀ A21 A22).PosDef) :
    finiteLoewnerLe
      (fun i j : s => (A22 - A21 * A11⁻¹ * A21.transpose) i j)
      (fun i j : s => A22 i j) := by
  have hFull' :
      (Matrix.fromBlocks A11 A21.transpose (A21.transpose)ᴴ A22).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hFull
  have hA11 : A11.PosDef :=
    higham13_spd_leadingBlock_posDef A11 A21.transpose A22 hFull'
  exact higham13_spd_schurComplement_source_loewnerLe_A22
    A11 A21 A22 hA11

/-- Higham, 2nd ed., Chapter 13, Lemma 13.10 proof route:
    the SPD Schur complement inherits the full matrix's operator-2 certificate.

    This combines the Loewner bound `S <= A22`, the trailing-principal-block
    operator certificate `||A22||_2 <= ||A||_2`, and the PSD Schur-complement
    fact.  It closes the `||S||_2` half of the source condition-number bound;
    the inverse half `||S^{-1}||_2 <= ||A^{-1}||_2` remains separate. -/
theorem higham13_lemma13_10_schur_opNorm2Le_of_full_operator_bound
    {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [Nonempty s]
    (A11 : Matrix r r ℝ) (A21 : Matrix s r ℝ) (A22 : Matrix s s ℝ)
    {normA : ℝ}
    (hFull : (Matrix.fromBlocks A11 A21.transpose A21 A22).PosDef)
    (hA : finiteOpNorm2Le
      (fun i j : r ⊕ s => (Matrix.fromBlocks A11 A21.transpose A21 A22) i j)
      normA) :
    finiteOpNorm2Le
      (fun i j : s => (A22 - A21 * A11⁻¹ * A21.transpose) i j)
      normA := by
  classical
  let Afull : r ⊕ s → r ⊕ s → ℝ :=
    fun i j => (Matrix.fromBlocks A11 A21.transpose A21 A22) i j
  let S : s → s → ℝ :=
    fun i j => (A22 - A21 * A11⁻¹ * A21.transpose) i j
  haveI : Nonempty (r ⊕ s) :=
    ⟨Sum.inr (Classical.choice (inferInstance : Nonempty s))⟩
  have hNormA_nonneg : 0 ≤ normA :=
    finiteOpNorm2Le_radius_nonneg Afull (by simpa [Afull] using hA)
  have hA22 : finiteOpNorm2Le (fun i j : s => A22 i j) normA := by
    have hprincipal :=
      finiteOpNorm2Le_sumInr_principal Afull (by simpa [Afull] using hA)
    simpa [Afull, Matrix.fromBlocks] using hprincipal
  have hSpos : (A22 - A21 * A11⁻¹ * A21.transpose).PosDef := by
    simpa using higham13_spd_schurComplement_source_posDef A11 A21 A22 hFull
  have hSsym : IsSymmetricFiniteMatrix S := by
    simpa [S] using Matrix_isHermitian.to_IsSymmetricFiniteMatrix S hSpos.isHermitian
  have hSpsd : finitePSD S := by
    simpa [S] using Matrix_posSemidef.to_finitePSD S hSpos.posSemidef
  have hSle : finiteLoewnerLe S (fun i j : s => A22 i j) := by
    simpa [S] using
      higham13_spd_schurComplement_source_loewnerLe_A22_of_full
        A11 A21 A22 hFull
  exact finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_of_finiteOpNorm2Le
    S (fun i j : s => A22 i j) hNormA_nonneg hSsym hSpsd hSle hA22

end NumStability
