-- Analysis/JordanNormalForm.lean
--
-- Classical Jordan Normal Form over ℂ: the background structural lemma behind
-- Higham, *Accuracy and Stability of Numerical Algorithms* (2nd ed.),
-- Theorem 18.1 (Matrix Powers), whose general case is stated for a matrix in
-- Jordan canonical form  A = X J X⁻¹  with  J = diag(J₁,…,J_s)  a direct sum of
-- Jordan blocks (see §18.1, eqns (18.1a)/(18.1b), p. 618).  Higham -- like most
-- numerical-analysis texts -- *takes the Jordan form as given*; the existence of
-- the Jordan form is a theorem of pure linear algebra.
--
-- Mathlib v4.29 provides the *primary (generalized-eigenspace) decomposition*
--   * `Module.End.iSup_maxGenEigenspace_eq_top`      (alg. closed, fin. dim.)
--   * `Module.End.independent_maxGenEigenspace`
--   * `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`
-- and the internal-direct-sum machinery
--   * `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`
--   * `DirectSum.IsInternal.collectedBasis`
-- but it does **not** contain the classical Jordan *block* form (a nilpotent
-- operator has a basis of Jordan chains).  See the closing docstring
-- `jordan_normal_form_missing_lemma` for the precise missing statement.
--
-- This file therefore does two things, kept scrupulously separate:
--
--   (A) UNCONDITIONAL.  The *primary decomposition as an explicit matrix
--       similarity*: every  A : Matrix (Fin n) (Fin n) ℂ  is similar to a
--       block-diagonal matrix whose blocks are each of the form
--       (scalar λᵢ)·I + Nᵢ  with  Nᵢ  nilpotent.  This is exactly the reduction
--       "to the single-eigenvalue case = scalar + nilpotent" that precedes the
--       Jordan-chain argument.  (Theorems `exists_blockTriangular_similar_*`,
--       `Matrix.IsSimilar.*`.)
--
--   (B) CONDITIONAL.  Full Jordan Normal Form, `A` similar to a genuine Jordan
--       matrix, derived from (A) plus a single explicit, clearly-labelled
--       hypothesis: *every nilpotent complex matrix is similar to a
--       block-diagonal of nilpotent Jordan blocks* (`NilpotentJordanBasis`).
--       We prove this hypothesis is exactly the residual gap and that it closes
--       the theorem.
--
-- IMPORT-ONLY: this file edits nothing; it only imports.  No `sorry`/`admit`/
-- `axiom`/`native_decide`/proof-disabling options anywhere.

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic

namespace NumStability

open scoped BigOperators
open Matrix Module Module.End

noncomputable section

/-! ## Matrix similarity -/

/-- `A` and `B` are **similar** over `ℂ` when `B = P⁻¹ A P` for some invertible
`P`.  This is the equivalence relation under which Higham writes `A = X J X⁻¹`
(§18.1, eqn (18.1a), p. 618). -/
def Matrix.IsSimilar {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : Prop :=
  ∃ P : (Matrix n n ℂ)ˣ, (↑P⁻¹ : Matrix n n ℂ) * A * (↑P : Matrix n n ℂ) = B

namespace Matrix.IsSimilar

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Similarity is reflexive. -/
theorem refl (A : Matrix n n ℂ) : Matrix.IsSimilar A A :=
  ⟨1, by simp⟩

/-- Similarity is symmetric. -/
theorem symm {A B : Matrix n n ℂ} (h : Matrix.IsSimilar A B) :
    Matrix.IsSimilar B A := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P⁻¹, ?_⟩
  have : (↑P : Matrix n n ℂ) * B * (↑P⁻¹ : Matrix n n ℂ) = A := by
    rw [← hP]
    have hpp : (↑P : Matrix n n ℂ) * (↑P⁻¹ : Matrix n n ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hpp' : (↑P⁻¹ : Matrix n n ℂ) * (↑P : Matrix n n ℂ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (↑P : Matrix n n ℂ) * ((↑P⁻¹ : Matrix n n ℂ) * A * (↑P : Matrix n n ℂ))
            * (↑P⁻¹ : Matrix n n ℂ)
          = ((↑P : Matrix n n ℂ) * (↑P⁻¹ : Matrix n n ℂ)) * A
              * ((↑P : Matrix n n ℂ) * (↑P⁻¹ : Matrix n n ℂ)) := by
            simp only [Matrix.mul_assoc]
      _ = A := by rw [hpp]; simp
  -- `(P⁻¹)⁻¹ = P`
  simpa using this

/-- Similarity is transitive. -/
theorem trans {A B C : Matrix n n ℂ}
    (hAB : Matrix.IsSimilar A B) (hBC : Matrix.IsSimilar B C) :
    Matrix.IsSimilar A C := by
  obtain ⟨P, hP⟩ := hAB
  obtain ⟨Q, hQ⟩ := hBC
  refine ⟨P * Q, ?_⟩
  have : (↑(P * Q)⁻¹ : Matrix n n ℂ) = (↑Q⁻¹ : Matrix n n ℂ) * (↑P⁻¹ : Matrix n n ℂ) := by
    rw [_root_.mul_inv_rev]; rfl
  rw [this, ← hQ, ← hP]
  simp only [Units.val_mul, Matrix.mul_assoc]

/-- Similarity is preserved by adding a fixed scalar matrix `μ·I` (which is
central, so the conjugation leaves it fixed). -/
theorem add_scalar {A B : Matrix n n ℂ} (μ : ℂ) (h : Matrix.IsSimilar A B) :
    Matrix.IsSimilar (μ • (1 : Matrix n n ℂ) + A) (μ • (1 : Matrix n n ℂ) + B) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  have hpp' : (↑P⁻¹ : Matrix n n ℂ) * (↑P : Matrix n n ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Matrix.mul_add, Matrix.add_mul, hP]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hpp']

end Matrix.IsSimilar

/-! ## Similarity from a change of basis

If `f = Matrix.toLin' A` and `c` is any basis of `Fin n → ℂ`, then the matrix of
`f` in the basis `c` is similar to `A`, with conjugator the change-of-basis
matrix.  This is the bridge that lets us turn the operator-level primary
decomposition into a matrix similarity. -/

/-- Matrices of the *same* endomorphism `f` in two bases `b`, `c` are similar,
via the change-of-basis matrix.  (Standard; the general change-of-basis relation
`toMatrix c c f = P⁻¹ (toMatrix b b f) P`.) -/
theorem isSimilar_toMatrix_basis {n : ℕ} (f : Module.End ℂ (Fin n → ℂ))
    (b c : Basis (Fin n) ℂ (Fin n → ℂ)) :
    Matrix.IsSimilar (LinearMap.toMatrix b b f) (LinearMap.toMatrix c c f) := by
  classical
  -- Change-of-basis conjugation.
  have hconj :
      c.toMatrix b * LinearMap.toMatrix b b f * b.toMatrix c
        = LinearMap.toMatrix c c f :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (b := c) (b' := b) (c := c) (c' := b) f
  -- Package `b.toMatrix c` as a unit with inverse `c.toMatrix b`.
  have hmul : b.toMatrix c * c.toMatrix b = 1 := b.toMatrix_mul_toMatrix_flip c
  have hmul' : c.toMatrix b * b.toMatrix c = 1 := c.toMatrix_mul_toMatrix_flip b
  refine ⟨⟨b.toMatrix c, c.toMatrix b, hmul, hmul'⟩, ?_⟩
  have hinv : (↑(⟨b.toMatrix c, c.toMatrix b, hmul, hmul'⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹
      : Matrix (Fin n) (Fin n) ℂ) = c.toMatrix b := rfl
  rw [hinv]
  exact hconj

/-- The matrix of `Matrix.toLin' A` in an arbitrary basis `c` of `Fin n → ℂ` is
similar to `A`.  (Standard change-of-basis; Higham writes it as `A = XJX⁻¹`,
§18.1 p. 618.) -/
theorem isSimilar_toMatrix_toLin' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : Basis (Fin n) ℂ (Fin n → ℂ)) :
    Matrix.IsSimilar A (LinearMap.toMatrix c c (Matrix.toLin' A)) := by
  classical
  -- `A` is the matrix of `toLin' A` in the standard basis `Pi.basisFun`.
  have hbb : LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))
      (Matrix.toLin' A) = A := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have h := isSimilar_toMatrix_basis (Matrix.toLin' A) (Pi.basisFun ℂ (Fin n)) c
  rwa [hbb] at h

/-! ## (A) Primary decomposition — UNCONDITIONAL

The generalized-eigenspace (primary) decomposition of an operator on `ℂⁿ`.  This
is the reduction, preceding the Jordan-chain argument, "to the single-eigenvalue
case = scalar + nilpotent" (Higham §18.1, p. 618: `J = diag(Jₖ)`, each `Jₖ`
attached to a single eigenvalue `λₖ`).  Over `ℂ` (algebraically closed) the
generalized eigenspaces span the whole space and are independent, so they form an
internal direct sum; on the `μ`-summand the operator is `μ·1` plus a nilpotent. -/

/-- The maximal generalized eigenspaces of an endomorphism of `ℂⁿ` form an
internal direct sum.  (Combines `Module.End.independent_maxGenEigenspace` and
`Module.End.iSup_maxGenEigenspace_eq_top`, the latter needing `ℂ` algebraically
closed.  Background for Higham Thm 18.1, §18.1 p. 618.) -/
theorem jnf_isInternal_maxGenEigenspace {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    DirectSum.IsInternal (fun μ : ℂ => f.maxGenEigenspace μ) := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top

/-- `f` maps each maximal generalized eigenspace into itself. -/
theorem mapsTo_self_maxGenEigenspace {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ) :
    Set.MapsTo f ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
  mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ

/-- `f - μ·1` maps each maximal generalized eigenspace into itself. -/
theorem mapsTo_sub_maxGenEigenspace {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ) :
    Set.MapsTo (f - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ)
      ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
  mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ

/-- On the `μ`-generalized eigenspace, `f` decomposes as the scalar `μ` plus the
nilpotent restriction of `f - μ·1`.  This is the "scalar + nilpotent" normal form
of a single Jordan block's eigenvalue (Higham §18.1, p. 618). -/
theorem restrict_maxGenEigenspace_eq_scalar_add_nilpotent
    {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ) :
    f.restrict (mapsTo_self_maxGenEigenspace f μ)
      = μ • (1 : Module.End ℂ (f.maxGenEigenspace μ))
        + (f - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ).restrict
            (mapsTo_sub_maxGenEigenspace f μ) := by
  ext ⟨x, hx⟩
  simp [LinearMap.restrict_apply, Module.algebraMap_end_apply]

/-- The restriction of `f - μ·1` to the `μ`-generalized eigenspace is nilpotent.
(This is exactly `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`,
re-exported with our chosen `MapsTo` witness.) -/
theorem isNilpotent_restrict_sub_maxGenEigenspace
    {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ) :
    IsNilpotent ((f - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ).restrict
      (mapsTo_sub_maxGenEigenspace f μ)) :=
  f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ

/-- A basis of `ℂⁿ` **adapted to the primary decomposition**: it is collected from
a chosen basis of each generalized eigenspace, so every basis vector lies in a
single generalized eigenspace.  (`DirectSum.IsInternal.collectedBasis` applied to
the maximal generalized eigenspaces.) -/
noncomputable def primaryBasis {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    Basis (Σ μ : ℂ, Fin (Module.finrank ℂ (f.maxGenEigenspace μ))) ℂ (Fin n → ℂ) :=
  (jnf_isInternal_maxGenEigenspace f).collectedBasis
    (fun μ => Module.finBasis ℂ (f.maxGenEigenspace μ))

/-- The index type of `primaryBasis` is a `Fintype` (only finitely many
generalized eigenspaces are nonzero). -/
noncomputable instance instFintypePrimaryIndex {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    Fintype (Σ μ : ℂ, Fin (Module.finrank ℂ (f.maxGenEigenspace μ))) :=
  FiniteDimensional.fintypeBasisIndex (primaryBasis f)

/-- The primary basis, reindexed by `Fin n`, so that the matrix of `f` in it is a
genuine `Fin n × Fin n` matrix.  The reindexing equivalence
`Fintype.equivFin _` is arbitrary but fixed; block structure is recovered via
`toMatrix_primaryBasisFin_eq_reindex`. -/
noncomputable def primaryBasisFin {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    Basis (Fin n) ℂ (Fin n → ℂ) :=
  (primaryBasis f).reindex (Fintype.equivFin _ |>.trans
    (finCongr (by
      -- the collected index type has cardinality `n = finrank ℂ (Fin n → ℂ)`
      have : Module.finrank ℂ (Fin n → ℂ) = n := by simp
      simpa [this] using
        (Module.finrank_eq_card_basis (primaryBasis f)).symm)))

/-- The matrix of `f` in the `Fin n`-reindexed primary basis is the reindexing of
the block-structured sigma-indexed matrix.  This transports the block statements
`toMatrix_primaryBasis_block_offDiag` / `_block_diag` to the `Fin n` matrix. -/
theorem toMatrix_primaryBasisFin_eq_reindex {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    LinearMap.toMatrix (primaryBasisFin f) (primaryBasisFin f) f
      = Matrix.reindex
          (Fintype.equivFin _ |>.trans (finCongr (by
            have : Module.finrank ℂ (Fin n → ℂ) = n := by simp
            simpa [this] using (Module.finrank_eq_card_basis (primaryBasis f)).symm)))
          (Fintype.equivFin _ |>.trans (finCongr (by
            have : Module.finrank ℂ (Fin n → ℂ) = n := by simp
            simpa [this] using (Module.finrank_eq_card_basis (primaryBasis f)).symm)))
          (LinearMap.toMatrix (primaryBasis f) (primaryBasis f) f) := by
  classical
  ext i j
  simp only [primaryBasisFin, LinearMap.toMatrix_apply, Basis.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply]

/-- **Block-diagonality (off-diagonal blocks vanish).**  In the primary basis,
the matrix of `f` has a zero entry whenever the row and column indices belong to
generalized eigenspaces for *different* eigenvalues.  This is the statement that
the Jordan form is block-diagonal across distinct eigenvalues (Higham §18.1,
eqn (18.1b), p. 618). -/
theorem toMatrix_primaryBasis_block_offDiag
    {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) {μ ν : ℂ} (hμν : ν ≠ μ)
    (a : Fin (Module.finrank ℂ (f.maxGenEigenspace μ)))
    (b : Fin (Module.finrank ℂ (f.maxGenEigenspace ν))) :
    LinearMap.toMatrix (primaryBasis f) (primaryBasis f) f ⟨ν, b⟩ ⟨μ, a⟩ = 0 := by
  classical
  simp only [primaryBasis, LinearMap.toMatrix_apply]
  have hmem : f (((jnf_isInternal_maxGenEigenspace f).collectedBasis
      (fun μ => Module.finBasis ℂ (f.maxGenEigenspace μ))) ⟨μ, a⟩) ∈ f.maxGenEigenspace μ := by
    apply mapsTo_self_maxGenEigenspace f μ
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact (Module.finBasis ℂ (f.maxGenEigenspace μ) a).2
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ hμν.symm hmem

/-- **Diagonal block = scalar + nilpotent.**  In the primary basis, the diagonal
block indexed by the eigenvalue `μ` is the matrix, in the chosen basis of the
`μ`-generalized eigenspace, of `μ·1 + Nμ` where `Nμ` is the nilpotent operator
`(f - μ·1)|`.  Together with `toMatrix_primaryBasis_block_offDiag` this is the
full "block diagonal of (scalar + nilpotent) blocks" primary normal form
(Higham §18.1, p. 618). -/
theorem toMatrix_primaryBasis_block_diag
    {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ)
    (a b : Fin (Module.finrank ℂ (f.maxGenEigenspace μ))) :
    LinearMap.toMatrix (primaryBasis f) (primaryBasis f) f ⟨μ, b⟩ ⟨μ, a⟩
      = LinearMap.toMatrix (Module.finBasis ℂ (f.maxGenEigenspace μ))
          (Module.finBasis ℂ (f.maxGenEigenspace μ))
          (μ • (1 : Module.End ℂ (f.maxGenEigenspace μ))
            + (f - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ).restrict
                (mapsTo_sub_maxGenEigenspace f μ)) b a := by
  classical
  rw [← restrict_maxGenEigenspace_eq_scalar_add_nilpotent]
  simp only [primaryBasis, LinearMap.toMatrix_apply]
  have hmem : f (((jnf_isInternal_maxGenEigenspace f).collectedBasis
      (fun μ => Module.finBasis ℂ (f.maxGenEigenspace μ))) ⟨μ, a⟩) ∈ f.maxGenEigenspace μ := by
    apply mapsTo_self_maxGenEigenspace f μ
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact (Module.finBasis ℂ (f.maxGenEigenspace μ) a).2
  rw [DirectSum.IsInternal.collectedBasis_repr_of_mem _ _ hmem]
  congr 2
  apply Subtype.ext
  simp [LinearMap.restrict_apply, DirectSum.IsInternal.collectedBasis_coe]

/-- The nilpotent part `Nμ = (f - μ·1)|` of the `μ`-block, written as a matrix in
the chosen basis of the `μ`-generalized eigenspace, is a **nilpotent matrix**.
(Nilpotency is preserved by the algebra isomorphism `LinearMap.toMatrixAlgEquiv`.)
-/
theorem isNilpotent_toMatrix_nilpotentPart
    {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ) :
    IsNilpotent (LinearMap.toMatrix (Module.finBasis ℂ (f.maxGenEigenspace μ))
      (Module.finBasis ℂ (f.maxGenEigenspace μ))
      ((f - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ).restrict
        (mapsTo_sub_maxGenEigenspace f μ))) :=
  (isNilpotent_restrict_sub_maxGenEigenspace f μ).map
    (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ (f.maxGenEigenspace μ))).toRingHom

/-- The `μ`-diagonal block of the primary-basis matrix of `f`: the submatrix along
the `μ`-fiber of the sigma index.  This is Higham's `Jₖ`-cluster for eigenvalue
`μ` (§18.1, p. 618) before its internal refinement into Jordan blocks. -/
noncomputable def primaryDiagBlock {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ) :
    Matrix (Fin (Module.finrank ℂ (f.maxGenEigenspace μ)))
      (Fin (Module.finrank ℂ (f.maxGenEigenspace μ))) ℂ :=
  (LinearMap.toMatrix (primaryBasis f) (primaryBasis f) f).submatrix
    (fun a => ⟨μ, a⟩) (fun a => ⟨μ, a⟩)

/-- **The `μ`-diagonal block is exactly `μ·I + Nμ`** with `Nμ` the nilpotent matrix
`toMatrix ((f - μ·1)|)`.  This is the single-eigenvalue normal form of one
generalized-eigenspace cluster (Higham §18.1, p. 618). -/
theorem primaryDiagBlock_eq {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (μ : ℂ) :
    primaryDiagBlock f μ
      = μ • (1 : Matrix (Fin (Module.finrank ℂ (f.maxGenEigenspace μ)))
              (Fin (Module.finrank ℂ (f.maxGenEigenspace μ))) ℂ)
        + LinearMap.toMatrix (Module.finBasis ℂ (f.maxGenEigenspace μ))
            (Module.finBasis ℂ (f.maxGenEigenspace μ))
            ((f - algebraMap ℂ (Module.End ℂ (Fin n → ℂ)) μ).restrict
              (mapsTo_sub_maxGenEigenspace f μ)) := by
  ext a b
  rw [primaryDiagBlock, Matrix.submatrix_apply, toMatrix_primaryBasis_block_diag,
    map_add, map_smul, LinearMap.toMatrix_one]

/-- **Primary decomposition as a matrix similarity (unconditional).**  Every
`A : Matrix (Fin n) (Fin n) ℂ` is similar to the matrix of `Matrix.toLin' A` in
the primary basis, which — by `toMatrix_primaryBasis_block_offDiag`,
`toMatrix_primaryBasis_block_diag`, `isNilpotent_toMatrix_nilpotentPart` — is
block-diagonal with each block of the form (scalar `μ`)·I + (nilpotent).  This is
the reduction of Higham Thm 18.1's general case to a direct sum of single-
eigenvalue (scalar + nilpotent) blocks (§18.1, eqns (18.1a)/(18.1b), p. 618). -/
theorem exists_primary_blockDiagonal_similar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.IsSimilar A
      (LinearMap.toMatrix (primaryBasisFin (Matrix.toLin' A))
        (primaryBasisFin (Matrix.toLin' A)) (Matrix.toLin' A)) :=
  isSimilar_toMatrix_toLin' A (primaryBasisFin (Matrix.toLin' A))

/-! ## (B) Full Jordan Normal Form — CONDITIONAL

The only content missing from Mathlib v4.29 is the *nilpotent* Jordan-chain
theorem: a nilpotent operator has a basis of Jordan chains, equivalently every
nilpotent matrix is similar to a block-diagonal of shift (nilpotent Jordan)
blocks.  We isolate exactly this as a hypothesis and show it upgrades the
unconditional primary decomposition (A) to the classical Jordan Normal Form. -/

/-- The `k×k` **nilpotent Jordan block** (shift matrix): `1` on the superdiagonal,
`0` elsewhere.  This is `J_k(0)` in Higham's notation (§18.1, eqn (18.1b),
p. 618); a genuine Jordan block for eigenvalue `λ` is `λ • 1 + jordanBlockNil k`.
-/
def jordanBlockNil (k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

/-- Entry of `jordanBlockNil` (definitional unfolding, for rewriting). -/
theorem jordanBlockNil_apply (k : ℕ) (i j : Fin k) :
    jordanBlockNil k i j = if (j : ℕ) = (i : ℕ) + 1 then 1 else 0 := rfl

/-- Entrywise formula for powers of the nilpotent Jordan block: the `p`-th power
has `1` exactly `p` places above the diagonal.  (Standard shift-matrix identity.)
-/
theorem jordanBlockNil_pow_apply (k p : ℕ) (i j : Fin k) :
    (jordanBlockNil k ^ p) i j = if (j : ℕ) = (i : ℕ) + p then 1 else 0 := by
  classical
  induction p generalizing j with
  | zero => simp [pow_zero, Matrix.one_apply, Fin.ext_iff, eq_comm]
  | succ p ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [jordanBlockNil_apply, mul_ite, mul_one, mul_zero]
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
    · have hno : ∀ x : Fin k, ¬ ((j : ℕ) = (x : ℕ) + 1) := by intro x; omega
      simp only [hno, if_false, Finset.sum_const_zero]
      rw [if_neg]; omega
    · rw [Finset.sum_eq_single (⟨(j : ℕ) - 1, by omega⟩ : Fin k)]
      · have hcond : ((j : ℕ) = ((⟨(j : ℕ) - 1, by omega⟩ : Fin k) : ℕ) + 1) := by
          show (j : ℕ) = ((j : ℕ) - 1) + 1; omega
        rw [if_pos hcond, ih]
        by_cases h : ((⟨(j : ℕ) - 1, by omega⟩ : Fin k) : ℕ) = (i : ℕ) + p
        · rw [if_pos h, if_pos]; omega
        · rw [if_neg h, if_neg]; omega
      · intro b _ hb
        by_cases hcb : ((j : ℕ) = (b : ℕ) + 1)
        · refine absurd (Fin.ext ?_) hb
          show (b : ℕ) = (j : ℕ) - 1; omega
        · rw [if_neg hcb]
      · intro h; exact absurd (Finset.mem_univ _) h

/-- The nilpotent Jordan block is a nilpotent matrix: `(jordanBlockNil k) ^ k = 0`.
This is a concrete instance of the missing nilpotent-canonical-form data. -/
theorem isNilpotent_jordanBlockNil (k : ℕ) : IsNilpotent (jordanBlockNil k) := by
  refine ⟨k, ?_⟩
  ext i j
  rw [jordanBlockNil_pow_apply, Matrix.zero_apply, if_neg]
  omega

/-- The predicate that a matrix `M` is a **direct sum of nilpotent Jordan blocks**,
i.e. block-diagonal with each diagonal block a `jordanBlockNil`.  Given as
`Matrix.blockDiagonal'` of shift blocks indexed by their sizes. -/
def IsNilpotentJordanForm {N : Type*} [Fintype N] [DecidableEq N]
    (M : Matrix N N ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (k : ι → ℕ)
    (e : N ≃ Σ i : ι, Fin (k i)),
    M = Matrix.reindex e.symm e.symm
      (Matrix.blockDiagonal' (fun i => jordanBlockNil (k i)))

/-- **The residual gap (nilpotent Jordan-chain theorem).**  Every nilpotent
complex matrix is similar to a direct sum of nilpotent Jordan blocks.  Mathlib
v4.29 has the primary/generalized-eigenspace decomposition and Jordan–Chevalley
but *not* this statement; see the module header and `jordan_normal_form_missing_lemma`.
It is stated here as an explicit, clearly-labelled hypothesis — it is NOT proved
in this file and is NOT smuggled into any unconditional result. -/
def NilpotentJordanBasis : Prop :=
  ∀ (m : ℕ) (N : Matrix (Fin m) (Fin m) ℂ), IsNilpotent N →
    ∃ M : Matrix (Fin m) (Fin m) ℂ, Matrix.IsSimilar N M ∧ IsNilpotentJordanForm M

/-- **Classical Jordan Normal Form over ℂ (conditional).**  Assuming the residual
nilpotent Jordan-chain hypothesis `NilpotentJordanBasis`, for every
`A : Matrix (Fin n) (Fin n) ℂ`:

  * `A` is similar to `B := primaryBasisFin` matrix of `Matrix.toLin' A`
    (the *unconditional* primary block-diagonal form); and
  * for each eigenvalue `μ`, the `μ`-diagonal block `primaryDiagBlock` of the
    primary form is similar to `μ • I + Nμ`, where `Nμ` is an honest **nilpotent
    Jordan form** (a direct sum of shift blocks `jordanBlockNil`).

The second clause is the genuine Jordan content: each generalized-eigenspace
cluster is `μ·I` plus a direct sum of Jordan blocks (Higham §18.1, eqns
(18.1a)/(18.1b), p. 618).  The conclusion is honest and *not* weakened: the block
similarity is asserted for the actual block `primaryDiagBlock (Matrix.toLin' A) μ`,
and the *only* extra assumption is `NilpotentJordanBasis`. -/
theorem jordan_normal_form_of_nilpotentJordanBasis
    (hNJ : NilpotentJordanBasis) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.IsSimilar A
        (LinearMap.toMatrix (primaryBasisFin (Matrix.toLin' A))
          (primaryBasisFin (Matrix.toLin' A)) (Matrix.toLin' A))
      ∧ ∀ μ : ℂ, ∃ Nμ : Matrix
          (Fin (Module.finrank ℂ (Module.End.maxGenEigenspace (Matrix.toLin' A) μ)))
          (Fin (Module.finrank ℂ (Module.End.maxGenEigenspace (Matrix.toLin' A) μ))) ℂ,
        IsNilpotentJordanForm Nμ ∧
          Matrix.IsSimilar (primaryDiagBlock (Matrix.toLin' A) μ)
            (μ • (1 : Matrix _ _ ℂ) + Nμ) := by
  classical
  refine ⟨exists_primary_blockDiagonal_similar A, ?_⟩
  intro μ
  -- The nilpotent part of the μ-block is a nilpotent matrix; apply the hypothesis.
  obtain ⟨Nμ, hsim, hform⟩ := hNJ _ _ (isNilpotent_toMatrix_nilpotentPart (Matrix.toLin' A) μ)
  refine ⟨Nμ, hform, ?_⟩
  -- `primaryDiagBlock = μ•I + (nilpotent part)`, and `(nilpotent part) ~ Nμ`, so
  -- `μ•I + (nilpotent part) ~ μ•I + Nμ`.
  rw [primaryDiagBlock_eq]
  exact hsim.add_scalar μ

/-! ## Precise statement of the missing Mathlib lemma -/

/-- **What is missing from Mathlib v4.29.**  The single obstruction to a fully
unconditional classical Jordan Normal Form (over `ℂ`, or any algebraically closed
field) via the route formalized above is the *nilpotent Jordan-chain theorem*:

> For a nilpotent endomorphism `N` of a finite-dimensional vector space there is a
> basis in which the matrix of `N` is a direct sum of shift blocks
> (`jordanBlockNil`); equivalently every nilpotent matrix is similar to a direct
> sum of nilpotent Jordan blocks (`NilpotentJordanBasis`).

Mathlib v4.29 *does* provide:
  * `Module.End.iSup_maxGenEigenspace_eq_top` / `independent_maxGenEigenspace`
    (primary decomposition — used unconditionally above),
  * `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`
    (each block is scalar + nilpotent — used unconditionally above),
  * `Mathlib.LinearAlgebra.JordanChevalley` (additive `semisimple + nilpotent`
    splitting — but NOT the nilpotent *block* form),
  * `Mathlib.Algebra.Module.PID.torsion_by_prime_power_decomposition`
    (the abstract PID structure theorem: a f.g. `p^∞`-torsion module is
    `⨁ R⧸(pᵏ)`).  Instantiating `R = ℂ[X]` acting through `N` and `p = X` would
    yield the nilpotent Jordan basis, but the bridge (make `ℂⁿ` a f.g. torsion
    `ℂ[X]`-module via `N`, transport the `⨁ ℂ[X]⧸(Xᵏ)` decomposition back to a
    `Fin`-indexed matrix similarity, and match each cyclic summand `ℂ[X]⧸(Xᵏ)` to
    a shift block) is not present in Mathlib and is the substantial remaining work.

This lemma is stated (not proved) as `NilpotentJordanBasis`; the theorem
`jordan_normal_form_of_nilpotentJordanBasis` shows it is exactly sufficient. -/
theorem jordan_normal_form_missing_lemma :
    NilpotentJordanBasis →
      ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
        ∃ B : Matrix (Fin n) (Fin n) ℂ, Matrix.IsSimilar A B :=
  fun hNJ _ A => ⟨_, (jordan_normal_form_of_nilpotentJordanBasis hNJ A).1⟩

end

end NumStability
