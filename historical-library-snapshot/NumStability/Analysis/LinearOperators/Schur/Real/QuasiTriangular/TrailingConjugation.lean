import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import NumStability.Analysis.LinearOperators.Schur.Real.InvariantSubspace.TwoByTwo
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.Basic
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.BlockEmbedding
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.OrthogonalFrame
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.Reindex

/-!
# Analysis.LinearOperators.Schur.Real.QuasiTriangular.TrailingConjugation

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

/-
Analysis/RealQuasiSchur.lean

The **full real quasi-triangular (quasi-)Schur decomposition**.  Higham,
*Accuracy and Stability of Numerical Algorithms*, 2nd ed., §16.2, equation
(16.4): every real square matrix `A` is orthogonally similar to a real
*block*-upper-triangular matrix `R` whose diagonal blocks have size `1` (real
eigenvalues) or `2` (complex-conjugate eigenvalue pairs):

  `∃ Q ∈ orthogonalGroup, Qᵀ A Q = R`, with `R` block-upper-triangular
  (zeros strictly below the `≤ 2` diagonal-block structure).

This closes the residual obstruction recorded at the end of
`Analysis/RealInvariantSubspace.lean`: iterating the real "peel-1-or-2" primitive
into the FULL orthogonal quasi-triangular form via the *variable-`d`*
(`d ∈ {1, 2}`) orthogonal deflation induction.

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., §16.2, equation (16.4) (real Schur decomposition); the classical
statement is Golub & Van Loan, *Matrix Computations*, Theorem 7.4.1.
-/






open scoped BigOperators Matrix
open Module

namespace NumStability














namespace RealQuasiSchurAux

/-! ### The quasi-upper-triangular predicate (Higham (16.4))

A matrix `R : Matrix (Fin n) (Fin n) ℝ` is *quasi-upper-triangular* when there is
a block-assignment `p : Fin n → ℕ` such that:
* `p` is monotone — so each block `p⁻¹(c)` is a contiguous interval;
* every block has at most `2` elements — the diagonal blocks are `1×1` or `2×2`;
* `R i j = 0` whenever row `i` lies in a strictly later block than column `j`
  (`p j < p i`) — i.e. everything strictly below the block diagonal vanishes.

This is precisely the real quasi-triangular Schur form of Higham §16.2 (16.4):
block-upper-triangular with `1×1`/`2×2` diagonal blocks.  In the degenerate case
`p = id` (all blocks of size `1`) it reduces to ordinary upper-triangularity
`R i j = 0` for `j < i`. -/





/-! ### Block-diagonal orthogonal re-embedding over a sum index

Re-embedding an `m×m` orthogonal matrix `U` as the trailing block of a
`(Fin d ⊕ Fin m)`-indexed matrix with an identity `d×d` leading block, used to
lift the trailing-block reduction of Higham §16.2 (16.4) to the full space. -/

variable {d m : ℕ}





































/-! ### Deflation: an invariant leading block zeros the lower-left block

If the first `d` columns of an orthogonal `Q` span an `A`-invariant subspace,
then conjugating `A` by `Q` zeros the block strictly below those columns. -/

variable {n : ℕ}






























































/-! ### Orthogonal frame whose leading `d` columns span the invariant subspace

From a `d`-dimensional real invariant subspace `W` we build an orthogonal `Q`
whose first `d` columns form an orthonormal basis of `W`; this is the orthonormal
extension `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` that the
variable-`d` deflation of Higham §16.2 (16.4) consumes. -/


































































































































































































































































































































































































































































/-! ### Reindexing helpers: conjugation and orthogonality transport

Transporting an orthogonal conjugation `Xᵀ A X` along an index equivalence
`e : Fin n ≃ ι`.  `Matrix.reindex e e` is an algebra isomorphism, so it commutes
with products, transposes and units, hence carries orthogonal conjugations to
orthogonal conjugations. -/



































/-! ### The order-compatible splitting equivalence `Fin n ≃ Fin d ⊕ Fin m`

For `d + m = n`, the equivalence `splitEquiv` sends the first `d` indices to the
`Fin d` summand and the rest to the `Fin m` summand, order-preservingly. -/



































































/-! ### Block conjugation by the re-embedded trailing orthogonal matrix -/

/-- Conjugating a block matrix `[[P, Bu], [0, D]]` (zero lower-left) by the block
    embedding `[[1,0],[0,U]]` yields `[[P, Bu·U], [0, Uᵀ·D·U]]`; in particular the
    lower-left stays zero and the trailing block becomes `Uᵀ D U`.  The block-form
    deflation re-embedding for the variable-`d` step of Higham §16.2 (16.4). -/
lemma conj_embedBlock_eq {d m : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (Bu : Matrix (Fin d) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    (embedBlock (d := d) U)ᵀ * Matrix.fromBlocks P Bu 0 D * embedBlock (d := d) U
      = Matrix.fromBlocks P (Bu * U) 0 (Uᵀ * D * U) := by
  unfold embedBlock
  rw [Matrix.fromBlocks_transpose]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Re-embedding a trailing orthogonal factor does not change entries whose row
    and column are both in the leading block. -/
lemma embedBlock_conj_apply_inl_inl {d m : ℕ}
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (a b : Fin d) :
    ((embedBlock (d := d) U)ᵀ * M * embedBlock (d := d) U) (Sum.inl a) (Sum.inl b) =
      M (Sum.inl a) (Sum.inl b) := by
  simp [embedBlock, Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply]

/-- Re-embedding a trailing orthogonal factor turns the trailing block into the
    conjugated trailing block. -/
lemma embedBlock_conj_apply_inr_inr {d m : ℕ}
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m) :
    ((embedBlock (d := d) U)ᵀ * M * embedBlock (d := d) U) (Sum.inr a) (Sum.inr b) =
      (Uᵀ * M.toBlocks₂₂ * U) a b := by
  simp [embedBlock, Matrix.fromBlocks, Matrix.toBlocks₂₂, Matrix.mul_apply]

/-- Trailing recursive conjugation leaves entries in the leading `d = 2` block
    unchanged after transporting back from the split index. -/
lemma trailing_conj_preserves_leading_entry
    {m n : ℕ} (hnm : 2 + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {i j : Fin n} (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) :
    let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := 2) U)
    (Qfullᵀ * A * Qfull) i j = (Qᵀ * A * Q) i j := by
  let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
  let Q' : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := Matrix.reindex e e Q
  let A' : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := Matrix.reindex e e A
  let E : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := embedBlock (d := 2) U
  let V : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ := Q' * E
  have hQfull :
      (Matrix.reindex e.symm e.symm V)ᵀ * A * Matrix.reindex e.symm e.symm V =
        Matrix.reindex e.symm e.symm (Vᵀ * A' * V) := by
    have h := reindex_conj e.symm A' V
    rw [show Matrix.reindex e.symm e.symm A' = A by
      simp [A']] at h
    exact h.symm
  have hV :
      Vᵀ * A' * V = Eᵀ * (Q'ᵀ * A' * Q') * E := by
    dsimp [V]
    rw [Matrix.transpose_mul]
    simp only [mul_assoc]
  have hQ' : Q'ᵀ * A' * Q' = Matrix.reindex e e (Qᵀ * A * Q) := by
    exact (reindex_conj e A Q).symm
  have hei : e i = Sum.inl ⟨(i : ℕ), hi⟩ := splitEquiv_eq_inl_of_lt hnm i hi
  have hej : e j = Sum.inl ⟨(j : ℕ), hj⟩ := splitEquiv_eq_inl_of_lt hnm j hj
  have hsym_i : e.symm (Sum.inl ⟨(i : ℕ), hi⟩) = i := by
    rw [← hei]
    exact e.symm_apply_apply i
  have hsym_j : e.symm (Sum.inl ⟨(j : ℕ), hj⟩) = j := by
    rw [← hej]
    exact e.symm_apply_apply j
  change (((Matrix.reindex e.symm e.symm V)ᵀ * A *
      Matrix.reindex e.symm e.symm V) i j = (Qᵀ * A * Q) i j)
  rw [hQfull]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  change (Vᵀ * A' * V) (e i) (e j) = (Qᵀ * A * Q) i j
  rw [hei, hej, hV, embedBlock_conj_apply_inl_inl, hQ']
  simp [Matrix.reindex_apply, hsym_i, hsym_j]

/-- Trailing recursive conjugation transports entries in the trailing block to
    the conjugated recursive block after splitting by an arbitrary leading
    dimension `d`.  This is the entrywise algebra needed before recursive
    spectral certificates can be threaded through the Schur construction. -/
lemma trailing_conj_preserves_trailing_entry
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {i j : Fin n} {a b : Fin m}
    (hi : (i : ℕ) = d + (a : ℕ)) (hj : (j : ℕ) = d + (b : ℕ)) :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    (Qfullᵀ * A * Qfull) i j =
      (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b := by
  let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
  let Q' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e Q
  let A' : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.reindex e e A
  let E : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := embedBlock (d := d) U
  let V : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Q' * E
  have hQfull :
      (Matrix.reindex e.symm e.symm V)ᵀ * A * Matrix.reindex e.symm e.symm V =
        Matrix.reindex e.symm e.symm (Vᵀ * A' * V) := by
    have h := reindex_conj e.symm A' V
    rw [show Matrix.reindex e.symm e.symm A' = A by
      simp [A']] at h
    exact h.symm
  have hV :
      Vᵀ * A' * V = Eᵀ * (Q'ᵀ * A' * Q') * E := by
    dsimp [V]
    rw [Matrix.transpose_mul]
    simp only [mul_assoc]
  have hQ' : Q'ᵀ * A' * Q' = Matrix.reindex e e (Qᵀ * A * Q) := by
    exact (reindex_conj e A Q).symm
  have hei : e i = Sum.inr a := splitEquiv_eq_inr_of_eq_add hnm i a hi
  have hej : e j = Sum.inr b := splitEquiv_eq_inr_of_eq_add hnm j b hj
  change (((Matrix.reindex e.symm e.symm V)ᵀ * A *
      Matrix.reindex e.symm e.symm V) i j =
        (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b)
  rw [hQfull]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  change (Vᵀ * A' * V) (e i) (e j) =
    (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b
  rw [hei, hej, hV, embedBlock_conj_apply_inr_inr, hQ']

/-- The ordered `2 x 2` block on a trailing pair is exactly the corresponding
    principal block of the recursively conjugated trailing Schur factor. -/
lemma principalTwoBlock_trailing_conj_transports_trailing_two
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n} {a b : Fin m}
    (hp : (p : ℕ) = d + (a : ℕ))
    (hq : (q : ℕ) = d + (b : ℕ)) :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
      NumStability.principalTwoBlock
        (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hp hp
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hp hq
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hq hp
  · exact trailing_conj_preserves_trailing_entry hnm A Q U hq hq

/-- No-real-eigenline and negative-discriminant certificates for a trailing
    recursive `2 x 2` block transport back through the full re-embedded Schur
    factor. -/
lemma trailing_twoBlock_spectral_preserved_after_trailing_conj
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n} {a b : Fin m}
    (hp : (p : ℕ) = d + (a : ℕ))
    (hq : (q : ℕ) = d + (b : ℕ))
    (hno :
      let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock
          (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b)) :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
      ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
        4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := d) U)
  have hblock :
      NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
        NumStability.principalTwoBlock
          (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b :=
    principalTwoBlock_trailing_conj_transports_trailing_two hnm A Q U hp hq
  have hno' :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) := by
    rw [hblock]
    simpa [e] using hno
  exact ⟨hno',
    NumStability.principalTwoBlock_disc_neg_of_matrixNoRealEigenline
      (Qfullᵀ * A * Qfull) p q hno'⟩

/-- A recursive trailing adjacent same-block spectral certificate lifts to the
    parent block map after re-embedding the trailing Schur factor. -/
lemma trailing_twoBlock_spectral_with_parentBlockMap_after_trailing_conj
    {d m n : ℕ} (hnm : d + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    (p' : Fin m → ℕ) {a b : Fin m}
    (hab : (b : ℕ) = (a : ℕ) + 1)
    (hsame : p' a = p' b)
    (hspectral :
      let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
      HasRealQuasiSchurTwoBlockSpectral
        (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) p') :
    let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := d) U)
    let pmap : Fin n → ℕ :=
      fun i => Sum.elim (fun _ : Fin d => 0) (fun c : Fin m => p' c + 1) (e i)
    let p : Fin n := e.symm (Sum.inr a)
    let q : Fin n := e.symm (Sum.inr b)
    (q : ℕ) = (p : ℕ) + 1 ∧
      pmap p = pmap q ∧
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
      ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
        4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  let e : Fin n ≃ Fin d ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := d) U)
  let pmap : Fin n → ℕ :=
    fun i => Sum.elim (fun _ : Fin d => 0) (fun c : Fin m => p' c + 1) (e i)
  let p : Fin n := e.symm (Sum.inr a)
  let q : Fin n := e.symm (Sum.inr b)
  have hpval : (p : ℕ) = d + (a : ℕ) := by
    have hsum : splitEquiv hnm p = Sum.inr a := by
      dsimp [p, e]
      exact (splitEquiv hnm).apply_symm_apply (Sum.inr a)
    exact (splitEquiv_inr_val hnm hsum).symm
  have hqval : (q : ℕ) = d + (b : ℕ) := by
    have hsum : splitEquiv hnm q = Sum.inr b := by
      dsimp [q, e]
      exact (splitEquiv hnm).apply_symm_apply (Sum.inr b)
    exact (splitEquiv_inr_val hnm hsum).symm
  have hadj : (q : ℕ) = (p : ℕ) + 1 := by
    omega
  have hsame_parent : pmap p = pmap q := by
    dsimp [pmap, p, q, e]
    simp [hsame]
  have htrail :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock
          (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b) ∧
        ((Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a a -
            (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) b b) ^ 2 +
          4 * (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) a b *
            (Uᵀ * (Matrix.reindex e e (Qᵀ * A * Q)).toBlocks₂₂ * U) b a < 0 := by
    simpa [e] using hspectral a b hab hsame
  have hfull :
      NumStability.MatrixNoRealEigenline
          (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
        ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
          4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
    simpa [e, Qfull, p, q] using
      trailing_twoBlock_spectral_preserved_after_trailing_conj
        hnm A Q U hpval hqval htrail.1
  exact ⟨hadj, hsame_parent, hfull.1, hfull.2⟩

/-- The principal leading `2 x 2` block is unchanged when the trailing recursive
    conjugation is re-embedded. -/
lemma principalTwoBlock_trailing_conj_preserves_leading_two
    {m n : ℕ} (hnm : 2 + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n}
    (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 1) :
    let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := 2) U)
    NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
      NumStability.principalTwoBlock (Qᵀ * A * Q) p q := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)
  · exact trailing_conj_preserves_leading_entry hnm A Q U (by omega) (by omega)

/-- No-real-eigenline and negative-discriminant certificates for the leading
    `2 x 2` block survive the trailing recursive conjugation. -/
lemma leading_twoBlock_spectral_preserved_after_trailing_conj
    {m n : ℕ} (hnm : 2 + m = n)
    (A Q : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    {p q : Fin n}
    (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 1)
    (hno :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qᵀ * A * Q) p q)) :
    let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
    let Qfull : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.reindex e.symm e.symm
        (Matrix.reindex e e Q * embedBlock (d := 2) U)
    NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
      ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
        4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := 2) U)
  have hblock :
      NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q =
        NumStability.principalTwoBlock (Qᵀ * A * Q) p q :=
    principalTwoBlock_trailing_conj_preserves_leading_two hnm A Q U hp hq
  have hno' :
      NumStability.MatrixNoRealEigenline
        (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) := by
    rw [hblock]
    exact hno
  exact ⟨hno',
    NumStability.principalTwoBlock_disc_neg_of_matrixNoRealEigenline
      (Qfullᵀ * A * Qfull) p q hno'⟩

/-- A two-dimensional no-real-eigenline peel branch can be framed, recursively
    re-embedded through an orthogonal trailing factor, and still expose the
    leading `2 x 2` no-real-eigenline/negative-discriminant certificate. -/
lemma exists_orthogonal_frame_two_principalBlock_spectral_after_trailing_conj
    {m n : ℕ} (hnm : 2 + m = n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (W : Submodule ℝ (Fin n → ℝ))
    (hd : finrank ℝ W = 2)
    (hWinv : ∀ w ∈ W, A.mulVecLin w ∈ W)
    (hWno :
      ∀ w ∈ W, w ≠ 0 →
        ¬ ∃ nu : ℝ, A *ᵥ w = nu • w)
    (U : Matrix (Fin m) (Fin m) ℝ)
    (hUorth : U ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    ∃ (Q Qfull : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n),
      Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        Qfull ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        (p : ℕ) = 0 ∧
        (q : ℕ) = 1 ∧
        Submodule.span ℝ
          (Set.range
            (fun c : {c : Fin n // (c : ℕ) < 2} => (fun k => Q k c.1))) = W ∧
        (let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
         Qfull =
          Matrix.reindex e.symm e.symm
            (Matrix.reindex e e Q * embedBlock (d := 2) U)) ∧
        NumStability.MatrixNoRealEigenline
          (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
        ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
          4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 := by
  obtain ⟨Q, p, q, hQ, hp, hq, hQspan, hno, _hdisc⟩ :=
    exists_orthogonal_frame_two_principalBlock_noRealEigenline_disc_neg
      A W hd hWinv hWno
  let e : Fin n ≃ Fin 2 ⊕ Fin m := splitEquiv hnm
  let Qfull : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := 2) U)
  have hQfullorth : Qfull ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    change Matrix.reindex e.symm e.symm
      (Matrix.reindex e e Q * embedBlock (d := 2) U) ∈ Matrix.orthogonalGroup (Fin n) ℝ
    exact reindex_mem_orthogonal e.symm
      (Submonoid.mul_mem _
        (reindex_mem_orthogonal e hQ)
        (embedBlock_mem_orthogonal (d := 2) hUorth))
  have hspectral :
      NumStability.MatrixNoRealEigenline
          (NumStability.principalTwoBlock (Qfullᵀ * A * Qfull) p q) ∧
        ((Qfullᵀ * A * Qfull) p p - (Qfullᵀ * A * Qfull) q q) ^ 2 +
          4 * (Qfullᵀ * A * Qfull) p q * (Qfullᵀ * A * Qfull) q p < 0 :=
    leading_twoBlock_spectral_preserved_after_trailing_conj
      hnm A Q U hp hq hno
  exact ⟨Q, Qfull, p, q, hQ, hQfullorth, hp, hq, hQspan, rfl,
    hspectral.1, hspectral.2⟩

/-! ### The variable-`d` orthogonal deflation induction (Higham (16.4)) -/

































































































































































































































































































































































































































































end RealQuasiSchurAux

/-! ### The main theorems (Higham §16.2 (16.4)) -/
















































































end NumStability
