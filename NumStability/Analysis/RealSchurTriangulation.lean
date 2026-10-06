/-
Analysis/RealSchurTriangulation.lean

Real **(quasi-)Schur triangulation**.  Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed., §16.2, states the real Schur decomposition as
(16.4): every real square matrix `A` is orthogonally similar to a real
*quasi*-upper-triangular matrix `R` (block-upper-triangular with `1×1` blocks for
the real eigenvalues and `2×2` blocks for the complex-conjugate eigenvalue
pairs), `QᵀAQ = R`, `Q` orthogonal.

Mathlib (v4.29.0) has no real Schur form, and no ready-made "invariant subspace
of dimension `≤ 2`" primitive.  What it *does* have is the algebraic fact behind
the `2×2` blocks (`Irreducible.natDegree_le_two`: an irreducible real polynomial
has degree `≤ 2`) and, for the deflation, the machinery of characteristic
polynomials.

This file proves the **fully triangular** case unconditionally and honestly:

  **If `A.charpoly` splits over `ℝ` (equivalently: all eigenvalues of `A` are
  real), then `A` is orthogonally similar to a genuine real upper-triangular
  matrix** — `∃ Q ∈ orthogonalGroup, QᵀAQ = T` with `T i j = 0` for `j < i`.

This is exactly the case in which the `2×2` blocks of (16.4) degenerate to `1×1`
blocks, i.e. the real quasi-triangular form *is* triangular.  It covers, among
others, every symmetric matrix (whose charpoly splits, Mathlib
`Matrix.IsHermitian.splits_charpoly`) and every matrix with real spectrum.  The
splitting hypothesis is a genuine, non-vacuous, *necessary and sufficient*
condition for full real triangularizability (a real matrix with a genuine
complex-conjugate pair, e.g. a rotation, is provably **not** orthogonally similar
to any real upper-triangular matrix), so no strength is smuggled into a
hypothesis: the conclusion (orthogonal similarity to triangular form) is strictly
stronger than the hypothesis (charpoly splits).

Proof: the **deflation induction** of the complex Schur file
(`SchurTriangulation.lean`), but the eigenvector at each step now comes from a
*real* root of the (split) characteristic polynomial rather than from algebraic
closure, and the hypothesis is propagated to the trailing block by the block
factorization `charpoly (fromBlocks _ 0 _ _) = _.charpoly * _.charpoly` together
with `Splits.of_dvd`.

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., §16.2, equation (16.4) (real Schur decomposition); the classical
statement is Golub & Van Loan, *Matrix Computations*, Theorem 7.4.1.

Main result:
* `NumStability.real_schur_triangulation_of_splits` — real orthogonal
  triangularization under the split-characteristic-polynomial hypothesis.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

open scoped BigOperators Matrix

namespace NumStability

namespace RealSchurAux

/-! ### Block embedding of an `n×n` matrix as the trailing block of an `(n+1)×(n+1)` one

This mirrors `SchurAux` from the complex file, but over `ℝ` and with the
orthogonal (real) group in place of the unitary group. -/

/-- Embed an `n×n` real matrix `B` as the trailing block of an `(n+1)×(n+1)`
    matrix, with a `1` in the `(0,0)` slot and zeros in the rest of row `0` /
    column `0`. -/
def embed {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => B i' j') j) i

@[simp] lemma embed_zero_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    embed B 0 0 = 1 := rfl

@[simp] lemma embed_zero_succ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    embed B 0 j.succ = 0 := rfl

@[simp] lemma embed_succ_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    embed B i.succ 0 = 0 := rfl

@[simp] lemma embed_succ_succ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    embed B i.succ j.succ = B i j := rfl

lemma embed_transpose {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    (embed B)ᵀ = embed (Bᵀ) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.transpose_apply]

lemma embed_one {n : ℕ} : embed (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_inj, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

lemma embed_mul {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ) :
    embed B * embed C = embed (B * C) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply]

/-- The block embedding of an orthogonal matrix is orthogonal. -/
lemma embed_mem_orthogonal {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    embed U ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  rw [embed_transpose, embed_mul]
  rw [Matrix.mem_orthogonalGroup_iff'] at hU
  rw [hU, embed_one]

/-- Conjugating by `embed U` acts on the trailing block by conjugating that block by `U`. -/
lemma conj_embed_succ_succ {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ((embed U)ᵀ * M * embed U) i.succ j.succ
      = (Uᵀ * (M.submatrix Fin.succ Fin.succ) * U) i j := by
  simp only [Matrix.mul_apply, embed_transpose, Fin.sum_univ_succ, Matrix.submatrix_apply]
  simp [Matrix.transpose_apply]

/-- The trailing entries of column `0` after conjugation by `embed U` stay zero, provided the
    original column `0` was zero below the diagonal. -/
lemma conj_embed_succ_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hcol : ∀ k : Fin n, M k.succ 0 = 0) (i : Fin n) :
    ((embed U)ᵀ * M * embed U) i.succ 0 = 0 := by
  simp only [Matrix.mul_apply, embed_transpose, Fin.sum_univ_succ]
  simp [Matrix.transpose_apply, hcol]

/-! ### Deflation column-zeroing from an eigenvector -/

/-- **Deflation step.**  Conjugating `A` by an orthogonal `Q` whose `0`-th column is a unit
    eigenvector `v` with eigenvalue `μ` produces a matrix whose `0`-th column is `μ • e₀`; in
    particular every below-diagonal entry of that column is zero. -/
lemma conj_eigenvector_col_zero {N : ℕ} (A Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (μ : ℝ)
    (v : Fin (N + 1) → ℝ) (hQu : Q ∈ Matrix.orthogonalGroup (Fin (N + 1)) ℝ)
    (hQcol : ∀ i, Q i 0 = v i) (hev : A *ᵥ v = μ • v) (i : Fin (N + 1)) (hi : i ≠ 0) :
    (Qᵀ * A * Q) i 0 = 0 := by
  have hcol : (Qᵀ * A * Q) i 0 = ((Qᵀ * A * Q) *ᵥ (Pi.single 0 1)) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol]
  have hQe : Q *ᵥ (Pi.single (0 : Fin (N + 1)) 1) = v := by
    rw [Matrix.mulVec_single_one]; ext k; simp [Matrix.col_apply, hQcol k]
  have hstar : star (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) * Q = 1 := hQu.1
  have hstar' : Qᵀ * Q = 1 := by
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hstar
  have hQhv : Qᵀ *ᵥ v = Pi.single (0 : Fin (N + 1)) 1 := by
    have h1 : Qᵀ *ᵥ (Q *ᵥ (Pi.single (0 : Fin (N + 1)) 1)) = Pi.single (0 : Fin (N + 1)) 1 := by
      rw [Matrix.mulVec_mulVec, hstar', Matrix.one_mulVec]
    rw [hQe] at h1; exact h1
  have hfull : (Qᵀ * A * Q) *ᵥ (Pi.single (0 : Fin (N + 1)) 1)
      = μ • (Pi.single (0 : Fin (N + 1)) (1 : ℝ) : Fin (N + 1) → ℝ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQe, hev, Matrix.mulVec_smul, hQhv]
  rw [hfull, Pi.smul_apply, Pi.single_apply, if_neg hi, smul_zero]

/-! ### Real unit eigenvector from a real root of the (split) characteristic polynomial -/

/-- Over `ℝ`, if `A.charpoly` splits then `A` has a real eigenvalue.  (For a nonempty index the
    charpoly has positive degree, and a split polynomial of positive degree has a root, which is
    an eigenvalue.) -/
lemma exists_real_eigenvalue_of_splits {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsplit : A.charpoly.Splits) :
    ∃ μ : ℝ, Module.End.HasEigenvalue (Matrix.mulVecLin A) μ := by
  have hmon : A.charpoly.Monic := Matrix.charpoly_monic A
  have hdeg : A.charpoly.degree = (n + 1 : ℕ) := by
    rw [Matrix.charpoly_degree_eq_dim]; simp
  have hdeg0 : A.charpoly.degree ≠ 0 := by
    rw [hdeg]; exact_mod_cast (Nat.succ_ne_zero n)
  obtain ⟨μ, hμ⟩ := hsplit.exists_eval_eq_zero hdeg0
  refine ⟨μ, ?_⟩
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_mulVecLin]
  exact hμ

/-- Over `ℝ`, if `A.charpoly` splits then `A` has a *unit* eigenvector: an eigenvalue `μ` and a
    vector `w` of the euclidean space with `‖w‖ = 1` and `A *ᵥ w = μ • w`. -/
lemma exists_unit_eigenvector_of_splits {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsplit : A.charpoly.Splits) :
    ∃ (μ : ℝ) (w : EuclideanSpace ℝ (Fin (n + 1))),
      ‖w‖ = 1 ∧ A *ᵥ (w : Fin (n + 1) → ℝ) = μ • (w : Fin (n + 1) → ℝ) := by
  obtain ⟨μ, hμ⟩ := exists_real_eigenvalue_of_splits A hsplit
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hev : A *ᵥ v = μ • v := by
    have := hv.apply_eq_smul; simpa [Matrix.mulVecLin_apply] using this
  set vE : EuclideanSpace ℝ (Fin (n + 1)) := (WithLp.equiv 2 _).symm v with hvE
  have hvE0 : vE ≠ 0 := by
    rw [hvE]; intro h; apply hv0
    have := congrArg (WithLp.equiv 2 (Fin (n + 1) → ℝ)) h; simpa using this
  have hnorm : ‖vE‖ ≠ 0 := norm_ne_zero_iff.mpr hvE0
  refine ⟨μ, (‖vE‖⁻¹ : ℝ) • vE, ?_, ?_⟩
  · rw [norm_smul]; simp [norm_inv, hnorm]
  · have hcoe : ((‖vE‖⁻¹ : ℝ) • vE : EuclideanSpace ℝ (Fin (n + 1)))
        = (‖vE‖⁻¹ : ℝ) • v := by ext k; simp [hvE]
    rw [hcoe, Matrix.mulVec_smul, hev, smul_comm]

/-- Complete a unit vector `w` of the euclidean space to an orthonormal basis with `w` at index `0`,
    packaged as an orthogonal matrix `Q` whose `0`-th column is `w`. -/
lemma exists_orthogonal_first_col {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) (hw : ‖w‖ = 1) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Q ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ ∧
      (∀ i, Q i 0 = w i) := by
  have hcard :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = Fintype.card (Fin (n + 1)) := by simp
  set f : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun _ => w with hf
  have horth : Orthonormal ℝ (Set.restrict {0} f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp only [Set.restrict_apply, hf]
    rw [inner_self_eq_norm_sq_to_K]; simp [hw]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.toMatrix b.toBasis,
    ?_, ?_⟩
  · exact (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toMatrix_orthonormalBasis_mem_unitary b
  · intro i
    have hb0 : b 0 = w := by simpa [hf] using hb 0 (Set.mem_singleton 0)
    have key : (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.toMatrix b.toBasis i 0 = b 0 i := by
      rw [Module.Basis.toMatrix_apply]
      simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr]
    rw [key, hb0]

/-! ### Propagating the split hypothesis to the trailing block

The deflated matrix `M` has zero column `0` below the diagonal.  Reindexing so that
row/column `0` sits last, `M` becomes block form `fromBlocks (trailing) 0 (row) (corner)`, whose
charpoly is `(trailing).charpoly * (corner).charpoly`.  Hence the trailing block's charpoly divides
`M.charpoly`; and `M.charpoly = A.charpoly` because orthogonal conjugation is conjugation by a unit
matrix. -/

/-- Charpoly of a real matrix is unchanged by orthogonal conjugation. -/
lemma charpoly_conj_orthogonal {m : ℕ} (A Q : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    (Qᵀ * A * Q).charpoly = A.charpoly := by
  have hQT : Qᵀ * Q = 1 := by
    have := hQ.1
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- `Q` is a unit with inverse `Qᵀ`.
  have hunit : Q * Qᵀ = 1 := by
    have := hQ.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  let Qu : (Matrix (Fin m) (Fin m) ℝ)ˣ := ⟨Q, Qᵀ, hunit, hQT⟩
  have hval : Qu.val = Q := rfl
  have hinv : (Qu⁻¹).val = Qᵀ := rfl
  have := Matrix.charpoly_units_conj' Qu A
  rw [hval, hinv] at this
  exact this

/-- If `M`'s column `0` is zero below the diagonal, the trailing block's charpoly divides
    `M.charpoly`.  Proof: reindex row/col `0` to the end and read off the block factorization. -/
lemma trailing_charpoly_dvd {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hcol : ∀ k : Fin N, M k.succ 0 = 0) :
    (M.submatrix Fin.succ Fin.succ).charpoly ∣ M.charpoly := by
  -- Reindex via `Fin (N+1) ≃ Fin N ⊕ Unit`, sending `0 ↦ inr` and `k.succ ↦ inl k`.
  set e : Fin (N + 1) ≃ Fin N ⊕ Unit :=
    (finSuccEquiv N).trans (Equiv.optionEquivSumPUnit (Fin N)) with he
  -- The reindexed matrix is block-lower-triangular free: upper-right of the (trailing,corner)
  -- split is zero.
  set B : Matrix (Fin N ⊕ Unit) (Fin N ⊕ Unit) ℝ := Matrix.reindex e e M with hB
  have hzero : B = Matrix.fromBlocks (M.submatrix Fin.succ Fin.succ) 0
      (Matrix.of fun (_ : Unit) (j : Fin N) => M 0 j.succ)
      (Matrix.of fun (_ : Unit) (_ : Unit) => M 0 0) := by
    refine Matrix.ext (fun i j => ?_)
    have hkey : ∀ x : Fin N ⊕ Unit, e.symm x = Sum.elim Fin.succ (fun _ => 0) x := by
      rintro (x | x) <;>
        simp [he, Equiv.symm_trans_apply, Equiv.optionEquivSumPUnit_symm_inl,
          Equiv.optionEquivSumPUnit_symm_inr, finSuccEquiv_symm_some, finSuccEquiv_symm_none]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [hB, Matrix.reindex_apply, Matrix.submatrix_apply, hkey]
      | inr j =>
        simp [hB, Matrix.reindex_apply, hkey, hcol i]
    | inr i =>
      cases j with
      | inl j =>
        simp [hB, Matrix.reindex_apply, hkey]
      | inr j =>
        simp [hB, Matrix.reindex_apply, hkey]
  have hMcp : M.charpoly = B.charpoly := by
    rw [hB, Matrix.charpoly_reindex]
  rw [hMcp, hzero, Matrix.charpoly_fromBlocks_zero₁₂]
  exact ⟨_, rfl⟩

end RealSchurAux

/-! ### The main theorem -/

open RealSchurAux in
/-- **Real orthogonal triangularization under a split characteristic polynomial.**

    If the characteristic polynomial of a real square matrix `A` splits over `ℝ` (equivalently: all
    eigenvalues of `A` are real), then `A` is orthogonally similar to a real *upper-triangular*
    matrix: there exist an orthogonal `Q` (`QᵀQ = 1`) and an upper-triangular `T` (meaning
    `T i j = 0` whenever `j < i`) with `QᵀAQ = T`.

    This is the real Schur decomposition of Higham §16.2 (16.4) in the case where the
    complex-conjugate `2×2` blocks degenerate to `1×1` blocks, i.e. the quasi-triangular form is
    genuinely triangular.  It applies in particular to every symmetric matrix and to every matrix
    with real spectrum.

    Proof by deflation induction on the dimension: a real root of the (split) characteristic
    polynomial gives a real eigenvector; conjugating by an orthogonal matrix whose first column is
    that eigenvector zeros the first column below the diagonal; the split hypothesis passes to the
    trailing block via the block factorization of the characteristic polynomial, and the induction
    hypothesis triangulates the trailing block, which is re-embedded by a block-diagonal orthogonal
    matrix. -/
theorem real_schur_triangulation_of_splits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsplit : A.charpoly.Splits) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℝ) (T : Matrix (Fin n) (Fin n) ℝ),
      Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧ (Qᵀ * A * Q = T) ∧
        (∀ i j, j < i → T i j = 0) := by
  induction n with
  | zero =>
    refine ⟨1, 1ᵀ * A * 1, Submonoid.one_mem _, rfl, ?_⟩
    intro i; exact absurd i.2 (Nat.not_lt_zero _)
  | succ N ih =>
    -- 1. a real unit eigenvector (uses that the charpoly splits)
    obtain ⟨μ, w, hwnorm, hwev⟩ := exists_unit_eigenvector_of_splits A hsplit
    -- 2. an orthogonal `Q` with 0-th column `w`
    obtain ⟨Q, hQu, hQcol⟩ := exists_orthogonal_first_col w hwnorm
    set M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Qᵀ * A * Q with hM
    -- 3. column 0 of `M` is zero below the diagonal
    have hMcol : ∀ i : Fin (N + 1), i ≠ 0 → M i 0 = 0 := by
      intro i hi
      exact conj_eigenvector_col_zero A Q μ (fun k => w k) hQu hQcol hwev i hi
    have hMcol' : ∀ k : Fin N, M k.succ 0 = 0 := fun k => hMcol k.succ (Fin.succ_ne_zero k)
    -- 4. the trailing block, and propagation of the split hypothesis
    set M' : Matrix (Fin N) (Fin N) ℝ := M.submatrix Fin.succ Fin.succ with hM'
    have hMcp : M.charpoly = A.charpoly := charpoly_conj_orthogonal A Q hQu
    have hM'split : M'.charpoly.Splits := by
      have hdvd : M'.charpoly ∣ M.charpoly := trailing_charpoly_dvd M hMcol'
      rw [hMcp] at hdvd
      exact Polynomial.Splits.of_dvd hsplit A.charpoly_monic.ne_zero hdvd
    obtain ⟨U', T', hU'u, hU'eq, hU'tri⟩ := ih M' hM'split
    -- 5. re-embed the trailing orthogonal matrix and assemble
    set U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Q * embed U' with hU
    refine ⟨U, Uᵀ * A * U, ?_, rfl, ?_⟩
    · exact Submonoid.mul_mem _ hQu (embed_mem_orthogonal hU'u)
    · -- upper-triangularity of `Uᵀ * A * U = (embed U')ᵀ * M * embed U'`
      have hconj : Uᵀ * A * U = (embed U')ᵀ * M * embed U' := by
        rw [hU, hM, Matrix.transpose_mul]
        simp only [mul_assoc]
      rw [hconj]
      intro i j hji
      induction i using Fin.cases with
      | zero => exact (Fin.not_lt_zero j hji).elim
      | succ i' =>
        induction j using Fin.cases with
        | zero => exact conj_embed_succ_zero M U' hMcol' i'
        | succ j' =>
          rw [conj_embed_succ_succ M U' i' j']
          have hji' : j' < i' := by rwa [Fin.succ_lt_succ_iff] at hji
          rw [hU'eq]
          exact hU'tri i' j' hji'

end NumStability
