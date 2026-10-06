/-
Analysis/SchurTriangulation.lean

Classical **Schur triangulation** over `ℂ`:  every complex square matrix `A` is
unitarily similar to an upper-triangular matrix `T`, i.e. there is a unitary `U`
with `Uᴴ A U = T` and `T i j = 0` for `j < i`.

Mathlib (v4.29.0) provides the spectral theorem only for *Hermitian* matrices
(`Matrix.IsHermitian.spectral_theorem`), which yields a *diagonal* form and
requires Hermitian input; it does **not** provide the general Schur form.  This
file builds it from first principles by the classical **deflation induction**:

* an eigenpair exists because `ℂ` is algebraically closed
  (`Module.End.exists_eigenvalue`, `Complex.isAlgClosed`);
* a unit eigenvector is completed to an orthonormal basis
  (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), giving a unitary
  `Q` whose first column is the eigenvector
  (`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`, the packaging used
  by `Matrix.IsHermitian.eigenvectorUnitary`);
* conjugating by `Q` zeros the first column below the diagonal, and the
  `(n-1)×(n-1)` trailing block is triangulated by the induction hypothesis and
  re-embedded via a block-diagonal unitary.

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., Section 18.1 (Schur decomposition, used for the Henrici
departure-from-normality bound (18.7)); the Schur decomposition is classical,
see e.g. Golub & Van Loan, *Matrix Computations*, Theorem 7.1.3.

Main results:
* `NumStability.schur_triangulation` — matrix Schur form over `ℂ`.
* `NumStability.schur_triangulation_diag_add_strictUpper` — the `T = D + N`
  split with `D` diagonal (the eigenvalues) and `N` strictly upper-triangular.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped BigOperators Matrix

namespace NumStability

namespace SchurAux

/-! ### Block embedding of an `n×n` matrix as the trailing block of an `(n+1)×(n+1)` one -/

/-- Embed an `n×n` matrix `B` as the trailing block of an `(n+1)×(n+1)` matrix,
    with a `1` in the `(0,0)` slot and zeros in the rest of row `0` / column `0`. -/
def embed {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => B i' j') j) i

@[simp] lemma embed_zero_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    embed B 0 0 = 1 := rfl

@[simp] lemma embed_zero_succ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    embed B 0 j.succ = 0 := rfl

@[simp] lemma embed_succ_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    embed B i.succ 0 = 0 := rfl

@[simp] lemma embed_succ_succ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    embed B i.succ j.succ = B i j := rfl

lemma embed_conjTranspose {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    (embed B)ᴴ = embed (Bᴴ) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

lemma embed_one {n : ℕ} : embed (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_inj, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

lemma embed_mul {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) :
    embed B * embed C = embed (B * C) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply]

/-- The block embedding of a unitary matrix is unitary. -/
lemma embed_mem_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    embed U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, embed_conjTranspose, embed_mul]
  rw [← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff'.mp hU), embed_one]

/-- Conjugating by `embed U` acts on the trailing block by conjugating that block by `U`. -/
lemma conj_embed_succ_succ {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((embed U)ᴴ * M * embed U) i.succ j.succ
      = (Uᴴ * (M.submatrix Fin.succ Fin.succ) * U) i j := by
  simp only [Matrix.mul_apply, embed_conjTranspose, Fin.sum_univ_succ, Matrix.submatrix_apply]
  simp [Matrix.conjTranspose_apply]

/-- The trailing entries of column `0` after conjugation by `embed U` stay zero, provided the
    original column `0` was zero below the diagonal. -/
lemma conj_embed_succ_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hcol : ∀ k : Fin n, M k.succ 0 = 0) (i : Fin n) :
    ((embed U)ᴴ * M * embed U) i.succ 0 = 0 := by
  simp only [Matrix.mul_apply, embed_conjTranspose, Fin.sum_univ_succ]
  simp [Matrix.conjTranspose_apply, hcol]

/-! ### Deflation column-zeroing from an eigenvector -/

/-- **Deflation step.**  Conjugating `A` by a unitary `Q` whose `0`-th column is a unit
    eigenvector `v` with eigenvalue `μ` produces a matrix whose `0`-th column is `μ • e₀`; in
    particular every below-diagonal entry of that column is zero. -/
lemma conj_eigenvector_col_zero {N : ℕ} (A Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (μ : ℂ)
    (v : Fin (N + 1) → ℂ) (hQu : Q ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ)
    (hQcol : ∀ i, Q i 0 = v i) (hev : A *ᵥ v = μ • v) (i : Fin (N + 1)) (hi : i ≠ 0) :
    (Qᴴ * A * Q) i 0 = 0 := by
  have hcol : (Qᴴ * A * Q) i 0 = ((Qᴴ * A * Q) *ᵥ (Pi.single 0 1)) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol]
  have hQe : Q *ᵥ (Pi.single (0 : Fin (N + 1)) 1) = v := by
    rw [Matrix.mulVec_single_one]; ext k; simp [Matrix.col_apply, hQcol k]
  have hstar : star (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * Q = 1 := hQu.1
  have hQhv : Qᴴ *ᵥ v = Pi.single (0 : Fin (N + 1)) 1 := by
    have h1 : Qᴴ *ᵥ (Q *ᵥ (Pi.single (0 : Fin (N + 1)) 1)) = Pi.single (0 : Fin (N + 1)) 1 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hstar, Matrix.one_mulVec]
    rw [hQe] at h1; exact h1
  have hfull : (Qᴴ * A * Q) *ᵥ (Pi.single (0 : Fin (N + 1)) 1)
      = μ • (Pi.single (0 : Fin (N + 1)) (1 : ℂ) : Fin (N + 1) → ℂ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQe, hev, Matrix.mulVec_smul, hQhv]
  rw [hfull, Pi.smul_apply, Pi.single_apply, if_neg hi, smul_zero]

/-! ### Unit eigenvector and its unitary completion -/

/-- Over `ℂ`, every `(n+1)×(n+1)` matrix has a unit eigenvector: an eigenvalue `μ` and a vector `w`
    of the euclidean space with `‖w‖ = 1` and `A *ᵥ w = μ • w`. -/
lemma exists_unit_eigenvector {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (μ : ℂ) (w : EuclideanSpace ℂ (Fin (n + 1))),
      ‖w‖ = 1 ∧ A *ᵥ (w : Fin (n + 1) → ℂ) = μ • (w : Fin (n + 1) → ℂ) := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.mulVecLin A)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hev : A *ᵥ v = μ • v := by
    have := hv.apply_eq_smul; simpa [Matrix.mulVecLin_apply] using this
  set vE : EuclideanSpace ℂ (Fin (n + 1)) := (WithLp.equiv 2 _).symm v with hvE
  have hvE0 : vE ≠ 0 := by
    rw [hvE]; intro h; apply hv0
    have := congrArg (WithLp.equiv 2 (Fin (n + 1) → ℂ)) h; simpa using this
  have hnorm : ‖vE‖ ≠ 0 := norm_ne_zero_iff.mpr hvE0
  refine ⟨μ, (‖vE‖⁻¹ : ℂ) • vE, ?_, ?_⟩
  · rw [norm_smul]; simp [norm_inv, hnorm]
  · have hcoe : ((‖vE‖⁻¹ : ℂ) • vE : EuclideanSpace ℂ (Fin (n + 1)))
        = (‖vE‖⁻¹ : ℂ) • v := by ext k; simp [hvE]
    rw [hcoe, Matrix.mulVec_smul, hev, smul_comm]

/-- Complete a unit vector `w` of the euclidean space to an orthonormal basis with `w` at index `0`,
    packaged as a unitary matrix `Q` whose `0`-th column is `w`. -/
lemma exists_unitary_first_col {n : ℕ} (w : EuclideanSpace ℂ (Fin (n + 1))) (hw : ‖w‖ = 1) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Q ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ ∧
      (∀ i, Q i 0 = w i) := by
  have hcard :
      Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) = Fintype.card (Fin (n + 1)) := by simp
  set f : Fin (n + 1) → EuclideanSpace ℂ (Fin (n + 1)) := fun _ => w with hf
  have horth : Orthonormal ℂ (Set.restrict {0} f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp only [Set.restrict_apply, hf]
    rw [inner_self_eq_norm_sq_to_K]; simp [hw]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨(EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  intro i
  have hb0 : b 0 = w := by simpa [hf] using hb 0 (Set.mem_singleton 0)
  have key : (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b.toBasis i 0 = b 0 i := by
    rw [Module.Basis.toMatrix_apply]
    simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr]
  rw [key, hb0]

end SchurAux

/-! ### The main theorem -/

open SchurAux in
/-- **Schur triangulation over `ℂ`.**  Every complex square matrix `A` is unitarily similar to an
    upper-triangular matrix: there exist a unitary `U` and an upper-triangular `T` (meaning
    `T i j = 0` whenever `j < i`) with `Uᴴ A U = T`.

    Proof by deflation induction on the dimension: peel off a unit eigenvector, conjugate by a
    unitary whose first column is that eigenvector (zeroing the first column below the diagonal),
    then triangulate the trailing block by the induction hypothesis and re-embed via a
    block-diagonal unitary. -/
theorem schur_triangulation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (Uᴴ * A * U = T) ∧ (∀ i j, j < i → T i j = 0) := by
  induction n with
  | zero =>
    refine ⟨1, 1ᴴ * A * 1, Submonoid.one_mem _, rfl, ?_⟩
    intro i; exact absurd i.2 (Nat.not_lt_zero _)
  | succ N ih =>
    -- 1. a unit eigenvector
    obtain ⟨μ, w, hwnorm, hwev⟩ := exists_unit_eigenvector A
    -- 2. a unitary `Q` with 0-th column `w`
    obtain ⟨Q, hQu, hQcol⟩ := exists_unitary_first_col w hwnorm
    set M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Qᴴ * A * Q with hM
    -- 3. column 0 of `M` is zero below the diagonal
    have hMcol : ∀ i : Fin (N + 1), i ≠ 0 → M i 0 = 0 := by
      intro i hi
      exact conj_eigenvector_col_zero A Q μ (fun k => w k) hQu hQcol hwev i hi
    have hMcol' : ∀ k : Fin N, M k.succ 0 = 0 := fun k => hMcol k.succ (Fin.succ_ne_zero k)
    -- 4. triangulate the trailing block by induction
    set M' : Matrix (Fin N) (Fin N) ℂ := M.submatrix Fin.succ Fin.succ with hM'
    obtain ⟨U', T', hU'u, hU'eq, hU'tri⟩ := ih M'
    -- 5. re-embed the trailing unitary and assemble
    set U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Q * embed U' with hU
    refine ⟨U, Uᴴ * A * U, ?_, rfl, ?_⟩
    · exact Submonoid.mul_mem _ hQu (embed_mem_unitary hU'u)
    · -- upper-triangularity of `Uᴴ * A * U = (embed U')ᴴ * M * embed U'`
      have hconj : Uᴴ * A * U = (embed U')ᴴ * M * embed U' := by
        rw [hU, hM, Matrix.conjTranspose_mul]
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

/-! ### Corollary: the `T = D + N` diagonal-plus-strict-upper split -/

/-- **Diagonal-plus-strictly-upper split of the Schur factor.**  The upper-triangular Schur factor
    `T` (with `Uᴴ A U = T`) decomposes as `T = D + N`, where `D` is the diagonal matrix of the
    eigenvalues (the diagonal of `T`) and `N` is strictly upper-triangular with
    `N i j = if j > i then T i j else 0`.  This is the form used for the Henrici
    departure-from-normality bound, Higham (18.7). -/
theorem schur_triangulation_diag_add_strictUpper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ)
      (D : Matrix (Fin n) (Fin n) ℂ) (N : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      (Uᴴ * A * U = T) ∧
      (∀ i j, j < i → T i j = 0) ∧
      D = Matrix.diagonal (fun i => T i i) ∧
      (∀ i j, N i j = if j > i then T i j else 0) ∧
      T = D + N := by
  obtain ⟨U, T, hUu, hUeq, hUtri⟩ := schur_triangulation A
  refine ⟨U, T, Matrix.diagonal (fun i => T i i),
    (fun i j => if j > i then T i j else 0), hUu, hUeq, hUtri, rfl, fun _ _ => rfl, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  rcases lt_trichotomy j i with h | h | h
  · -- j < i : below diagonal, T i j = 0, and both terms zero
    rw [hUtri i j h]
    simp [Ne.symm (ne_of_lt h), not_lt.mpr (le_of_lt h)]
  · -- j = i : diagonal
    subst h; simp
  · -- j > i : strictly upper
    simp [Ne.symm (ne_of_gt h), h]

end NumStability
