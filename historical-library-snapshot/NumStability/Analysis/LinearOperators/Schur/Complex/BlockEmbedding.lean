import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Analysis.LinearOperators.Schur.Complex.BlockEmbedding

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

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























/-! ### Unit eigenvector and its unitary completion -/















































end SchurAux

/-! ### The main theorem -/




















































/-! ### Corollary: the `T = D + N` diagonal-plus-strict-upper split -/





























end NumStability
