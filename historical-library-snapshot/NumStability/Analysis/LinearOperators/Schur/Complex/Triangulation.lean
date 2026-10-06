import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import NumStability.Analysis.LinearOperators.Schur.Complex.BlockEmbedding
import NumStability.Analysis.LinearOperators.Schur.Complex.Deflation

/-!
# Analysis.LinearOperators.Schur.Complex.Triangulation

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
































































/-! ### Deflation column-zeroing from an eigenvector -/























/-! ### Unit eigenvector and its unitary completion -/















































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
