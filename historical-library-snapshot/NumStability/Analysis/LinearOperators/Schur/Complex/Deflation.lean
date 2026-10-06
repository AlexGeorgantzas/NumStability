import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Analysis.LinearOperators.Schur.Complex.Deflation

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




















































/-! ### Corollary: the `T = D + N` diagonal-plus-strict-upper split -/





























end NumStability
