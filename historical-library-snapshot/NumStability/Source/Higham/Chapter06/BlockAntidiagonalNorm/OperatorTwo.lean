import NumStability.Source.Higham.Chapter06.Asides.UnitaryInvariance

/-!
# Higham Chapter 6: block-antidiagonal operator-2 norm

Source correspondence for the operator-2 reduction of the block-antidiagonal
matrix built from a matrix and its adjoint.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-! ### (iv) Block antidiagonal `p`-norm identity (`p = 2`)

Higham §6.2, p. 113 (unnumbered display after (6.21)):
`‖[[0, A], [Aᴴ, 0]]‖_p = max(‖A‖_p, ‖A‖_q)`, `1/p + 1/q = 1`.  For `p = 2`
we have `q = 2`, so the right side is `max(‖A‖₂, ‖A‖₂) = ‖A‖₂`.

We assemble the reduction using the repo/Mathlib `l2` operator-norm API.  Write
`H := [[0, A], [Aᴴ, 0]]` (Mathlib `fromBlocks`, indexed by `Fin m ⊕ Fin n`).
The two structural facts below are proved outright; the norm identity is then
derived from the C*-identity `‖H‖² = ‖HᴴH‖`, the Hermitian symmetry `Hᴴ = H`,
the block-diagonal square `H² = diag(AAᴴ, AᴴA)`, and `‖AAᴴ‖ = ‖AᴴA‖ = ‖A‖²`,
reducing everything to the single standard fact that the `l2` operator norm of a
block-diagonal matrix is the max of the block norms (`hblock`), which is absent
from Mathlib. -/

/-- **The block antidiagonal matrix `[[0,A],[Aᴴ,0]]` is Hermitian.** -/
theorem ch6aside_blockAntidiag_hermitian {m n : ℕ} (A : CMatrix m n) :
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ))ᴴ =
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.fromBlocks_conjTranspose]
  simp

/-- **Square of the block antidiagonal matrix is block diagonal:**
    `[[0,A],[Aᴴ,0]]² = diag(A Aᴴ, Aᴴ A)`. -/
theorem ch6aside_blockAntidiag_sq {m n : ℕ} (A : CMatrix m n) :
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ)) *
      (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ)) =
      Matrix.fromBlocks
        (complexCMatrixAsMatrix A * (complexCMatrixAsMatrix A)ᴴ)
        (0 : Matrix (Fin m) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin m) ℂ)
        ((complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A) := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **Block antidiagonal `2`-norm identity** (Higham §6.2, p. 113, at `p = 2`):
    `‖[[0,A],[Aᴴ,0]]‖₂ = ‖A‖₂`.  The reduction is proved in full; the sole
    residual is `hblock`, the standard "`l2` norm of a block-diagonal matrix is
    the max of the block norms", which Mathlib does not provide. -/
theorem ch6aside_blockAntidiag_op2_eq {m n : ℕ} (A : CMatrix m n)
    (hblock :
      ‖Matrix.fromBlocks (complexCMatrixAsMatrix A * (complexCMatrixAsMatrix A)ᴴ)
          (0 : Matrix (Fin m) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin m) ℂ)
          ((complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A)‖ =
        max ‖complexCMatrixAsMatrix A * (complexCMatrixAsMatrix A)ᴴ‖
          ‖(complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A‖) :
    ‖Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (complexCMatrixAsMatrix A)
        ((complexCMatrixAsMatrix A)ᴴ) (0 : Matrix (Fin n) (Fin n) ℂ)‖ =
      complexMatrixOp2 A := by
  set Am := complexCMatrixAsMatrix A with hAm
  set H := Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) Am Amᴴ
    (0 : Matrix (Fin n) (Fin n) ℂ) with hH
  rw [ch6aside_op2_eq_l2, ← hAm]
  -- `‖A Aᴴ‖ = ‖Aᴴ A‖ = ‖A‖²`.
  have hAHA : ‖Amᴴ * Am‖ = ‖Am‖ * ‖Am‖ :=
    Matrix.l2_opNorm_conjTranspose_mul_self Am
  have hAAH : ‖Am * Amᴴ‖ = ‖Am‖ * ‖Am‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (Amᴴ)
    rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
  -- `‖H‖² = ‖HᴴH‖ = ‖H²‖ = ‖diag(AAᴴ, AᴴA)‖ = max(‖A‖²,‖A‖²) = ‖A‖²`.
  have hHH : ‖H‖ * ‖H‖ = ‖Am‖ * ‖Am‖ := by
    have hcstar : ‖Hᴴ * H‖ = ‖H‖ * ‖H‖ := Matrix.l2_opNorm_conjTranspose_mul_self H
    have hherm : Hᴴ = H := by
      rw [hH, Matrix.fromBlocks_conjTranspose]; simp
    have hsq : H * H = Matrix.fromBlocks (Am * Amᴴ)
        (0 : Matrix (Fin m) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin m) ℂ) (Amᴴ * Am) := by
      rw [hH, Matrix.fromBlocks_multiply]; simp
    rw [hherm, hsq, hblock, hAAH, hAHA, max_self] at hcstar
    exact hcstar.symm
  have hsq2 : ‖H‖ ^ 2 = ‖Am‖ ^ 2 := by rw [sq, sq]; exact hHH
  exact (sq_eq_sq₀ (norm_nonneg H) (norm_nonneg Am)).mp hsq2

end NumStability
