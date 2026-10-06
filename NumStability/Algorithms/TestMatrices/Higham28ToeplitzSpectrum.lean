/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28ToeplitzGeneral

namespace NumStability

open scoped BigOperators ComplexConjugate
open Matrix Polynomial

noncomputable section

private noncomputable def complexToeplitzSineMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.map (higham9_12_sineMatrix n) Complex.ofReal

private theorem complexToeplitzSineMatrix_transpose_mul
    {n : ℕ} (hn : 0 < n) :
    (complexToeplitzSineMatrix n).transpose *
        complexToeplitzSineMatrix n = 1 := by
  classical
  ext i j
  have h := (higham9_sineMatrix_isOrthogonal hn).col_orthonormal i j
  have hc := congrArg Complex.ofReal h
  by_cases hij : i = j
  · subst j
    simpa [complexToeplitzSineMatrix, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply] using hc
  · simpa [complexToeplitzSineMatrix, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, hij] using hc

private theorem complexToeplitzSineMatrix_mul_transpose
    {n : ℕ} (hn : 0 < n) :
    complexToeplitzSineMatrix n *
        (complexToeplitzSineMatrix n).transpose = 1 := by
  classical
  ext i j
  have h := (higham9_sineMatrix_isOrthogonal hn).row_orthonormal i j
  have hc := congrArg Complex.ofReal h
  by_cases hij : i = j
  · subst j
    simpa [complexToeplitzSineMatrix, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply] using hc
  · simpa [complexToeplitzSineMatrix, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, hij] using hc

private theorem complexToeplitzSineMatrix_column
    {n : ℕ} (k : Fin n) :
    (fun i : Fin n => complexToeplitzSineMatrix n i k) =
      (Real.sqrt (2 / ((n : ℝ) + 1)) : ℂ) •
        (fun i : Fin n => (toeplitzSineVector n k i : ℂ)) := by
  funext i
  simp only [complexToeplitzSineMatrix, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul]
  unfold higham9_12_sineMatrix toeplitzSineVector
  push_cast
  congr 2

private theorem complexSymmetricToeplitz_scaled_sine_eigenpair
    {n : ℕ} (s d : ℂ) (k : Fin n) :
    Matrix.mulVec (complexTridiagonalToeplitz n s d s)
        (fun i => complexToeplitzSineMatrix n i k) =
      (d + 2 * s *
          (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
            (n + 1 : ℕ)) : ℂ)) •
        (fun i => complexToeplitzSineMatrix n i k) := by
  rw [complexToeplitzSineMatrix_column]
  rw [Matrix.mulVec_smul, complexSymmetricToeplitz_sine_eigenpair]
  simp [smul_smul, mul_comm]

private theorem complexSymmetricToeplitz_mul_sineMatrix
    {n : ℕ} (s d : ℂ) :
    complexTridiagonalToeplitz n s d s * complexToeplitzSineMatrix n =
      complexToeplitzSineMatrix n *
        Matrix.diagonal (fun k : Fin n =>
          d + 2 * s *
            (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
              (n + 1 : ℕ)) : ℂ)) := by
  classical
  ext i k
  have h := congrFun (complexSymmetricToeplitz_scaled_sine_eigenpair s d k) i
  rw [Matrix.mul_apply]
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    mul_comm] using h

private theorem complexSymmetricToeplitz_diagonalization
    {n : ℕ} (hn : 0 < n) (s d : ℂ) :
    complexTridiagonalToeplitz n s d s =
      complexToeplitzSineMatrix n *
        Matrix.diagonal (fun k : Fin n =>
          d + 2 * s *
            (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
              (n + 1 : ℕ)) : ℂ)) *
        (complexToeplitzSineMatrix n).transpose := by
  calc
    complexTridiagonalToeplitz n s d s =
        complexTridiagonalToeplitz n s d s * 1 := by rw [Matrix.mul_one]
    _ = complexTridiagonalToeplitz n s d s *
        (complexToeplitzSineMatrix n *
          (complexToeplitzSineMatrix n).transpose) := by
      rw [complexToeplitzSineMatrix_mul_transpose hn]
    _ = (complexTridiagonalToeplitz n s d s *
          complexToeplitzSineMatrix n) *
        (complexToeplitzSineMatrix n).transpose := by
      rw [Matrix.mul_assoc]
    _ = _ := by rw [complexSymmetricToeplitz_mul_sineMatrix]

private theorem complexSymmetricToeplitz_charpoly
    {n : ℕ} (s d : ℂ) :
    (complexTridiagonalToeplitz n s d s).charpoly =
      ∏ k : Fin n,
        (X - C (d + 2 * s *
          (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
            (n + 1 : ℕ)) : ℂ))) := by
  by_cases hn : 0 < n
  · let Q := complexToeplitzSineMatrix n
    let D : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.diagonal (fun k : Fin n =>
        d + 2 * s *
          (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
            (n + 1 : ℕ)) : ℂ))
    have hdiag : complexTridiagonalToeplitz n s d s = Q * D * Q.transpose := by
      simpa [Q, D] using complexSymmetricToeplitz_diagonalization hn s d
    have hQtQ : Q.transpose * Q = 1 := by
      simpa [Q] using complexToeplitzSineMatrix_transpose_mul hn
    rw [hdiag]
    calc
      (Q * D * Q.transpose).charpoly =
          (Q * (D * Q.transpose)).charpoly := by rw [Matrix.mul_assoc]
      _ = (D * Q.transpose * Q).charpoly :=
        Matrix.charpoly_mul_comm Q (D * Q.transpose)
      _ = D.charpoly := by rw [Matrix.mul_assoc, hQtQ, Matrix.mul_one]
      _ = _ := by
        dsimp [D]
        rw [Matrix.charpoly_diagonal]
  · have hn0 : n = 0 := by omega
    subst n
    simp [Matrix.charpoly_isEmpty]

private noncomputable def complexToeplitzScaling
    (n : ℕ) (q : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => q ^ i.val)

private noncomputable def complexToeplitzScalingInv
    (n : ℕ) (q : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (q ^ i.val)⁻¹)

private theorem complexToeplitzScaling_mul_inv
    (n : ℕ) (q : ℂ) (hq : q ≠ 0) :
    complexToeplitzScaling n q * complexToeplitzScalingInv n q = 1 := by
  classical
  rw [complexToeplitzScaling, complexToeplitzScalingInv,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [pow_ne_zero _ hq]
  · simp [hij]

private theorem complexToeplitzScalingInv_mul
    (n : ℕ) (q : ℂ) (hq : q ≠ 0) :
    complexToeplitzScalingInv n q * complexToeplitzScaling n q = 1 := by
  classical
  rw [complexToeplitzScaling, complexToeplitzScalingInv,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [pow_ne_zero _ hq]
  · simp [hij]

private theorem complexTridiagonalToeplitz_mul_scaling
    {n : ℕ} (c d e q s : ℂ)
    (heq : e * q = s) (hcq : c = q * s) :
    complexTridiagonalToeplitz n c d e * complexToeplitzScaling n q =
      complexToeplitzScaling n q * complexTridiagonalToeplitz n s d s := by
  classical
  ext i j
  rw [complexToeplitzScaling, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    simp [complexTridiagonalToeplitz]
    ring
  · by_cases hsuper : i.val + 1 = j.val
    · have hsub : ¬j.val + 1 = i.val := by omega
      simp only [complexTridiagonalToeplitz, if_neg hij, if_pos hsuper,
        if_neg hsub]
      rw [show j.val = i.val + 1 by omega, pow_succ]
      linear_combination q ^ i.val * heq
    · by_cases hsub : j.val + 1 = i.val
      · simp only [complexTridiagonalToeplitz, if_neg hij,
          if_neg hsuper, if_pos hsub]
        rw [show i.val = j.val + 1 by omega, pow_succ]
        rw [hcq]
        ring
      · simp [complexTridiagonalToeplitz, hij, hsuper, hsub]

private theorem complexTridiagonalToeplitz_charpoly_eq_symmetric_of_ne
    {n : ℕ} (c d e : ℂ) (hc : c ≠ 0) (he : e ≠ 0)
    (s : ℂ) (hsq : s * s = c * e) :
    (complexTridiagonalToeplitz n c d e).charpoly =
      (complexTridiagonalToeplitz n s d s).charpoly := by
  let q := s / e
  have hce : c * e ≠ 0 := mul_ne_zero hc he
  have hs : s ≠ 0 := by
    intro hs0
    rw [hs0, zero_mul] at hsq
    exact hce hsq.symm
  have hq : q ≠ 0 := div_ne_zero hs he
  have heq : e * q = s := by
    dsimp [q]
    field_simp
  have hcq : c = q * s := by
    dsimp [q]
    rw [div_mul_eq_mul_div, hsq]
    field_simp
  let D := complexToeplitzScaling n q
  let Dinv := complexToeplitzScalingInv n q
  let A := complexTridiagonalToeplitz n c d e
  let B := complexTridiagonalToeplitz n s d s
  have hDDinv : D * Dinv = 1 := by
    simpa [D, Dinv] using complexToeplitzScaling_mul_inv n q hq
  have hAD : A * D = D * B := by
    simpa [A, B, D] using
      complexTridiagonalToeplitz_mul_scaling c d e q s heq hcq
  have hconj : A = D * B * Dinv := by
    calc
      A = A * 1 := by rw [Matrix.mul_one]
      _ = A * (D * Dinv) := by rw [hDDinv]
      _ = (A * D) * Dinv := by rw [Matrix.mul_assoc]
      _ = (D * B) * Dinv := by rw [hAD]
  change A.charpoly = B.charpoly
  rw [hconj]
  calc
    (D * B * Dinv).charpoly = (D * (B * Dinv)).charpoly := by
      rw [Matrix.mul_assoc]
    _ = (B * Dinv * D).charpoly :=
      Matrix.charpoly_mul_comm D (B * Dinv)
    _ = B.charpoly := by
      rw [Matrix.mul_assoc]
      have hDinvD : Dinv * D = 1 := by
        simpa [D, Dinv] using complexToeplitzScalingInv_mul n q hq
      rw [hDinvD, Matrix.mul_one]

private theorem complexTridiagonalToeplitz_upperTriangular_of_sub_zero
    (n : ℕ) (d e : ℂ) :
    (complexTridiagonalToeplitz n 0 d e).BlockTriangular id := by
  intro i j hji
  change j.val < i.val at hji
  have hij : i ≠ j := by
    intro hij
    subst j
    exact (lt_irrefl i) hji
  have hsuper : ¬i.val + 1 = j.val := by omega
  simp [complexTridiagonalToeplitz, hij, hsuper]

private theorem complexTridiagonalToeplitz_transpose_upperTriangular_of_super_zero
    (n : ℕ) (c d : ℂ) :
    (complexTridiagonalToeplitz n c d 0).transpose.BlockTriangular id := by
  intro i j hji
  change j.val < i.val at hji
  have hji_ne : j ≠ i := ne_of_lt hji
  have hsub : ¬i.val + 1 = j.val := by omega
  simp [Matrix.transpose_apply, complexTridiagonalToeplitz, hji_ne, hsub]

private theorem complexTridiagonalToeplitz_charpoly_of_sub_zero
    (n : ℕ) (d e : ℂ) :
    (complexTridiagonalToeplitz n 0 d e).charpoly =
      (X - C d) ^ n := by
  rw [Matrix.charpoly_of_upperTriangular _
    (complexTridiagonalToeplitz_upperTriangular_of_sub_zero n d e)]
  simp [complexTridiagonalToeplitz, Finset.prod_const]

private theorem complexTridiagonalToeplitz_charpoly_of_super_zero
    (n : ℕ) (c d : ℂ) :
    (complexTridiagonalToeplitz n c d 0).charpoly =
      (X - C d) ^ n := by
  rw [← Matrix.charpoly_transpose]
  rw [Matrix.charpoly_of_upperTriangular _
    (complexTridiagonalToeplitz_transpose_upperTriangular_of_super_zero n c d)]
  simp [Matrix.transpose_apply, complexTridiagonalToeplitz,
    Finset.prod_const]

/-- Higham, Section 28.5, p. 522: the unrestricted tridiagonal Toeplitz
characteristic polynomial is the product over the entire printed
`k = 1:n` list.  The formula is over `ℂ`, so it also covers `c*e < 0`;
when `c*e = 0`, all `n` identical factors are retained. -/
theorem complexTridiagonalToeplitz_p522_unrestricted_charpoly
    (n : ℕ) (c d e : ℝ) :
    (complexTridiagonalToeplitz n c d e).charpoly =
      ∏ k : Fin n,
        (X - C (generalToeplitzComplexEigenvalue n c d e k)) := by
  by_cases hc : c = 0
  · subst c
    change
      (complexTridiagonalToeplitz n 0 (d : ℂ) (e : ℂ)).charpoly = _
    rw [complexTridiagonalToeplitz_charpoly_of_sub_zero]
    simp [generalToeplitzComplexEigenvalue, realProductComplexSqrt,
      Finset.prod_const]
  · by_cases he : e = 0
    · subst e
      change
        (complexTridiagonalToeplitz n (c : ℂ) (d : ℂ) 0).charpoly = _
      rw [complexTridiagonalToeplitz_charpoly_of_super_zero]
      simp [generalToeplitzComplexEigenvalue, realProductComplexSqrt,
        Finset.prod_const]
    · let s : ℂ := realProductComplexSqrt c e
      have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
      have heC : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he
      have hsq : s * s = (c : ℂ) * (e : ℂ) := by
        dsimp [s]
        rw [realProductComplexSqrt_sq, Complex.ofReal_mul]
      rw [complexTridiagonalToeplitz_charpoly_eq_symmetric_of_ne
        (c : ℂ) (d : ℂ) (e : ℂ) hcC heC s hsq]
      rw [complexSymmetricToeplitz_charpoly]
      rfl

/-- Source-facing form for the original real Toeplitz matrix mapped to
`ℂ`: its characteristic polynomial is exactly the printed `n`-factor
product, including all repeated factors. -/
theorem tridiagonalToeplitz_p522_unrestricted_charpoly
    (n : ℕ) (c d e : ℝ) :
    ((tridiagonalToeplitz n c d e).map Complex.ofReal).charpoly =
      ∏ k : Fin n,
        (X - C (generalToeplitzComplexEigenvalue n c d e k)) := by
  rw [← complexTridiagonalToeplitz_ofReal]
  exact complexTridiagonalToeplitz_p522_unrestricted_charpoly n c d e

/-- Exact algebraic-multiplicity form of the unrestricted p. 522 list. -/
theorem tridiagonalToeplitz_p522_unrestricted_roots_charpoly
    (n : ℕ) (c d e : ℝ) :
    ((tridiagonalToeplitz n c d e).map Complex.ofReal).charpoly.roots =
      Multiset.map (generalToeplitzComplexEigenvalue n c d e)
        Finset.univ.val := by
  rw [tridiagonalToeplitz_p522_unrestricted_charpoly]
  rw [Polynomial.roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr (by
      intro k hk
      exact Polynomial.X_sub_C_ne_zero _)

/-- In either triangular zero case, the unrestricted formula specializes
to the repeated factor `(X-d)^n`, not merely to one occurrence of `d`. -/
theorem tridiagonalToeplitz_p522_charpoly_of_product_zero
    (n : ℕ) (c d e : ℝ) (hce : c * e = 0) :
    ((tridiagonalToeplitz n c d e).map Complex.ofReal).charpoly =
      (X - C (d : ℂ)) ^ n := by
  rcases mul_eq_zero.mp hce with hc | he
  · subst c
    rw [← complexTridiagonalToeplitz_ofReal]
    exact complexTridiagonalToeplitz_charpoly_of_sub_zero n (d : ℂ) (e : ℂ)
  · subst e
    rw [← complexTridiagonalToeplitz_ofReal]
    exact complexTridiagonalToeplitz_charpoly_of_super_zero n (c : ℂ) (d : ℂ)

theorem tridiagonalToeplitz_p522_roots_charpoly_of_product_zero
    (n : ℕ) (c d e : ℝ) (hce : c * e = 0) :
    ((tridiagonalToeplitz n c d e).map Complex.ofReal).charpoly.roots =
      Multiset.replicate n (d : ℂ) := by
  rw [tridiagonalToeplitz_p522_charpoly_of_product_zero n c d e hce,
    Polynomial.roots_pow, Polynomial.roots_X_sub_C,
    Multiset.nsmul_singleton]

end

end NumStability
