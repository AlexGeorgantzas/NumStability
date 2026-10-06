import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Equation35.HymanBlockFactorization.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation36.HymanDeterminant.MatrixInversion

/-!
# Chapter14 Problem14 HymanDeterminant MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    exact determinant hinge used in the Hyman backward-error proof.  If `T`
    is upper triangular, `DeltaT` has zero diagonal, and the componentwise
    bound `|DeltaT| <= gamma |T|` holds, then the bound forces `DeltaT` to
    have zero entries below the diagonal, so `T + DeltaT` has the same
    triangular determinant product as `T`. -/
theorem higham14_problem14_14_det_upper_add_zero_diag_of_abs_bound {n : ℕ}
    (T DeltaT : Matrix (Fin n) (Fin n) ℝ) (gamma : ℝ)
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|) :
    Matrix.det (T + DeltaT) = Matrix.det T := by
  have hDeltaLower : ∀ i j : Fin n, j < i → DeltaT i j = 0 := by
    intro i j hji
    have hTij : T i j = 0 := hTupper hji
    have hbound := hDeltaBound i j
    rw [hTij, abs_zero, mul_zero] at hbound
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  have hUpperSum : (T + DeltaT).BlockTriangular id := by
    intro i j hji
    simp [Matrix.add_apply, hTupper hji, hDeltaLower i j hji]
  rw [Matrix.det_of_upperTriangular hUpperSum, Matrix.det_of_upperTriangular hTupper]
  apply Finset.prod_congr rfl
  intro i _
  simp [Matrix.add_apply, hDeltaDiag i]

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    exact Hyman determinant wrapper after perturbing the triangular solve
    block.  The determinant-invariance hinge above keeps the factor `det T`
    even though the Hyman block uses `T + DeltaT` and its inverse certificate. -/
theorem higham14_problem14_14_hyman_det_cyclic_block_of_upper_add_zero_diag
    {n : ℕ}
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gamma : ℝ)
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    Matrix.det (higham14_hymanBlockMatrix (T + DeltaT) y h η) =
      Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  rw [higham14_eq14_36_hyman_det_cyclic_block
    (T + DeltaT) TpertInv y h η hTpertInv]
  rw [higham14_problem14_14_det_upper_add_zero_diag_of_abs_bound
    T DeltaT gamma hTupper hDeltaDiag hDeltaBound]

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    original-matrix Hyman determinant wrapper after perturbing the triangular
    solve block.  This combines the perturbed cyclic-block determinant formula
    with the signed row-permutation wrapper for the original Hessenberg matrix. -/
theorem higham14_problem14_14_hyman_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gamma : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hH :
      higham14_hymanBlockMatrix (T + DeltaT) y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    Matrix.det H =
      (Equiv.Perm.sign σ : ℝ) *
        Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  have horig :=
    higham14_eq14_36_hyman_det_original_of_row_permutation
      H (T + DeltaT) TpertInv y h η σ hH hTpertInv
  have hdet :
      Matrix.det (T + DeltaT) = Matrix.det T :=
    higham14_problem14_14_det_upper_add_zero_diag_of_abs_bound
      T DeltaT gamma hTupper hDeltaDiag hDeltaBound
  simpa [hdet] using horig

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    absolute-value form of the perturbed original-matrix Hyman determinant
    wrapper.  The row-permutation sign disappears from the magnitude bound. -/
theorem higham14_problem14_14_abs_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gamma : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hH :
      higham14_hymanBlockMatrix (T + DeltaT) y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    |Matrix.det H| =
      |Matrix.det T| * |higham14_hymanSchur h y TpertInv η| := by
  have hdet :=
    higham14_problem14_14_hyman_det_original_of_upper_add_zero_diag
      H T DeltaT TpertInv y h η gamma σ hH hTupper hDeltaDiag hDeltaBound
      hTpertInv
  have hsign_abs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  rw [hdet, abs_mul, abs_mul, hsign_abs, one_mul]

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    packaged original-matrix backward-error target for Hyman's method.  Once a
    later floating-point analysis supplies a componentwise-bounded `DeltaH`
    whose permuted block is the perturbed Hyman block, the exact determinant
    statement follows from the determinant wrappers above. -/
theorem higham14_problem14_14_exists_deltaH_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hDeltaHCert :
      ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (H + DeltaH) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      Matrix.det (H + DeltaH) =
        (Equiv.Perm.sign σ : ℝ) *
          Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  rcases hDeltaHCert with ⟨DeltaH, hDeltaHBound, hBlock⟩
  refine ⟨DeltaH, hDeltaHBound, ?_⟩
  exact
    higham14_problem14_14_hyman_det_original_of_upper_add_zero_diag
      (H + DeltaH) T DeltaT TpertInv y h η gammaT σ
      hBlock hTupper hDeltaTDiag hDeltaTBound hTpertInv

/-- Problem 14.14 absolute-value backward-error target for Hyman's method.
    This is the existential `DeltaH` companion to the signed determinant
    package above. -/
theorem higham14_problem14_14_exists_deltaH_abs_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hDeltaHCert :
      ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (H + DeltaH) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      |Matrix.det (H + DeltaH)| =
        |Matrix.det T| * |higham14_hymanSchur h y TpertInv η| := by
  rcases
    higham14_problem14_14_exists_deltaH_det_original_of_upper_add_zero_diag
      H T DeltaT TpertInv y h η gammaT gammaH σ hDeltaHCert
      hTupper hDeltaTDiag hDeltaTBound hTpertInv
    with ⟨DeltaH, hDeltaHBound, hdet⟩
  refine ⟨DeltaH, hDeltaHBound, ?_⟩
  have hsign_abs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  rw [hdet, abs_mul, abs_mul, hsign_abs, one_mul]

/-- Problem 14.14 support: diagonal similarity used to model the optional
    scaling of Hyman's Hessenberg matrix. -/
noncomputable def higham14_problem14_14_diagonalSimilarity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal d * A * Matrix.diagonal (fun i => (d i)⁻¹)

/-- Problem 14.14 support: transport a perturbation on the diagonally scaled
    matrix back to the original matrix. -/
noncomputable def higham14_problem14_14_diagonalUnscalePerturbation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (DeltaScaled : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (d i)⁻¹) * DeltaScaled * Matrix.diagonal d

theorem higham14_problem14_14_diagonalSimilarity_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) (i j : ι) :
    higham14_problem14_14_diagonalSimilarity d A i j =
      d i * A i j * (d j)⁻¹ := by
  simp [higham14_problem14_14_diagonalSimilarity, Matrix.mul_apply,
    Matrix.diagonal_apply, Finset.sum_ite_eq]

theorem higham14_problem14_14_diagonalUnscalePerturbation_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (DeltaScaled : Matrix ι ι ℝ) (i j : ι) :
    higham14_problem14_14_diagonalUnscalePerturbation d DeltaScaled i j =
      (d i)⁻¹ * DeltaScaled i j * d j := by
  simp [higham14_problem14_14_diagonalUnscalePerturbation, Matrix.mul_apply,
    Matrix.diagonal_apply, Finset.sum_ite_eq]

/-- Diagonal similarity preserves determinants.  This is the exact algebraic
    core behind the diagonal-scaling clause in Problem 14.14. -/
theorem higham14_problem14_14_det_diagonalSimilarity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ)
    (hd : ∀ i : ι, d i ≠ 0) :
    Matrix.det (higham14_problem14_14_diagonalSimilarity d A) =
      Matrix.det A := by
  have hprod :
      (∏ i : ι, d i) * (∏ i : ι, (d i)⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => mul_inv_cancel₀ (hd i))
  rw [higham14_problem14_14_diagonalSimilarity, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  calc
    (∏ i : ι, d i) * Matrix.det A * (∏ i : ι, (d i)⁻¹)
        = ((∏ i : ι, d i) * (∏ i : ι, (d i)⁻¹)) * Matrix.det A := by
            ring
    _ = Matrix.det A := by
            rw [hprod]
            ring

/-- A componentwise perturbation bound on the diagonally scaled matrix
    transports back to the same relative componentwise bound on the original
    matrix. -/
theorem higham14_problem14_14_unscaled_delta_bound_of_scaled
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (H DeltaScaled : Matrix ι ι ℝ) (gamma : ℝ)
    (hd : ∀ i : ι, d i ≠ 0)
    (hDeltaScaled : ∀ i j : ι,
      |DeltaScaled i j| ≤
        gamma * |higham14_problem14_14_diagonalSimilarity d H i j|) :
    ∀ i j : ι,
      |higham14_problem14_14_diagonalUnscalePerturbation d DeltaScaled i j| ≤
        gamma * |H i j| := by
  intro i j
  have hleft_nonneg : 0 ≤ |(d i)⁻¹| := abs_nonneg _
  have hright_nonneg : 0 ≤ |d j| := abs_nonneg _
  have hmul_left :=
    mul_le_mul_of_nonneg_left (hDeltaScaled i j) hleft_nonneg
  have hmul := mul_le_mul_of_nonneg_right hmul_left hright_nonneg
  have hdi : |(d i)⁻¹| * |d i| = 1 := by
    rw [abs_inv]
    exact inv_mul_cancel₀ (abs_ne_zero.mpr (hd i))
  have hdj : |(d j)⁻¹| * |d j| = 1 := by
    rw [abs_inv]
    exact inv_mul_cancel₀ (abs_ne_zero.mpr (hd j))
  calc
    |higham14_problem14_14_diagonalUnscalePerturbation d DeltaScaled i j|
        = |(d i)⁻¹| * |DeltaScaled i j| * |d j| := by
            rw [higham14_problem14_14_diagonalUnscalePerturbation_apply,
              abs_mul, abs_mul]
    _ ≤ |(d i)⁻¹| *
          (gamma * |higham14_problem14_14_diagonalSimilarity d H i j|) *
          |d j| := hmul
    _ = gamma * |H i j| := by
            rw [higham14_problem14_14_diagonalSimilarity_apply, abs_mul,
              abs_mul]
            calc
              |(d i)⁻¹| * (gamma * (|d i| * |H i j| * |(d j)⁻¹|)) *
                  |d j|
                  = gamma * |H i j| *
                      ((|(d i)⁻¹| * |d i|) * (|(d j)⁻¹| * |d j|)) := by
                      ring
              _ = gamma * |H i j| := by
                      rw [hdi, hdj]
                      ring

/-- Problem 14.14 diagonal-scaling transport: a determinant certificate and
    componentwise perturbation bound for the scaled Hessenberg matrix give the
    same determinant certificate and relative bound after unscaling. -/
theorem higham14_problem14_14_unscale_deltaH_det_of_diagonal_scaled_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Hscaled DeltaHscaled : Matrix ι ι ℝ) (d : ι → ℝ)
    (gamma theta : ℝ)
    (hd : ∀ i : ι, d i ≠ 0)
    (hHscaled : Hscaled = higham14_problem14_14_diagonalSimilarity d H)
    (hDeltaScaled : ∀ i j : ι, |DeltaHscaled i j| ≤ gamma * |Hscaled i j|)
    (hdetScaled : Matrix.det (Hscaled + DeltaHscaled) = theta) :
    ∃ DeltaH : Matrix ι ι ℝ,
      (∀ i j : ι, |DeltaH i j| ≤ gamma * |H i j|) ∧
      Matrix.det (H + DeltaH) = theta := by
  let DeltaH :=
    higham14_problem14_14_diagonalUnscalePerturbation d DeltaHscaled
  refine ⟨DeltaH, ?_, ?_⟩
  · apply higham14_problem14_14_unscaled_delta_bound_of_scaled d H DeltaHscaled gamma hd
    intro i j
    simpa [hHscaled] using hDeltaScaled i j
  · have hsim :
        higham14_problem14_14_diagonalSimilarity d (H + DeltaH) =
          Hscaled + DeltaHscaled := by
      ext i j
      simp [DeltaH, hHscaled, Matrix.add_apply,
        higham14_problem14_14_diagonalSimilarity_apply,
        higham14_problem14_14_diagonalUnscalePerturbation_apply]
      field_simp [hd i, hd j]
    have hdet :=
      higham14_problem14_14_det_diagonalSimilarity d (H + DeltaH) hd
    rw [← hdet, hsim, hdetScaled]

/-- Problem 14.14 diagonal-scaling wrapper for Hyman's method.  Applying the
    existing perturbed Hyman determinant package to a diagonally scaled
    Hessenberg matrix and then unscaling gives the same relative
    componentwise `DeltaH` certificate for the original matrix. -/
theorem higham14_problem14_14_exists_deltaH_det_original_of_diagonal_scaled_upper_add_zero_diag
    {n : ℕ}
    (H Hscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (d : Fin n ⊕ Unit → ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hd : ∀ i : Fin n ⊕ Unit, d i ≠ 0)
    (hHscaled : Hscaled = higham14_problem14_14_diagonalSimilarity d H)
    (hDeltaHScaledCert :
      ∃ DeltaHscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaHscaled i j| ≤ gammaH * |Hscaled i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (Hscaled + DeltaHscaled) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      Matrix.det (H + DeltaH) =
        (Equiv.Perm.sign σ : ℝ) *
          Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  rcases
    higham14_problem14_14_exists_deltaH_det_original_of_upper_add_zero_diag
      Hscaled T DeltaT TpertInv y h η gammaT gammaH σ
      hDeltaHScaledCert hTupper hDeltaTDiag hDeltaTBound hTpertInv
    with ⟨DeltaHscaled, hDeltaHscaled, hdetScaled⟩
  exact
    higham14_problem14_14_unscale_deltaH_det_of_diagonal_scaled_det
      H Hscaled DeltaHscaled d gammaH
      ((Equiv.Perm.sign σ : ℝ) *
        Matrix.det T * higham14_hymanSchur h y TpertInv η)
      hd hHscaled hDeltaHscaled hdetScaled

/-- Absolute-value form of the diagonally scaled Problem 14.14 Hyman
    backward-error target. -/
theorem higham14_problem14_14_exists_deltaH_abs_det_original_of_diagonal_scaled_upper_add_zero_diag
    {n : ℕ}
    (H Hscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (d : Fin n ⊕ Unit → ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hd : ∀ i : Fin n ⊕ Unit, d i ≠ 0)
    (hHscaled : Hscaled = higham14_problem14_14_diagonalSimilarity d H)
    (hDeltaHScaledCert :
      ∃ DeltaHscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaHscaled i j| ≤ gammaH * |Hscaled i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (Hscaled + DeltaHscaled) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      |Matrix.det (H + DeltaH)| =
        |Matrix.det T| * |higham14_hymanSchur h y TpertInv η| := by
  rcases
    higham14_problem14_14_exists_deltaH_det_original_of_diagonal_scaled_upper_add_zero_diag
      H Hscaled d T DeltaT TpertInv y h η gammaT gammaH σ
      hd hHscaled hDeltaHScaledCert hTupper hDeltaTDiag hDeltaTBound
      hTpertInv
    with ⟨DeltaH, hDeltaHBound, hdet⟩
  refine ⟨DeltaH, hDeltaHBound, ?_⟩
  have hsign_abs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  rw [hdet, abs_mul, abs_mul, hsign_abs, one_mul]

end NumStability
