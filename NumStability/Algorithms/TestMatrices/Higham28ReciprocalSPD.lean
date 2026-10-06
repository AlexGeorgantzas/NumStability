/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Contracts

namespace NumStability

open scoped BigOperators

/-! # Higham Chapter 28: general reciprocal-spectrum SPD construction

This module closes the precise construction on p. 520.  For a nonsingular
matrix `Z` and a diagonal sign matrix `D`, it builds `X = Z D Z⁻¹` and
`A = Xᵀ X`, then proves directly that `X² = I`, `det A = 1`, `A` is symmetric
positive definite, and every nonzero eigenvalue of `A` has its reciprocal as
an eigenvalue.  No spectral conclusion is assumed as a hypothesis.
-/

noncomputable def higham28SignDiagonal {n : ℕ} (d : Fin n → ℝ) : RSqMat n :=
  Matrix.diagonal d

noncomputable def higham28ReciprocalInvolution {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) : RSqMat n :=
  Z * higham28SignDiagonal d * Z⁻¹

noncomputable def higham28ReciprocalSPD {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) : RSqMat n :=
  (higham28ReciprocalInvolution Z d).transpose *
    higham28ReciprocalInvolution Z d

theorem higham28SignDiagonal_sq {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    higham28SignDiagonal d * higham28SignDiagonal d = (1 : RSqMat n) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [higham28SignDiagonal, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · rcases hd i with hi | hi <;> simp [hi]
    · intro b _ hbi
      simp [hbi]
    · simp
  · simp only [higham28SignDiagonal, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k _
      by_cases hik : i = k
      · subst k
        simp [hij]
      · simp [hik]

theorem higham28ReciprocalInvolution_sq {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    higham28ReciprocalInvolution Z d *
        higham28ReciprocalInvolution Z d = (1 : RSqMat n) := by
  let D := higham28SignDiagonal d
  have hD : D * D = (1 : RSqMat n) := by
    simpa [D] using higham28SignDiagonal_sq d hd
  have hZiZ : Z⁻¹ * Z = (1 : RSqMat n) := Matrix.nonsing_inv_mul Z hZ
  have hZZi : Z * Z⁻¹ = (1 : RSqMat n) := Matrix.mul_nonsing_inv Z hZ
  unfold higham28ReciprocalInvolution
  change (Z * D * Z⁻¹) * (Z * D * Z⁻¹) = _
  calc
    (Z * D * Z⁻¹) * (Z * D * Z⁻¹) =
        Z * D * (Z⁻¹ * Z) * D * Z⁻¹ := by noncomm_ring
    _ = Z * D * D * Z⁻¹ := by rw [hZiZ]; simp
    _ = Z * (D * D) * Z⁻¹ := by noncomm_ring
    _ = Z * Z⁻¹ := by rw [hD]; simp
    _ = 1 := hZZi

theorem higham28ReciprocalSPD_transpose {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) :
    (higham28ReciprocalSPD Z d).transpose =
      higham28ReciprocalSPD Z d := by
  simp [higham28ReciprocalSPD, Matrix.transpose_mul]

theorem higham28ReciprocalSPD_det_one {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    Matrix.det (higham28ReciprocalSPD Z d) = 1 := by
  let X := higham28ReciprocalInvolution Z d
  have hXsq : X * X = (1 : RSqMat n) := by
    simpa [X] using higham28ReciprocalInvolution_sq Z d hZ hd
  have hdetSq : Matrix.det X * Matrix.det X = 1 := by
    have := congrArg Matrix.det hXsq
    simpa [Matrix.det_mul] using this
  simp only [higham28ReciprocalSPD, Matrix.det_mul, Matrix.det_transpose]
  exact hdetSq

theorem higham28ReciprocalSPD_quadratic_eq_sum_sq {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) (v : RVec n) :
    (∑ i : Fin n, ∑ j : Fin n,
      v i * higham28ReciprocalSPD Z d i j * v j) =
      ∑ k : Fin n,
        (Matrix.mulVec (higham28ReciprocalInvolution Z d) v k) ^ 2 := by
  let X := higham28ReciprocalInvolution Z d
  change (∑ i : Fin n, ∑ j : Fin n,
      v i * (X.transpose * X) i j * v j) =
      ∑ k : Fin n, (Matrix.mulVec X v k) ^ 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        v i * (X k i * X k j) * v j) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        v i * (X k i * X k j) * v j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        v i * (X k i * X k j) * v j := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, (∑ j : Fin n, X k j * v j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

theorem higham28ReciprocalInvolution_mulVec_injective {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    Function.Injective (Matrix.mulVec (higham28ReciprocalInvolution Z d)) := by
  let X := higham28ReciprocalInvolution Z d
  have hXsq : X * X = (1 : RSqMat n) := by
    simpa [X] using higham28ReciprocalInvolution_sq Z d hZ hd
  intro v w hvw
  change Matrix.mulVec X v = Matrix.mulVec X w at hvw
  have := congrArg (Matrix.mulVec X) hvw
  simpa [Matrix.mulVec_mulVec, hXsq] using this

theorem higham28ReciprocalSPD_quadratic_pos {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1)
    (v : RVec n) (hv : ∃ i, v i ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n,
      v i * higham28ReciprocalSPD Z d i j * v j := by
  rw [higham28ReciprocalSPD_quadratic_eq_sum_sq]
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hv
    exact hi (congrFun h i)
  let X := higham28ReciprocalInvolution Z d
  have hXv0 : Matrix.mulVec X v ≠ 0 := by
    intro h
    exact hv0 ((higham28ReciprocalInvolution_mulVec_injective Z d hZ hd)
      (h.trans (Matrix.mulVec_zero X).symm))
  have hex : ∃ i, Matrix.mulVec X v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hXv0 (funext h)
  obtain ⟨i, hi⟩ := hex
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ?_
  exact ⟨i, Finset.mem_univ i,
    (sq_nonneg (Matrix.mulVec X v i)).lt_of_ne
      (Ne.symm (pow_ne_zero 2 hi))⟩

theorem higham28ReciprocalSPD_isSymPosDef_explicit {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    (∀ i j : Fin n,
      higham28ReciprocalSPD Z d i j = higham28ReciprocalSPD Z d j i) ∧
      ∀ v : RVec n, (∃ i, v i ≠ 0) →
        0 < ∑ i : Fin n, ∑ j : Fin n,
          v i * higham28ReciprocalSPD Z d i j * v j := by
  constructor
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j)
      (higham28ReciprocalSPD_transpose Z d)
    simpa [Matrix.transpose_apply] using h.symm
  · exact higham28ReciprocalSPD_quadratic_pos Z d hZ hd

/-! ## The triangular-factor sentence on p. 520

The source says that, for lower-triangular `Z`, the involution `X` is a
Cholesky factor "up to a column scaling" by the sign diagonal.  With the
printed convention `A = Xᵀ X`, multiplication on the **left** (row scaling)
is what preserves the Gram matrix.  Equivalently, multiplication on the right
is valid after transposing `X`.  The theorems below record the corrected exact
orientation.  A concrete two-by-two member of the printed family then shows
that right/column scaling `X` itself does not in general preserve `A`.
-/

private theorem higham28_lowerTriangular_mul_apply_diag {n : ℕ}
    (M N : RSqMat n)
    (hM : ∀ i j : Fin n, i < j → M i j = 0)
    (hN : ∀ i j : Fin n, i < j → N i j = 0)
    (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · simp [hN j i hlt]
    · simp [hM i j hgt]
  · simp

/-- A lower-triangular similarity matrix produces a lower-triangular
involution, and similarity by the sign diagonal leaves the diagonal equal to
the sign vector.  Both facts are derived from the actual nonsingular inverse. -/
theorem higham28ReciprocalInvolution_lower_and_diag {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hZlower : ∀ i j : Fin n, i < j → Z i j = 0) :
    (∀ i j : Fin n, i < j →
      higham28ReciprocalInvolution Z d i j = 0) ∧
      ∀ i : Fin n, higham28ReciprocalInvolution Z d i i = d i := by
  let D := higham28SignDiagonal d
  have hZtri :
      Z.BlockTriangular (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) := by
    intro i j hij
    exact hZlower i j (by simpa using hij)
  letI : Invertible Z := Z.invertibleOfIsUnitDet hZ
  have hZinvTri :
      Z⁻¹.BlockTriangular (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) :=
    Matrix.blockTriangular_inv_of_blockTriangular hZtri
  have hDtri :
      D.BlockTriangular (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) := by
    simpa [D] using
      (Matrix.blockTriangular_diagonal (b :=
        (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ)) d)
  have hZinvLower : ∀ i j : Fin n, i < j → Z⁻¹ i j = 0 := by
    intro i j hij
    exact hZinvTri (by simpa using hij)
  have hDlower : ∀ i j : Fin n, i < j → D i j = 0 := by
    intro i j hij
    simp [D, higham28SignDiagonal, ne_of_lt hij]
  have hZDtri :
      (Z * D).BlockTriangular
        (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) :=
    hZtri.mul hDtri
  have hZDlower : ∀ i j : Fin n, i < j → (Z * D) i j = 0 := by
    intro i j hij
    exact hZDtri (by simpa using hij)
  constructor
  · intro i j hij
    have hXtri :
        ((Z * D) * Z⁻¹).BlockTriangular
          (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) :=
      hZDtri.mul hZinvTri
    exact hXtri (by simpa [higham28ReciprocalInvolution, D] using hij)
  · intro i
    have hZdiagInv : Z i i * Z⁻¹ i i = 1 := by
      calc
        Z i i * Z⁻¹ i i = (Z * Z⁻¹) i i :=
          (higham28_lowerTriangular_mul_apply_diag Z Z⁻¹
            hZlower hZinvLower i).symm
        _ = (1 : RSqMat n) i i := by rw [Matrix.mul_nonsing_inv Z hZ]
        _ = 1 := by simp
    change ((Z * D) * Z⁻¹) i i = d i
    rw [higham28_lowerTriangular_mul_apply_diag (Z * D) Z⁻¹
      hZDlower hZinvLower i]
    rw [higham28_lowerTriangular_mul_apply_diag Z D hZlower hDlower i]
    rw [show D i i = d i by simp [D, higham28SignDiagonal]]
    change (Z i i * d i) * Z⁻¹ i i = d i
    calc
      (Z i i * d i) * Z⁻¹ i i = d i * (Z i i * Z⁻¹ i i) := by ring
      _ = d i := by rw [hZdiagInv]; ring

/-- Corrected row-scaling identity: left multiplication by the sign diagonal
preserves the Gram matrix defining `A`.  No triangularity is needed. -/
theorem higham28ReciprocalSPD_row_sign_factorization {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    let R := higham28SignDiagonal d *
      higham28ReciprocalInvolution Z d
    R.transpose * R = higham28ReciprocalSPD Z d := by
  let D := higham28SignDiagonal d
  let X := higham28ReciprocalInvolution Z d
  have hDD : D * D = (1 : RSqMat n) := by
    simpa [D] using higham28SignDiagonal_sq d hd
  have hDt : D.transpose = D := by
    simp [D, higham28SignDiagonal]
  change (D * X).transpose * (D * X) = X.transpose * X
  rw [Matrix.transpose_mul, hDt]
  calc
    (X.transpose * D) * (D * X) = X.transpose * (D * D) * X := by
      noncomm_ring
    _ = X.transpose * X := by rw [hDD]; simp

/-- Equivalent transpose/column-scaling identity.  The valid right scaling is
of `Xᵀ`, not of `X`: `(Xᵀ D)(Xᵀ D)ᵀ = A`. -/
theorem higham28ReciprocalSPD_transpose_column_sign_factorization {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    let L := (higham28ReciprocalInvolution Z d).transpose *
      higham28SignDiagonal d
    L * L.transpose = higham28ReciprocalSPD Z d := by
  let D := higham28SignDiagonal d
  let X := higham28ReciprocalInvolution Z d
  have hDD : D * D = (1 : RSqMat n) := by
    simpa [D] using higham28SignDiagonal_sq d hd
  have hDt : D.transpose = D := by
    simp [D, higham28SignDiagonal]
  change (X.transpose * D) * (X.transpose * D).transpose = X.transpose * X
  rw [Matrix.transpose_mul, hDt, Matrix.transpose_transpose]
  calc
    (X.transpose * D) * (D * X) = X.transpose * (D * D) * X := by
      noncomm_ring
    _ = X.transpose * X := by rw [hDD]; simp

/-- With lower-triangular `Z`, the corrected row-scaled factor is lower
triangular, has positive unit diagonal, and gives the exact reverse-Cholesky
factorization `A = RᵀR`. -/
theorem higham28ReciprocalSPD_lower_reverseCholeskyFactor {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1)
    (hZlower : ∀ i j : Fin n, i < j → Z i j = 0) :
    let R := higham28SignDiagonal d *
      higham28ReciprocalInvolution Z d
    (∀ i j : Fin n, i < j → R i j = 0) ∧
      (∀ i : Fin n, R i i = 1) ∧
      R.transpose * R = higham28ReciprocalSPD Z d := by
  let D := higham28SignDiagonal d
  let X := higham28ReciprocalInvolution Z d
  have hX := higham28ReciprocalInvolution_lower_and_diag Z d hZ hZlower
  change (∀ i j : Fin n, i < j → (D * X) i j = 0) ∧
    (∀ i : Fin n, (D * X) i i = 1) ∧
    (D * X).transpose * (D * X) = higham28ReciprocalSPD Z d
  refine ⟨?_, ?_, higham28ReciprocalSPD_row_sign_factorization Z d hd⟩
  · intro i j hij
    have hXlower : X i j = 0 := by simpa [X] using hX.1 i j hij
    simp [D, higham28SignDiagonal, hXlower]
  · intro i
    have hXdiag : X i i = d i := by simpa [X] using hX.2 i
    simp only [D, higham28SignDiagonal, Matrix.diagonal_mul]
    rw [hXdiag]
    rcases hd i with hi | hi <;> rw [hi] <;> norm_num

/-! ### A concrete source-discrepancy witness for column scaling `X` -/

noncomputable def higham28ColumnScalingCounterZ : RSqMat 2 :=
  ![![(1 : ℝ), 0], ![1, 1]]

noncomputable def higham28ColumnScalingCounterZInv : RSqMat 2 :=
  ![![(1 : ℝ), 0], ![-1, 1]]

noncomputable def higham28ColumnScalingCounterSigns : Fin 2 → ℝ :=
  ![(1 : ℝ), -1]

noncomputable def higham28ColumnScalingCounterX : RSqMat 2 :=
  ![![(1 : ℝ), 0], ![2, -1]]

theorem higham28ColumnScalingCounterZ_lower :
    ∀ i j : Fin 2, i < j → higham28ColumnScalingCounterZ i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [higham28ColumnScalingCounterZ]

theorem higham28ColumnScalingCounterZ_det_isUnit :
    IsUnit (Matrix.det higham28ColumnScalingCounterZ) := by
  apply isUnit_iff_ne_zero.mpr
  norm_num [higham28ColumnScalingCounterZ, Matrix.det_fin_two]

theorem higham28ColumnScalingCounterSigns_pm_one :
    ∀ i, higham28ColumnScalingCounterSigns i = 1 ∨
      higham28ColumnScalingCounterSigns i = -1 := by
  intro i
  fin_cases i <;> simp [higham28ColumnScalingCounterSigns]

theorem higham28ColumnScalingCounterZ_inv :
    higham28ColumnScalingCounterZ⁻¹ = higham28ColumnScalingCounterZInv := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham28ColumnScalingCounterZ,
      higham28ColumnScalingCounterZInv, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

theorem higham28ColumnScalingCounter_involution :
    higham28ReciprocalInvolution higham28ColumnScalingCounterZ
      higham28ColumnScalingCounterSigns = higham28ColumnScalingCounterX := by
  unfold higham28ReciprocalInvolution
  rw [higham28ColumnScalingCounterZ_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham28SignDiagonal,
      higham28ColumnScalingCounterZ, higham28ColumnScalingCounterSigns,
      higham28ColumnScalingCounterX, higham28ColumnScalingCounterZInv,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Literal right/column scaling of `X` by the source sign diagonal changes the
off-diagonal signs of its Gram matrix in this nonsingular lower-triangular
example, so it is not a factorization of the printed `A = XᵀX`. -/
theorem higham28ColumnScalingCounter_right_scaling_fails :
    let X := higham28ReciprocalInvolution higham28ColumnScalingCounterZ
      higham28ColumnScalingCounterSigns
    let D := higham28SignDiagonal higham28ColumnScalingCounterSigns
    (X * D).transpose * (X * D) ≠
      higham28ReciprocalSPD higham28ColumnScalingCounterZ
        higham28ColumnScalingCounterSigns := by
  dsimp only
  intro h
  unfold higham28ReciprocalSPD at h
  rw [higham28ColumnScalingCounter_involution] at h
  have h01 := congrArg (fun M : RSqMat 2 => M 0 1) h
  norm_num [higham28SignDiagonal, higham28ColumnScalingCounterSigns,
    higham28ColumnScalingCounterX, Matrix.mul_apply, Fin.sum_univ_two] at h01

theorem higham28ReciprocalSPD_reciprocal_eigenpair {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1)
    (lambda : ℝ) (v : RVec n)
    (hlambda : lambda ≠ 0) (hv : v ≠ 0)
    (heigen : Matrix.mulVec (higham28ReciprocalSPD Z d) v = lambda • v) :
    let w := Matrix.mulVec (higham28ReciprocalInvolution Z d) v
    w ≠ 0 ∧
      Matrix.mulVec (higham28ReciprocalSPD Z d) w = lambda⁻¹ • w := by
  let X := higham28ReciprocalInvolution Z d
  let A := higham28ReciprocalSPD Z d
  let B := X * X.transpose
  let w := Matrix.mulVec X v
  have hXsq : X * X = (1 : RSqMat n) := by
    simpa [X] using higham28ReciprocalInvolution_sq Z d hZ hd
  have hAw : A * B = (1 : RSqMat n) := by
    change (X.transpose * X) * (X * X.transpose) = _
    calc
      (X.transpose * X) * (X * X.transpose) =
          X.transpose * (X * X) * X.transpose := by noncomm_ring
      _ = X.transpose * X.transpose := by rw [hXsq]; simp
      _ = (X * X).transpose := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hXsq]; simp
  have hsim : X * A * X = B := by
    change X * (X.transpose * X) * X = X * X.transpose
    calc
      X * (X.transpose * X) * X = X * X.transpose * (X * X) := by
        noncomm_ring
      _ = X * X.transpose := by rw [hXsq]; simp
  have hXw : Matrix.mulVec X w = v := by
    rw [show w = Matrix.mulVec X v by rfl, Matrix.mulVec_mulVec, hXsq,
      Matrix.one_mulVec]
  have hw : w ≠ 0 := by
    intro hw0
    apply hv
    rw [← hXw, hw0]
    simp
  have heigenA : Matrix.mulVec A v = lambda • v := by
    simpa [A] using heigen
  have hBw : Matrix.mulVec B w = lambda • w := by
    calc
      Matrix.mulVec B w = Matrix.mulVec (X * A * X) w := by rw [hsim]
      _ = Matrix.mulVec (X * A) (Matrix.mulVec X w) := by
        exact (Matrix.mulVec_mulVec w (X * A) X).symm
      _ = Matrix.mulVec X (Matrix.mulVec A (Matrix.mulVec X w)) := by
        exact (Matrix.mulVec_mulVec (Matrix.mulVec X w) X A).symm
      _ = Matrix.mulVec X (Matrix.mulVec A v) := by rw [hXw]
      _ = Matrix.mulVec X (lambda • v) := by rw [heigenA]
      _ = lambda • w := by rw [Matrix.mulVec_smul]
  have happly := congrArg (Matrix.mulVec A) hBw
  have hscale : w = lambda • Matrix.mulVec A w := by
    simpa [Matrix.mulVec_mulVec, hAw, Matrix.mulVec_smul] using happly
  change w ≠ 0 ∧ Matrix.mulVec A w = lambda⁻¹ • w
  refine ⟨hw, ?_⟩
  funext i
  have hi := congrFun hscale i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  calc
    Matrix.mulVec A w i = lambda⁻¹ * (lambda * Matrix.mulVec A w i) := by
      field_simp
    _ = lambda⁻¹ * w i := by rw [← hi]
    _ = (lambda⁻¹ • w) i := by simp

end NumStability
