import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter28.Section04.ReciprocalSpectrumSPD.ReciprocalSPD

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28ReciprocalSPD under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators

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

end NumStability
