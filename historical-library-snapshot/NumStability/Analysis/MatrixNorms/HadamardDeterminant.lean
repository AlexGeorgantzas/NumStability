import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Hadamard determinant inequalities

Reusable real-matrix forms of Hadamard's determinant inequality.  The proof
normalizes a positive-definite Gram matrix to unit diagonal and applies a
weighted arithmetic-geometric mean inequality to its eigenvalues.
-/

namespace NumStability

open scoped BigOperators
open Matrix

/-- For nonnegative reals indexed by `Fin n` whose sum is `n`, the product is
at most one. -/
theorem geomMean_prod_le_one_of_sum_eq_card {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (hsum : ∑ i, z i = n) :
    ∏ i, z i ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ (1 / (n : ℝ)) := by
    intro i _
    positivity
  have hw' : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (1 / (n : ℝ))) z hw hw' (fun i _ => hz i)
  have hrhs : ∑ i : Fin n, (1 / (n : ℝ)) * z i = 1 := by
    rw [← Finset.mul_sum, hsum]
    field_simp
  rw [hrhs] at hgm
  have hprodnn : 0 ≤ ∏ i, z i ^ (1 / (n : ℝ)) := by
    apply Finset.prod_nonneg
    intro i _
    exact Real.rpow_nonneg (hz i) _
  have hpow : (∏ i, z i ^ (1 / (n : ℝ))) ^ n = ∏ i, z i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast (z i ^ (1 / (n : ℝ))) n, ← Real.rpow_mul (hz i)]
    rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  calc
    ∏ i, z i = (∏ i, z i ^ (1 / (n : ℝ))) ^ n := hpow.symm
    _ ≤ 1 ^ n := by gcongr
    _ = 1 := one_pow n

/-- The determinant of a real positive-definite matrix is at most the product
of its diagonal entries. -/
theorem posDef_det_le_prod_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) : M.det ≤ ∏ i, M i i := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp
  have hpos : ∀ i, 0 < M i i := fun i => hM.diag_pos
  set d : Fin n → ℝ := fun i => (Real.sqrt (M i i))⁻¹ with hd
  set D : Matrix (Fin n) (Fin n) ℝ := diagonal d with hD
  have hdsq : ∀ i, d i * d i = (M i i)⁻¹ := by
    intro i
    have hs : Real.sqrt (M i i) * Real.sqrt (M i i) = M i i :=
      Real.mul_self_sqrt (hpos i).le
    simp only [hd]
    rw [← mul_inv, hs]
  set C : Matrix (Fin n) (Fin n) ℝ := D * M * D with hC
  have hCij : ∀ i j, C i j = d i * M i j * d j := by
    intro i j
    simp [hC, hD, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq]
  have hCii : ∀ i, C i i = 1 := by
    intro i
    rw [hCij i i]
    calc
      d i * M i i * d i = d i * d i * M i i := by ring
      _ = (M i i)⁻¹ * M i i := by rw [hdsq i]
      _ = 1 := inv_mul_cancel₀ (hpos i).ne'
  have hstar : star d = d := by
    ext i
    simp
  have hCpsd : C.PosSemidef := by
    have h1 := hM.posSemidef.conjTranspose_mul_mul_same D
    rw [hD, diagonal_conjTranspose, hstar] at h1
    rw [hC, hD]
    exact h1
  have hCherm : C.IsHermitian := hCpsd.1
  have hprodd : (∏ i, d i) * (∏ i, d i) = (∏ i, M i i)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i _ => hdsq i)
  have hdetC : C.det = M.det * (∏ i, M i i)⁻¹ := by
    rw [hC, det_mul, det_mul, det_diagonal]
    calc
      (∏ i, d i) * M.det * (∏ i, d i)
          = M.det * ((∏ i, d i) * (∏ i, d i)) := by ring
      _ = M.det * (∏ i, M i i)⁻¹ := by rw [hprodd]
  have hdetC_eig : C.det = ∏ i, hCherm.eigenvalues i := by
    rw [hCherm.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC_eig : C.trace = ∑ i, hCherm.eigenvalues i := by
    rw [hCherm.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC : C.trace = (n : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.sum_congr rfl (fun i _ => hCii i)]
    simp
  have hsum_eig : ∑ i, hCherm.eigenvalues i = (n : ℝ) := by
    rw [← htraceC_eig, htraceC]
  have hprod_eig : ∏ i, hCherm.eigenvalues i ≤ 1 :=
    geomMean_prod_le_one_of_sum_eq_card hn _
      (fun i => hCpsd.eigenvalues_nonneg i) hsum_eig
  have hdetC_le : C.det ≤ 1 := by
    rw [hdetC_eig]
    exact hprod_eig
  have hprodpos : 0 < ∏ i, M i i := Finset.prod_pos (fun i _ => hpos i)
  rw [hdetC] at hdetC_le
  have h := mul_le_mul_of_nonneg_right hdetC_le hprodpos.le
  rwa [mul_assoc, inv_mul_cancel₀ hprodpos.ne', mul_one, one_mul] at h

/-- Hadamard's determinant inequality in squared real-row form. -/
theorem hadamard_det_sq_le_prod_row_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.det) ^ 2 ≤ ∏ i, ∑ j, (A i j) ^ 2 := by
  have hrhs_nonneg : 0 ≤ ∏ i, ∑ j, (A i j) ^ 2 :=
    Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  rcases eq_or_ne A.det 0 with h0 | h0
  · rw [h0]
    simpa using hrhs_nonneg
  have hAT : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A
  set G := A * Aᵀ with hG
  have hGpsd : G.PosSemidef := by
    have h := posSemidef_self_mul_conjTranspose A
    rwa [hAT] at h
  have hAunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h0)
  have hATunit : IsUnit Aᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
    exact isUnit_iff_ne_zero.mpr h0
  have hGpd : G.PosDef := (hGpsd.posDef_iff_isUnit).mpr (hAunit.mul hATunit)
  have hdetG : G.det = (A.det) ^ 2 := by
    rw [hG, det_mul, det_transpose]
    ring
  have hGii : ∀ i, G i i = ∑ j, (A i j) ^ 2 := by
    intro i
    rw [hG, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.transpose_apply]
    ring
  have hbound := posDef_det_le_prod_diag G hGpd
  rw [hdetG] at hbound
  calc
    (A.det) ^ 2 ≤ ∏ i, G i i := hbound
    _ = ∏ i, ∑ j, (A i j) ^ 2 :=
      Finset.prod_congr rfl (fun i _ => hGii i)

end NumStability
