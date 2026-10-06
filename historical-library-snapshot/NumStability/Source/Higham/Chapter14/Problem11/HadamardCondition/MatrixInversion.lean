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

/-!
# Chapter14 Problem11 HadamardCondition MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    Euclidean norm of row `i`, the quantity `||A(i,:)||₂` used in the
    determinant normalization defining the Hadamard condition number. -/
noncomputable def higham14_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  vecNorm2 (fun j : Fin n => A i j)

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    diagonal matrix whose diagonal entries are the row 2-norms of `A`. -/
noncomputable def higham14_rowNormDiagonal {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i : Fin n => higham14_rowNorm2 A i)

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    Hadamard determinant condition number `ψ(A)`, modeled in the positive
    form used by the subsequent Hadamard-inequality statement.  The printed
    display omits absolute-value bars on `det(A)`, while the condition-number
    interpretation requires `|det(A)|` in the denominator. -/
noncomputable def higham14_hadamardConditionNumber {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, higham14_rowNorm2 A i) /
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    signed raw version of the displayed ratio `det(D)/det(A)`.  Use
    `higham14_hadamardConditionNumber` for the nonnegative condition-number
    surface that matches the following Hadamard inequality discussion. -/
noncomputable def higham14_hadamardConditionNumberRaw {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, higham14_rowNorm2 A i) /
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)

lemma higham14_rowNorm2_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ higham14_rowNorm2 A i :=
  vecNorm2_nonneg _

/-- The row-norm diagonal has determinant equal to the product of the row
    2-norms, the numerator in Higham's `ψ(A)`. -/
theorem higham14_det_rowNormDiagonal_eq_prod_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    Matrix.det (higham14_rowNormDiagonal A) =
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  simp [higham14_rowNormDiagonal]

/-- Source-facing bridge from the diagonal determinant notation to the
    product-of-row-norms definition of `ψ(A)`. -/
theorem higham14_hadamardConditionNumber_eq_det_rowNormDiagonal_div_abs_det
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    higham14_hadamardConditionNumber A =
      Matrix.det (higham14_rowNormDiagonal A) /
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
  rw [higham14_det_rowNormDiagonal_eq_prod_rowNorm2]
  rfl

/-- When `det(A)` is positive, the raw displayed ratio agrees with the
    nonnegative Hadamard condition-number form. -/
theorem higham14_hadamardConditionNumberRaw_eq_conditionNumber_of_det_pos
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : 0 < Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) :
    higham14_hadamardConditionNumberRaw A =
      higham14_hadamardConditionNumber A := by
  simp [higham14_hadamardConditionNumberRaw,
    higham14_hadamardConditionNumber, abs_of_pos hdet]

theorem higham14_hadamardConditionNumber_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    0 ≤ higham14_hadamardConditionNumber A := by
  unfold higham14_hadamardConditionNumber
  exact div_nonneg
    (Finset.prod_nonneg fun i _ => higham14_rowNorm2_nonneg A i)
    (abs_nonneg _)

lemma higham14_rowNorm2_pos_of_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (i : Fin n) :
    0 < higham14_rowNorm2 A i := by
  have hne : higham14_rowNorm2 A i ≠ 0 := by
    intro hzero
    have hrow : ∀ j : Fin n, A i j = 0 :=
      (vecNorm2_eq_zero_iff (fun j : Fin n => A i j)).mp hzero
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hrow)
  exact lt_of_le_of_ne (higham14_rowNorm2_nonneg A i) (Ne.symm hne)

theorem higham14_hadamardConditionNumber_pos_of_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 < higham14_hadamardConditionNumber A := by
  unfold higham14_hadamardConditionNumber
  exact div_pos
    (Finset.prod_pos fun i _ => higham14_rowNorm2_pos_of_det_ne_zero A hdet i)
    (abs_pos.mpr hdet)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    Hadamard's determinant inequality in squared row-norm form.  This is a
    Chapter 14 source-facing wrapper around the Chapter 9 Gram determinant
    proof. -/
theorem higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 ≤
      ∏ i : Fin n, higham14_rowNorm2 A i ^ 2 := by
  simpa [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq] using
    (hadamard_det_sq_le_prod_row_sq
      (A := (A : Matrix (Fin n) (Fin n) ℝ)))

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    Hadamard's determinant inequality in the form
    `|det(A)| <= prod_i ||A(i,:)||_2`. -/
theorem higham14_problem14_11_abs_det_le_prod_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ≤
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  have hsquare :
      (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 ≤
        (∏ i : Fin n, higham14_rowNorm2 A i) ^ 2 := by
    rw [← Finset.prod_pow]
    exact higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq A
  exact abs_le_of_sq_le_sq hsquare
    (Finset.prod_nonneg fun i _ => higham14_rowNorm2_nonneg A i)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    nonsingular matrices have Hadamard determinant condition number at least
    one, in the nonnegative `|det(A)|` denominator convention. -/
theorem higham14_problem14_11_hadamardConditionNumber_ge_one_of_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    1 ≤ higham14_hadamardConditionNumber A := by
  have hden_pos : 0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| :=
    abs_pos.mpr hdet
  unfold higham14_hadamardConditionNumber
  exact (one_le_div hden_pos).mpr
    (higham14_problem14_11_abs_det_le_prod_rowNorm2 A)

/-- Source-facing predicate for Higham, Chapter 14, Problem 14.11:
    the rows of `A` are pairwise orthogonal in the Euclidean inner product. -/
def higham14_rowsOrthogonal {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≠ j → ∑ k : Fin n, A i k * A j k = 0

/-- The source-facing row-orthogonality predicate is exactly Mathlib's
    matrix row-orthogonality predicate. -/
theorem higham14_rowsOrthogonal_iff_hasOrthogonalRows {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    higham14_rowsOrthogonal A ↔
      Matrix.HasOrthogonalRows (A : Matrix (Fin n) (Fin n) ℝ) := by
  rfl

/-- Row orthogonality is equivalently zero off-diagonal entries in the
    row Gram matrix `A Aᵀ`.  This is the landing point for the missing
    equality case of Hadamard's determinant inequality. -/
theorem higham14_rowsOrthogonal_iff_gram_offdiag_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    higham14_rowsOrthogonal A ↔
      let AM : Matrix (Fin n) (Fin n) ℝ := A
      ∀ ⦃i j : Fin n⦄, i ≠ j →
        (AM * Matrix.transpose AM) i j = 0 := by
  constructor
  · intro h
    dsimp only
    intro i j hij
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using
      h (i := i) (j := j) hij
  · intro h
    dsimp only at h
    intro i j hij
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using
      h (i := i) (j := j) hij

/-- Higham, 2nd ed., Chapter 14, Problem 14.11 support:
    equality in the row-norm Hadamard bound transfers to equality in the
    row-Gram positive-definite Hadamard bound.  The remaining converse reduces
    to proving the equality case of that positive-definite bound. -/
theorem higham14_problem14_11_gram_det_eq_prod_diag_of_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (heq :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i) :
    let AM : Matrix (Fin n) (Fin n) ℝ := A
    Matrix.det (AM * Matrix.transpose AM) =
      ∏ i : Fin n, (AM * Matrix.transpose AM) i i := by
  dsimp only
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  change Matrix.det (AM * Matrix.transpose AM) =
    ∏ i : Fin n, (AM * Matrix.transpose AM) i i
  have hdetGram :
      Matrix.det (AM * Matrix.transpose AM) = Matrix.det AM ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    ring
  have hdiag :
      ∀ i : Fin n,
        (AM * Matrix.transpose AM) i i = higham14_rowNorm2 A i ^ 2 := by
    intro i
    have hnorm :
        higham14_rowNorm2 A i ^ 2 = ∑ j : Fin n, A i j ^ 2 := by
      simp [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
    calc
      (AM * Matrix.transpose AM) i i
          = ∑ j : Fin n, A i j * A i j := by
            simp [AM, Matrix.mul_apply, Matrix.transpose_apply]
      _ = ∑ j : Fin n, A i j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = higham14_rowNorm2 A i ^ 2 := hnorm.symm
  calc
    Matrix.det (AM * Matrix.transpose AM)
        = Matrix.det AM ^ 2 := hdetGram
    _ = |Matrix.det AM| ^ 2 := by rw [sq_abs]
    _ = |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ^ 2 := by simp [AM]
    _ = (∏ i : Fin n, higham14_rowNorm2 A i) ^ 2 := by rw [heq]
    _ = ∏ i : Fin n, higham14_rowNorm2 A i ^ 2 := by
          rw [Finset.prod_pow]
    _ = ∏ i : Fin n, (AM * Matrix.transpose AM) i i := by
          exact Finset.prod_congr rfl (fun i _ => (hdiag i).symm)

/-- AM-GM equality helper for the Chapter 14 Hadamard equality case:
    nonnegative `z_i` with arithmetic mean and geometric mean both one must
    have every `z_i = 1`. -/
theorem higham14_amgm_all_eq_one_of_sum_eq_card_prod_eq_one {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hsum : ∑ i : Fin n, z i = n) (hprod : ∏ i : Fin n, z i = 1) :
    ∀ i : Fin n, z i = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 < (1 / (n : ℝ)) := by
    intro _ _
    positivity
  have hw' : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hz' : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ z i := by
    intro i _
    exact hz i
  have hrhs : ∑ i : Fin n, (1 / (n : ℝ)) * z i = 1 := by
    rw [← Finset.mul_sum, hsum]
    field_simp
  have hgm_nonneg : 0 ≤ ∏ i : Fin n, z i ^ (1 / (n : ℝ)) := by
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _
  have hpow :
      (∏ i : Fin n, z i ^ (1 / (n : ℝ))) ^ n = ∏ i : Fin n, z i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast (z i ^ (1 / (n : ℝ))) n,
      ← Real.rpow_mul (hz i)]
    rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  have hgm_pow_one :
      (∏ i : Fin n, z i ^ (1 / (n : ℝ))) ^ n = 1 := by
    rw [hpow, hprod]
  have hgm_one : (∏ i : Fin n, z i ^ (1 / (n : ℝ))) = 1 :=
    (pow_eq_one_iff_of_nonneg hgm_nonneg hn.ne').mp hgm_pow_one
  have heq_gm_am :
      (∏ i ∈ (Finset.univ : Finset (Fin n)), z i ^ (1 / (n : ℝ))) =
        ∑ i ∈ (Finset.univ : Finset (Fin n)), (1 / (n : ℝ)) * z i := by
    have hgm_one_univ :
        (∏ i ∈ (Finset.univ : Finset (Fin n)), z i ^ (1 / (n : ℝ))) = 1 := by
      simpa using hgm_one
    have hrhs_univ :
        (∑ i ∈ (Finset.univ : Finset (Fin n)), (1 / (n : ℝ)) * z i) = 1 := by
      simpa using hrhs
    exact hgm_one_univ.trans hrhs_univ.symm
  have hall :=
    (Real.geom_mean_eq_arith_mean_weighted_iff'
      (s := (Finset.univ : Finset (Fin n)))
      (w := fun _ : Fin n => (1 / (n : ℝ))) (z := z)
      hw hw' hz').mp heq_gm_am
  intro i
  have hi := hall i (Finset.mem_univ i)
  exact hi.trans hrhs

/-- Higham, 2nd ed., Chapter 14, Problem 14.11 support:
    equality in the positive-definite Hadamard determinant inequality forces
    every off-diagonal entry to vanish. -/
theorem higham14_problem14_11_posDef_offdiag_eq_zero_of_det_eq_prod_diag
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (heq : Matrix.det M = ∏ i : Fin n, M i i) :
    ∀ ⦃i j : Fin n⦄, i ≠ j → M i j = 0 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    intro i
    exact Fin.elim0 i
  have hpos : ∀ i : Fin n, 0 < M i i := fun i => hM.diag_pos
  set d : Fin n → ℝ := fun i => (Real.sqrt (M i i))⁻¹ with hd
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d with hD
  have hdsq : ∀ i : Fin n, d i * d i = (M i i)⁻¹ := by
    intro i
    have hs : Real.sqrt (M i i) * Real.sqrt (M i i) = M i i :=
      Real.mul_self_sqrt (hpos i).le
    simp only [hd]
    rw [← mul_inv, hs]
  set C : Matrix (Fin n) (Fin n) ℝ := D * M * D with hC
  have hCij : ∀ i j : Fin n, C i j = d i * M i j * d j := by
    intro i j
    simp [hC, hD, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq]
  have hCii : ∀ i : Fin n, C i i = 1 := by
    intro i
    rw [hCij i i]
    calc d i * M i i * d i = d i * d i * M i i := by ring
      _ = (M i i)⁻¹ * M i i := by rw [hdsq i]
      _ = 1 := inv_mul_cancel₀ (hpos i).ne'
  have hstar : star d = d := by ext i; simp
  have hCpsd : C.PosSemidef := by
    have h1 := hM.posSemidef.conjTranspose_mul_mul_same D
    rw [hD, Matrix.diagonal_conjTranspose, hstar] at h1
    rw [hC, hD]
    exact h1
  have hCherm : C.IsHermitian := hCpsd.1
  have hprodd : (∏ i : Fin n, d i) * (∏ i : Fin n, d i) =
      (∏ i : Fin n, M i i)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i _ => hdsq i)
  have hdetC : C.det = M.det * (∏ i : Fin n, M i i)⁻¹ := by
    rw [hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    calc (∏ i : Fin n, d i) * M.det * (∏ i : Fin n, d i)
        = M.det * ((∏ i : Fin n, d i) * (∏ i : Fin n, d i)) := by ring
      _ = M.det * (∏ i : Fin n, M i i)⁻¹ := by rw [hprodd]
  have hdetC_eig : C.det = ∏ i : Fin n, hCherm.eigenvalues i := by
    rw [hCherm.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC_eig : C.trace = ∑ i : Fin n, hCherm.eigenvalues i := by
    rw [hCherm.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC : C.trace = (n : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.sum_congr rfl (fun i _ => hCii i)]
    simp
  have hsum_eig : ∑ i : Fin n, hCherm.eigenvalues i = (n : ℝ) := by
    rw [← htraceC_eig, htraceC]
  have hprodpos : 0 < ∏ i : Fin n, M i i :=
    Finset.prod_pos fun i _ => hpos i
  have hdetC_one : C.det = 1 := by
    rw [hdetC, heq, mul_inv_cancel₀ hprodpos.ne']
  have hprod_eig_one : ∏ i : Fin n, hCherm.eigenvalues i = 1 := by
    rw [← hdetC_eig, hdetC_one]
  have heig_one : ∀ i : Fin n, hCherm.eigenvalues i = 1 :=
    higham14_amgm_all_eq_one_of_sum_eq_card_prod_eq_one hn
      hCherm.eigenvalues (fun i => hCpsd.eigenvalues_nonneg i)
      hsum_eig hprod_eig_one
  have hCeq_one : C = 1 := by
    rw [hCherm.spectral_theorem]
    have hdiag :
        Matrix.diagonal (RCLike.ofReal ∘ hCherm.eigenvalues) =
          (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal, heig_one i]
      · simp [Matrix.diagonal, hij]
    rw [hdiag]
    simp
  intro i j hij
  have hCij_zero : C i j = 0 := by
    have hentry := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) hCeq_one
    simpa [Matrix.one_apply, hij] using hentry
  have hdi_ne : d i ≠ 0 := by
    simp [hd, (Real.sqrt_pos.mpr (hpos i)).ne']
  have hdj_ne : d j ≠ 0 := by
    simp [hd, (Real.sqrt_pos.mpr (hpos j)).ne']
  rw [hCij i j] at hCij_zero
  have hleft : d i * M i j = 0 := by
    exact (mul_eq_zero.mp hCij_zero).resolve_right hdj_ne
  exact (mul_eq_zero.mp hleft).resolve_left hdi_ne

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    pairwise orthogonal rows attain equality in Hadamard's determinant
    inequality.  This is the source equality direction that does not require
    excluding zero rows. -/
theorem higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_rowsOrthogonal
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (horth : higham14_rowsOrthogonal A) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  have hgram :
      let AM : Matrix (Fin n) (Fin n) ℝ := A
      AM * Matrix.transpose AM =
        Matrix.diagonal (fun i : Fin n => ∑ k : Fin n, A i k ^ 2) := by
    dsimp only
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
    · simp [Matrix.mul_apply, Matrix.transpose_apply, hij, horth hij]
  have hsquare :
      (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 =
        (∏ i : Fin n, higham14_rowNorm2 A i) ^ 2 := by
    have hdetGram :
        let AM : Matrix (Fin n) (Fin n) ℝ := A
        Matrix.det (AM * Matrix.transpose AM) =
          (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 := by
      dsimp only
      rw [Matrix.det_mul, Matrix.det_transpose]
      ring
    rw [← hdetGram, hgram, Matrix.det_diagonal]
    rw [← Finset.prod_pow]
    simp [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
  exact (sq_eq_sq₀ (abs_nonneg _) (Finset.prod_nonneg fun i _ =>
    higham14_rowNorm2_nonneg A i)).mp (by
      rw [sq_abs]
      exact hsquare)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    equality in Hadamard's determinant inequality implies `ψ(A) = 1` for
    nonsingular `A`.  This isolates the algebraic condition-number bridge from
    the harder equality-characterization step. -/
theorem higham14_problem14_11_hadamardConditionNumber_eq_one_of_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (heq :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i) :
    higham14_hadamardConditionNumber A = 1 := by
  have hden_ne : |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ≠ 0 :=
    abs_ne_zero.mpr hdet
  unfold higham14_hadamardConditionNumber
  rw [← heq]
  exact div_self hden_ne

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    if `ψ(A) = 1` for nonsingular `A`, then Hadamard's determinant inequality
    is attained with equality. -/
theorem higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hpsi : higham14_hadamardConditionNumber A = 1) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  have hden_ne : |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ≠ 0 :=
    abs_ne_zero.mpr hdet
  unfold higham14_hadamardConditionNumber at hpsi
  have hmul :=
    congrArg
      (fun x : ℝ =>
        x * |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) hpsi
  dsimp only at hmul
  rw [div_mul_cancel₀ _ hden_ne] at hmul
  simpa [one_mul] using hmul.symm

/-- Higham, 2nd ed., Chapter 14, Problem 14.11 support:
    if `psi(A)=1` for nonsingular `A`, then the associated row Gram matrix
    attains equality in the positive-definite Hadamard determinant bound. -/
theorem higham14_problem14_11_gram_det_eq_prod_diag_of_hadamardConditionNumber_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hpsi : higham14_hadamardConditionNumber A = 1) :
    let AM : Matrix (Fin n) (Fin n) ℝ := A
    Matrix.det (AM * Matrix.transpose AM) =
      ∏ i : Fin n, (AM * Matrix.transpose AM) i i :=
  higham14_problem14_11_gram_det_eq_prod_diag_of_abs_det_eq_prod_rowNorm2 A
    (higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
      A hdet hpsi)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    for nonsingular `A`, the normalized condition-number statement `ψ(A) = 1`
    is equivalent to equality in Hadamard's determinant inequality. -/
theorem higham14_problem14_11_hadamardConditionNumber_eq_one_iff_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    higham14_hadamardConditionNumber A = 1 ↔
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i := by
  constructor
  · exact
      higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
        A hdet
  · exact
      higham14_problem14_11_hadamardConditionNumber_eq_one_of_abs_det_eq_prod_rowNorm2
        A hdet

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    nonsingular matrices with pairwise orthogonal rows have `ψ(A) = 1`. -/
theorem higham14_problem14_11_hadamardConditionNumber_eq_one_of_rowsOrthogonal
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (horth : higham14_rowsOrthogonal A) :
    higham14_hadamardConditionNumber A = 1 :=
  higham14_problem14_11_hadamardConditionNumber_eq_one_of_abs_det_eq_prod_rowNorm2
    A hdet
    (higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_rowsOrthogonal A horth)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    equality in Hadamard's determinant inequality for a nonsingular matrix
    forces pairwise orthogonal rows. -/
theorem higham14_problem14_11_rowsOrthogonal_of_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (heq :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i) :
    higham14_rowsOrthogonal A := by
  rw [higham14_rowsOrthogonal_iff_gram_offdiag_zero A]
  dsimp only
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  have hgram_eq :
      Matrix.det (AM * Matrix.transpose AM) =
        ∏ i : Fin n, (AM * Matrix.transpose AM) i i := by
    simpa [AM] using
      higham14_problem14_11_gram_det_eq_prod_diag_of_abs_det_eq_prod_rowNorm2
        A heq
  have hAT :
      Matrix.conjTranspose AM = Matrix.transpose AM :=
    Matrix.conjTranspose_eq_transpose_of_trivial AM
  have hGpsd : (AM * Matrix.transpose AM).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose AM
    rwa [hAT] at h
  have hAunit : IsUnit AM :=
    (Matrix.isUnit_iff_isUnit_det AM).mpr (isUnit_iff_ne_zero.mpr (by simpa [AM] using hdet))
  have hATunit : IsUnit (Matrix.transpose AM) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (by simpa [AM] using hdet)
  have hGpd : (AM * Matrix.transpose AM).PosDef :=
    (hGpsd.posDef_iff_isUnit).mpr (hAunit.mul hATunit)
  exact
    higham14_problem14_11_posDef_offdiag_eq_zero_of_det_eq_prod_diag
      (AM * Matrix.transpose AM) hGpd hgram_eq

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    for nonsingular `A`, `ψ(A) = 1` forces pairwise orthogonal rows. -/
theorem higham14_problem14_11_rowsOrthogonal_of_hadamardConditionNumber_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hpsi : higham14_hadamardConditionNumber A = 1) :
    higham14_rowsOrthogonal A :=
  higham14_problem14_11_rowsOrthogonal_of_abs_det_eq_prod_rowNorm2 A hdet
    (higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
      A hdet hpsi)

end NumStability
