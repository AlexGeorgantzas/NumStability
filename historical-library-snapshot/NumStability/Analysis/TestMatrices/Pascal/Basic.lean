import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Analysis TestMatrices Pascal Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.4, p. 518: the symmetric Pascal matrix. -/
noncomputable def pascalMatrix (n : ℕ) : RSqMat n :=
  fun i j => (Nat.choose (i.val + j.val) j.val : ℝ)

@[simp] theorem pascalMatrix_apply {n : ℕ} (i j : Fin n) :
    pascalMatrix n i j = (Nat.choose (i.val + j.val) j.val : ℝ) := rfl

/-- The Pascal matrix in Section 28.4 is symmetric. -/
theorem pascalMatrix_transpose (n : ℕ) :
    (pascalMatrix n).transpose = pascalMatrix n := by
  ext i j
  simp only [Matrix.transpose_apply, pascalMatrix_apply]
  rw [add_comm j.val i.val]
  exact_mod_cast Nat.choose_symm_add

/-- Vandermonde's convolution in the form used by the Pascal Gram
factorization. -/
theorem pascal_choose_gram (i j : ℕ) :
    (∑ k ∈ Finset.range (i + 1), Nat.choose i k * Nat.choose j k) =
      Nat.choose (i + j) i := by
  calc
    (∑ k ∈ Finset.range (i + 1), Nat.choose i k * Nat.choose j k) =
        ∑ k ∈ Finset.range (i + 1),
          Nat.choose i (i + 1 - 1 - k) * Nat.choose j (i + 1 - 1 - k) := by
            symm
            exact Finset.sum_range_reflect
              (fun k => Nat.choose i k * Nat.choose j k) (i + 1)
    _ = ∑ k ∈ Finset.range (i + 1), Nat.choose i k * Nat.choose j (i - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have harith : i + 1 - 1 - k = i - k := by omega
      rw [harith, Nat.choose_symm hki]
    _ = Nat.choose (i + j) i := by
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The unit lower-triangular Pascal matrix used in Higham's factorization
`P = L Lᵀ`. -/
noncomputable def pascalLower (n : ℕ) : RSqMat n :=
  fun i j => (Nat.choose i.val j.val : ℝ)

/-- Higham, Section 28.4, p. 518: the symmetric Pascal matrix has the exact
Gram/Cholesky factorization `P = L Lᵀ`. -/
theorem pascalMatrix_eq_lower_mul_transpose (n : ℕ) :
    pascalMatrix n = pascalLower n * (pascalLower n).transpose := by
  ext i j
  simp only [pascalMatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
    pascalLower]
  symm
  rw [Fin.sum_univ_eq_sum_range
    (fun x : ℕ => (Nat.choose i.val x : ℝ) * (Nat.choose j.val x : ℝ)) n]
  have hsubset : Finset.range (i.val + 1) ⊆ Finset.range n :=
    Finset.range_mono (Nat.succ_le_of_lt i.isLt)
  calc
    (∑ x ∈ Finset.range n,
        (Nat.choose i.val x : ℝ) * (Nat.choose j.val x : ℝ)) =
        ∑ x ∈ Finset.range (i.val + 1),
          (Nat.choose i.val x : ℝ) * (Nat.choose j.val x : ℝ) := by
      symm
      apply Finset.sum_subset hsubset
      intro k hkn hki
      have hik : i.val < k := by
        have hnmem : ¬ k < i.val + 1 := by simpa using hki
        omega
      simp [Nat.choose_eq_zero_of_lt hik]
    _ = (Nat.choose (i.val + j.val) i.val : ℝ) := by
      exact_mod_cast pascal_choose_gram i.val j.val
    _ = (Nat.choose (i.val + j.val) j.val : ℝ) := by
      exact_mod_cast Nat.choose_symm_add

/-- The Pascal factor is lower triangular. -/
theorem pascalLower_blockTriangular (n : ℕ) :
    (pascalLower n).BlockTriangular OrderDual.toDual := by
  intro i j hij
  simp only [pascalLower]
  have hlt : i.val < j.val := hij
  simp [Nat.choose_eq_zero_of_lt hlt]

/-- The unit lower-triangular Pascal factor has determinant one. -/
theorem pascalLower_det (n : ℕ) : Matrix.det (pascalLower n) = 1 := by
  rw [Matrix.det_of_lowerTriangular (pascalLower n)
    (pascalLower_blockTriangular n)]
  simp [pascalLower]

/-- Higham, Section 28.4, p. 518: the symmetric Pascal matrix has determinant
one. -/
theorem pascalMatrix_det (n : ℕ) : Matrix.det (pascalMatrix n) = 1 := by
  rw [pascalMatrix_eq_lower_mul_transpose, Matrix.det_mul,
    Matrix.det_transpose, pascalLower_det]
  norm_num

/-- The alternating binomial convolution behind the signed Pascal
involution. -/
theorem signedPascalConvolutionInt (i j : ℕ) :
    (∑ k ∈ Finset.range (i + 1),
      ((-1 : ℤ) ^ k * Nat.choose i k) *
        ((-1 : ℤ) ^ j * Nat.choose k j)) =
      if i = j then 1 else 0 := by
  by_cases hji : j ≤ i
  · have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => ((-1 : ℤ) ^ k * Nat.choose i k) *
        ((-1 : ℤ) ^ j * Nat.choose k j)) (show j ≤ i + 1 by omega)
    have hlow :
        (∑ k ∈ Finset.range j,
          ((-1 : ℤ) ^ k * Nat.choose i k) *
            ((-1 : ℤ) ^ j * Nat.choose k j)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkj : k < j := Finset.mem_range.mp hk
      simp [Nat.choose_eq_zero_of_lt hkj]
    rw [← hsplit, hlow, zero_add, Finset.sum_Ico_eq_sum_range]
    have hrange : i + 1 - j = (i - j) + 1 := by omega
    rw [hrange]
    calc
      (∑ k ∈ Finset.range (i - j + 1),
        ((-1 : ℤ) ^ (j + k) * Nat.choose i (j + k)) *
          ((-1 : ℤ) ^ j * Nat.choose (j + k) j)) =
          (Nat.choose i j : ℤ) *
            ∑ k ∈ Finset.range (i - j + 1),
              (-1 : ℤ) ^ k * Nat.choose (i - j) k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hchoose := Nat.choose_mul (n := i) (k := j + k) (s := j)
          (Nat.le_add_right j k)
        have hchooseInt :
            (Nat.choose i (j + k) : ℤ) * Nat.choose (j + k) j =
              (Nat.choose i j : ℤ) * Nat.choose (i - j) k := by
          have hchoose' := hchoose
          simp only [Nat.add_sub_cancel_left] at hchoose'
          exact_mod_cast hchoose'
        calc
          ((-1 : ℤ) ^ (j + k) * Nat.choose i (j + k)) *
              ((-1 : ℤ) ^ j * Nat.choose (j + k) j) =
              (((-1 : ℤ) ^ (j + k)) * (-1 : ℤ) ^ j) *
                ((Nat.choose i (j + k) : ℤ) * Nat.choose (j + k) j) := by ring
          _ = (((-1 : ℤ) ^ (j + k)) * (-1 : ℤ) ^ j) *
                ((Nat.choose i j : ℤ) * Nat.choose (i - j) k) := by
                  rw [hchooseInt]
          _ = (Nat.choose i j : ℤ) *
                ((-1 : ℤ) ^ k * Nat.choose (i - j) k) := by
                  have hsign : ((-1 : ℤ) ^ (j + k)) * (-1 : ℤ) ^ j =
                      (-1 : ℤ) ^ k := by
                    rw [pow_add]
                    calc
                      ((-1 : ℤ) ^ j * (-1 : ℤ) ^ k) * (-1 : ℤ) ^ j =
                          ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) * (-1 : ℤ) ^ k := by
                            ring
                      _ = (-1 : ℤ) ^ k := by
                        rw [← mul_pow]
                        norm_num
                  rw [hsign]
                  ring
      _ = (Nat.choose i j : ℤ) * (if i - j = 0 then 1 else 0) := by
        rw [Int.alternating_sum_range_choose]
      _ = if i = j then 1 else 0 := by
        by_cases hij : i = j
        · subst j
          simp
        · have hsub : i - j ≠ 0 := by omega
          simp [hij, hsub]
  · have hij : i ≠ j := by omega
    rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkj : k < j := lt_of_le_of_lt hki (lt_of_not_ge hji)
    simp [Nat.choose_eq_zero_of_lt hkj]

/-- Higham's signed lower-triangular Pascal factor,
`S_ij = (-1)^j choose(i,j)`. -/
noncomputable def signedPascal (n : ℕ) : RSqMat n :=
  fun i j => (-1 : ℝ) ^ j.val * Nat.choose i.val j.val

/-- Higham, Section 28.4, p. 519: the signed triangular Pascal factor is
involutory. -/
theorem signedPascal_mul_self (n : ℕ) :
    signedPascal n * signedPascal n = 1 := by
  ext i j
  simp only [Matrix.mul_apply, signedPascal]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ((-1 : ℝ) ^ k * Nat.choose i.val k) *
      ((-1 : ℝ) ^ j.val * Nat.choose k j.val)) n]
  have hsubset : Finset.range (i.val + 1) ⊆ Finset.range n :=
    Finset.range_mono (Nat.succ_le_of_lt i.isLt)
  calc
    (∑ k ∈ Finset.range n,
      ((-1 : ℝ) ^ k * Nat.choose i.val k) *
        ((-1 : ℝ) ^ j.val * Nat.choose k j.val)) =
        ∑ k ∈ Finset.range (i.val + 1),
          ((-1 : ℝ) ^ k * Nat.choose i.val k) *
            ((-1 : ℝ) ^ j.val * Nat.choose k j.val) := by
      symm
      apply Finset.sum_subset hsubset
      intro k hkn hki
      have hik : i.val < k := by
        have hnmem : ¬ k < i.val + 1 := by simpa using hki
        omega
      simp [Nat.choose_eq_zero_of_lt hik]
    _ = if i.val = j.val then 1 else 0 := by
      exact_mod_cast signedPascalConvolutionInt i.val j.val
    _ = (1 : RSqMat n) i j := by
      simp [Matrix.one_apply, Fin.ext_iff]

/-- The diagonal sign matrix used to relate the ordinary and signed Pascal
factors. -/
noncomputable def pascalSignDiagonal (n : ℕ) : RSqMat n :=
  Matrix.diagonal (fun i => (-1 : ℝ) ^ i.val)

/-- The Pascal sign diagonal is itself involutory. -/
theorem pascalSignDiagonal_mul_self (n : ℕ) :
    pascalSignDiagonal n * pascalSignDiagonal n = 1 := by
  rw [pascalSignDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [← mul_pow]

/-- The Pascal sign diagonal is symmetric. -/
theorem pascalSignDiagonal_transpose (n : ℕ) :
    (pascalSignDiagonal n).transpose = pascalSignDiagonal n := by
  exact Matrix.diagonal_transpose _

/-- The signed Pascal factor is the ordinary lower factor with alternating
column signs. -/
theorem signedPascal_eq_lower_mul_signDiagonal (n : ℕ) :
    signedPascal n = pascalLower n * pascalSignDiagonal n := by
  ext i j
  simp [signedPascal, pascalLower, pascalSignDiagonal]
  ring

/-- A rearranged form of the signed-Pascal involution used in the inverse
calculation. -/
theorem pascal_lower_sign_lower_eq_sign (n : ℕ) :
    pascalLower n * pascalSignDiagonal n * pascalLower n =
      pascalSignDiagonal n := by
  have hS := signedPascal_mul_self n
  rw [signedPascal_eq_lower_mul_signDiagonal] at hS
  calc
    pascalLower n * pascalSignDiagonal n * pascalLower n =
        (pascalLower n * pascalSignDiagonal n * pascalLower n) *
          (pascalSignDiagonal n * pascalSignDiagonal n) := by
            rw [pascalSignDiagonal_mul_self, mul_one]
    _ = (pascalLower n * pascalSignDiagonal n) *
          (pascalLower n * pascalSignDiagonal n) * pascalSignDiagonal n := by
            simp only [mul_assoc]
    _ = pascalSignDiagonal n := by rw [hS, one_mul]

/-- Higham, Section 28.4, p. 519: `SᵀS` is a right inverse of the symmetric
Pascal matrix. -/
theorem pascalMatrix_mul_signedGram (n : ℕ) :
    pascalMatrix n * ((signedPascal n).transpose * signedPascal n) = 1 := by
  rw [pascalMatrix_eq_lower_mul_transpose,
    signedPascal_eq_lower_mul_signDiagonal, Matrix.transpose_mul,
    pascalSignDiagonal_transpose]
  have hmid := congrArg Matrix.transpose (pascal_lower_sign_lower_eq_sign n)
  simp only [Matrix.transpose_mul, pascalSignDiagonal_transpose] at hmid
  have hmid' :
      (pascalLower n).transpose * pascalSignDiagonal n *
          (pascalLower n).transpose = pascalSignDiagonal n := by
    simpa only [mul_assoc] using hmid
  calc
    pascalLower n * (pascalLower n).transpose *
        (pascalSignDiagonal n * (pascalLower n).transpose *
          (pascalLower n * pascalSignDiagonal n)) =
      pascalLower n *
        ((pascalLower n).transpose * pascalSignDiagonal n *
          (pascalLower n).transpose) *
        (pascalLower n * pascalSignDiagonal n) := by noncomm_ring
    _ = pascalLower n * pascalSignDiagonal n *
          (pascalLower n * pascalSignDiagonal n) := by
            rw [hmid']
    _ = 1 := by
      rw [← signedPascal_eq_lower_mul_signDiagonal]
      exact signedPascal_mul_self n

/-- The same `SᵀS` candidate is also a left inverse. -/
theorem signedGram_mul_pascalMatrix (n : ℕ) :
    ((signedPascal n).transpose * signedPascal n) * pascalMatrix n = 1 := by
  exact mul_eq_one_comm.mp (pascalMatrix_mul_signedGram n)

/-- Higham, 2nd ed., Section 28.4, p. 520: Cohen's printed entry formula for
the inverse of the symmetric Pascal matrix, on its stated lower-triangular
range `i ≥ j`.  Together with `pascalMatrix_mul_signedGram`, the left-hand
side is the `(i,j)` entry of `Pₙ⁻¹`. -/
theorem pascalInverseFormula_apply_of_le {n : ℕ} (i j : Fin n) (hji : j ≤ i) :
    ((signedPascal n).transpose * signedPascal n) i j =
      (-1 : ℝ) ^ (i.val - j.val) *
        ∑ k ∈ Finset.range (n - i.val),
          (Nat.choose (i.val + k) k : ℝ) *
            Nat.choose (i.val + k) (i.val + k - j.val) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, signedPascal]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      ((-1 : ℝ) ^ i.val * Nat.choose k i.val) *
        ((-1 : ℝ) ^ j.val * Nat.choose k j.val)) n]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k : ℕ =>
      ((-1 : ℝ) ^ i.val * Nat.choose k i.val) *
        ((-1 : ℝ) ^ j.val * Nat.choose k j.val))
    (Nat.le_of_lt i.isLt)
  have hlow :
      (∑ k ∈ Finset.range i.val,
        ((-1 : ℝ) ^ i.val * Nat.choose k i.val) *
          ((-1 : ℝ) ^ j.val * Nat.choose k j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k < i.val := Finset.mem_range.mp hk
    simp [Nat.choose_eq_zero_of_lt hki]
  rw [← hsplit, hlow, zero_add, Finset.sum_Ico_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hjk : j.val ≤ i.val + k := by omega
  have hsign : (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ j.val =
      (-1 : ℝ) ^ (i.val - j.val) := by
    calc
      (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ j.val =
          (-1 : ℝ) ^ (i.val - j.val + j.val) * (-1 : ℝ) ^ j.val := by
            rw [Nat.sub_add_cancel hji]
      _ = ((-1 : ℝ) ^ (i.val - j.val) * (-1 : ℝ) ^ j.val) *
          (-1 : ℝ) ^ j.val := by rw [pow_add]
      _ = (-1 : ℝ) ^ (i.val - j.val) := by
        calc
          ((-1 : ℝ) ^ (i.val - j.val) * (-1 : ℝ) ^ j.val) *
              (-1 : ℝ) ^ j.val =
            (-1 : ℝ) ^ (i.val - j.val) *
              (((-1 : ℝ) ^ j.val) * (-1 : ℝ) ^ j.val) := by ring
          _ = (-1 : ℝ) ^ (i.val - j.val) := by
            simp [← mul_pow]
  rw [Nat.choose_symm_add (a := i.val) (b := k)]
  rw [← Nat.choose_symm hjk]
  rw [← hsign]
  ring

end NumStability
