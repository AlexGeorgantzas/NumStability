/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Block

namespace NumStability

open scoped BigOperators

/-! # Higham, Chapter 28: A Gallery of Test Matrices

This module gives dimension-correct, zero-indexed definitions of the principal
matrix families and the deterministic orthogonality part of Stewart's Theorem
28.1.  The distributional Haar conclusion is intentionally not weakened to a
conditional statement; its missing Gaussian/Haar push-forward theorem remains
visible in the Chapter 28 not-proved ledger.
-/

/-! ## Hilbert and Cauchy matrices -/

/-- Higham, 2nd ed., Section 28.1, p. 512: the `n × n` Hilbert matrix.  Source
indices `i,j = 1,...,n` become `Fin n` indices and the denominator is
`i.val + j.val + 1`. -/
noncomputable def hilbertMatrix (n : ℕ) : RSqMat n :=
  fun i j => 1 / (i.val + j.val + 1 : ℕ)

@[simp] theorem hilbertMatrix_apply {n : ℕ} (i j : Fin n) :
    hilbertMatrix n i j = 1 / (i.val + j.val + 1 : ℕ) := rfl

/-- The Hilbert matrix is symmetric, as stated at the start of Section 28.1. -/
theorem hilbertMatrix_transpose (n : ℕ) :
    (hilbertMatrix n).transpose = hilbertMatrix n := by
  ext i j
  simp only [Matrix.transpose_apply, hilbertMatrix_apply]
  rw [add_comm i.val j.val]

/-- The explicit integer-valued expression printed in equation (28.1).  This
definition records the exact candidate entry; the generic inverse proof is a
separate selected obligation recorded in the Chapter 28 ledger. -/
noncomputable def hilbertInverseEntry (n : ℕ) (i j : Fin n) : ℝ :=
  (-1 : ℝ) ^ (i.val + j.val) * (i.val + j.val + 1) *
    Nat.choose (n + i.val) (n - (j.val + 1)) *
    Nat.choose (n + j.val) (n - (i.val + 1)) *
    (Nat.choose (i.val + j.val) i.val : ℝ) ^ 2

/-- Equation (28.1)'s candidate inverse matrix. -/
noncomputable def hilbertInverseFormula (n : ℕ) : RSqMat n :=
  fun i j => hilbertInverseEntry n i j

@[simp] theorem hilbertInverseFormula_apply {n : ℕ} (i j : Fin n) :
    hilbertInverseFormula n i j = hilbertInverseEntry n i j := rfl

/-- Product `0! 1! ... (n-1)!`; the extra `0! = 1` gives exactly the printed
`1! 2! ... (n-1)!` product. -/
noncomputable def factorialProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (Nat.factorial k : ℝ)

/-- Higham, 2nd ed., Section 28.1, p. 513, equation (28.2): the closed-form
candidate for `det(H_n)`. -/
noncomputable def hilbertDetFormula (n : ℕ) : ℝ :=
  factorialProduct n ^ 4 / factorialProduct (2 * n)

/-- Base-order closure check for equation (28.1).  The generic binomial
convolution remains the selected open theorem, but the encoded formula is
proved to be the inverse at order one. -/
theorem hilbert_order_one_inverse_formula :
    hilbertMatrix 1 * hilbertInverseFormula 1 = (1 : RSqMat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, hilbertMatrix, hilbertInverseFormula,
    hilbertInverseEntry]

/-- Base-order closure check for the exact determinant part of (28.2). -/
theorem hilbert_order_one_det_formula :
    Matrix.det (hilbertMatrix 1) = hilbertDetFormula 1 := by
  norm_num [hilbertMatrix, hilbertDetFormula, factorialProduct, Matrix.det_fin_one,
    Finset.prod_range_succ]

/-! ### Alternating-binomial foundation for (28.3)-(28.4) -/

/-- Alternating shifted-binomial sum used to verify the printed triangular
inverse. -/
def altChooseShift (N A r : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (N + 1),
    (-1 : ℤ) ^ m * Nat.choose N m * Nat.choose (A + m) r

theorem altChooseShift_succ_recurrence (N A r : ℕ) :
    altChooseShift (N + 1) A r =
      altChooseShift N A r - altChooseShift N (A + 1) r := by
  have hfirst :
      (Nat.choose A r : ℤ) +
          (∑ m ∈ Finset.range (N + 1),
            (-1 : ℤ) ^ (m + 1) * Nat.choose N (m + 1) *
              Nat.choose (A + (m + 1)) r) =
        altChooseShift N A r := by
    unfold altChooseShift
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, pow_zero, Int.ofNat_one, one_mul,
      Nat.add_zero]
    conv_lhs => rw [Finset.sum_range_succ]
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N)]
    simp only [Int.ofNat_zero, mul_zero, zero_mul, add_zero]
    rw [add_comm]
  have hsecond :
      (∑ m ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ (m + 1) * Nat.choose N m *
          Nat.choose (A + (m + 1)) r) =
        -altChooseShift N (A + 1) r := by
    unfold altChooseShift
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [pow_succ]
    ring_nf
  unfold altChooseShift
  rw [show N + 1 + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, Int.ofNat_one, one_mul,
    Nat.add_zero]
  rw [add_comm]
  calc
    (Nat.choose A r : ℤ) +
        ∑ m ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ (m + 1) * Nat.choose (N + 1) (m + 1) *
            Nat.choose (A + (m + 1)) r =
      ((Nat.choose A r : ℤ) +
        ∑ m ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ (m + 1) * Nat.choose N (m + 1) *
            Nat.choose (A + (m + 1)) r) +
        ∑ m ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ (m + 1) * Nat.choose N m *
            Nat.choose (A + (m + 1)) r := by
              rw [add_assoc]
              apply congrArg (fun z : ℤ => (Nat.choose A r : ℤ) + z)
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro m hm
              rw [Nat.choose_succ_succ]
              push_cast
              ring
    _ = altChooseShift N A r - altChooseShift N (A + 1) r := by
      rw [hfirst, hsecond]
      ring

theorem altChooseShift_eq (N A r : ℕ) :
    altChooseShift N A r =
      if r < N then 0 else (-1 : ℤ) ^ N * Nat.choose A (r - N) := by
  induction N generalizing A r with
  | zero => simp [altChooseShift]
  | succ N ih =>
      rw [altChooseShift_succ_recurrence, ih, ih]
      by_cases hrN : r < N
      · have hrs : r < N + 1 := by omega
        simp [hrN, hrs]
      · by_cases hrEq : r = N
        · subst r
          simp
        · have hNs : N + 1 ≤ r := by omega
          have hnot : ¬ r < N + 1 := by omega
          have hsub : r - N = (r - (N + 1)) + 1 := by omega
          simp [hrN, hnot, hsub, Nat.choose_succ_succ]
          rw [pow_succ]
          ring

theorem altChooseShift_pred_eq_zero (N A : ℕ) (hN : 0 < N) :
    altChooseShift N A (N - 1) = 0 := by
  rw [altChooseShift_eq]
  simp [show N - 1 < N by omega]

/-- Factorial part of the upper-triangular entry in (28.3). -/
noncomputable def hilbertRCore (i k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) ^ 2 /
    ((Nat.factorial (i + k + 1) : ℝ) * Nat.factorial (k - i))

/-- Signed binomial part of the inverse entry in (28.4). -/
noncomputable def hilbertRInvCore (k j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + j) * Nat.choose (k + j) k * Nat.choose j k

/-- One off-diagonal summand in the product of (28.3) and (28.4), reduced to
an alternating shifted-binomial summand. -/
theorem hilbert_core_product_eq_alt
    (i k j : ℕ) (hik : i ≤ k) (hkj : k ≤ j) (hij : i < j) :
    hilbertRCore i k * hilbertRInvCore k j =
      ((-1 : ℝ) ^ (i + j) / (j - i : ℝ)) *
        (((-1 : ℝ) ^ (k - i) * Nat.choose (j - i) (k - i)) *
          Nat.choose (i + j + (k - i)) (j - i - 1)) := by
  have hN : j - i ≠ 0 := by omega
  have hkm : k - i ≤ j - i := Nat.sub_le_sub_right hkj i
  have hchoose1 := Nat.cast_choose ℝ (show k ≤ k + j by omega)
  have hchoose2 := Nat.cast_choose ℝ hkj
  have hchoose3 := Nat.cast_choose ℝ hkm
  have hchoose4 := Nat.cast_choose ℝ
    (show j - i - 1 ≤ i + j + (k - i) by omega)
  unfold hilbertRCore hilbertRInvCore
  rw [hchoose1, hchoose2, hchoose3, hchoose4]
  have hfact : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  have hsign : (-1 : ℝ) ^ (k + j) =
      (-1 : ℝ) ^ (i + j) * (-1 : ℝ) ^ (k - i) := by
    rw [show k + j = (i + j) + (k - i) by omega, pow_add]
  rw [hsign]
  have hdiffne : (j : ℝ) - (i : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hij))
  field_simp [hfact, hN, hdiffne]
  rw [show k + j - k = j by omega]
  rw [show j - i - (k - i) = j - k by omega]
  rw [show i + j + (k - i) = k + j by omega]
  rw [show k + j - (j - i - 1) = i + k + 1 by omega]
  have hfacN : Nat.factorial (j - i) =
      (j - i) * Nat.factorial (j - i - 1) := by
    conv_lhs => rw [show j - i = (j - i - 1) + 1 by omega,
      Nat.factorial_succ]
    rw [show j - i - 1 + 1 = j - i by omega]
  rw [hfacN]
  push_cast
  rw [Nat.cast_sub (le_of_lt hij)]
  ring

theorem hilbert_core_sum_Icc_eq_zero (i j : ℕ) (hij : i < j) :
    (∑ k ∈ Finset.Icc i j, hilbertRCore i k * hilbertRInvCore k j) = 0 := by
  have hIcc : Finset.Icc i j = Finset.Ico i (j + 1) := by
    ext k
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  rw [show j + 1 - i = (j - i) + 1 by omega]
  calc
    (∑ m ∈ Finset.range (j - i + 1),
        hilbertRCore i (i + m) * hilbertRInvCore (i + m) j) =
      ((-1 : ℝ) ^ (i + j) / (j - i : ℝ)) *
        ∑ m ∈ Finset.range (j - i + 1),
          (((-1 : ℝ) ^ m * Nat.choose (j - i) m) *
            Nat.choose (i + j + m) (j - i - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ j - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      simpa [Nat.add_sub_cancel_left] using
        hilbert_core_product_eq_alt i (i + m) j
          (Nat.le_add_right i m) (by omega) hij
    _ = 0 := by
      have halt :
          (∑ m ∈ Finset.range (j - i + 1),
            (((-1 : ℝ) ^ m * Nat.choose (j - i) m) *
              Nat.choose (i + j + m) (j - i - 1))) = 0 := by
        exact_mod_cast altChooseShift_pred_eq_zero (j - i) (i + j) (by omega)
      rw [halt, mul_zero]

/-- Natural-index form of the displayed upper-triangular factor (28.3). -/
noncomputable def hilbertRNat (i j : ℕ) : ℝ :=
  if i ≤ j then Real.sqrt (2 * i + 1 : ℕ) * hilbertRCore i j else 0

/-- Natural-index form of the displayed inverse factor (28.4). -/
noncomputable def hilbertRInvNat (i j : ℕ) : ℝ :=
  if i ≤ j then Real.sqrt (2 * j + 1 : ℕ) * hilbertRInvCore i j else 0

/-- Higham, 2nd ed., Section 28.1, p. 513, equation (28.3): the upper-
triangular Cholesky-factor entry formula, translated to zero-based indices. -/
noncomputable def hilbertInvCholeskyEntry (n : ℕ) (i j : Fin n) : ℝ :=
  hilbertRNat i.val j.val

/-- Higham, 2nd ed., Section 28.1, p. 513, equation (28.4): the inverse of the
upper Cholesky-factor candidate, in zero-based indices. -/
noncomputable def hilbertInvCholeskyInverseEntry (n : ℕ) (i j : Fin n) : ℝ :=
  hilbertRInvNat i.val j.val

/-- Matrix form of (28.3). -/
noncomputable def hilbertCholeskyFactor (n : ℕ) : RSqMat n :=
  fun i j => hilbertInvCholeskyEntry n i j

/-- Matrix form of (28.4). -/
noncomputable def hilbertCholeskyFactorInverse (n : ℕ) : RSqMat n :=
  fun i j => hilbertInvCholeskyInverseEntry n i j

theorem hilbert_R_diag_product (i : ℕ) :
    hilbertRNat i i * hilbertRInvNat i i = 1 := by
  simp only [hilbertRNat, hilbertRInvNat, le_refl, ↓reduceIte]
  unfold hilbertRCore hilbertRInvCore
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one,
    Nat.choose_self, Even.neg_one_pow (Even.add_self i)]
  rw [Nat.cast_choose ℝ (show i ≤ i + i by omega)]
  have hfact : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  have hsqrt : Real.sqrt (2 * i + 1 : ℕ) ^ 2 = (2 * i + 1 : ℕ) := by
    rw [Real.sq_sqrt]
    positivity
  rw [show i + i - i = i by omega]
  have hfac : Nat.factorial (i + i + 1) =
      (i + i + 1) * Nat.factorial (i + i) := by
    rw [Nat.factorial_succ]
  rw [hfac]
  push_cast
  field_simp [hfact]
  push_cast at hsqrt
  nlinarith [hsqrt]

/-- Higham equations (28.3)-(28.4), generic closure: the two printed upper-
triangular matrices multiply to the identity for every order. -/
theorem hilbertCholeskyFactor_mul_inverse (n : ℕ) :
    hilbertCholeskyFactor n * hilbertCholeskyFactorInverse n = 1 := by
  ext i j
  simp only [Matrix.mul_apply, hilbertCholeskyFactor,
    hilbertCholeskyFactorInverse, hilbertInvCholeskyEntry,
    hilbertInvCholeskyInverseEntry]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => hilbertRNat i.val k * hilbertRInvNat k j.val) n]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i.val]
    · simpa using hilbert_R_diag_product i.val
    · intro k hk hki
      have hkn : k < n := Finset.mem_range.mp hk
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · simp [hilbertRNat, hilbertRInvNat, show ¬i.val ≤ k by omega]
      · simp [hilbertRNat, hilbertRInvNat, show ¬k ≤ i.val by omega]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr i.isLt)).elim
  · rcases lt_or_gt_of_ne (show i.val ≠ j.val by simpa [Fin.ext_iff] using hij) with hijlt | hjilt
    · have hsub : Finset.Icc i.val j.val ⊆ Finset.range n := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        exact Finset.mem_range.mpr (lt_of_le_of_lt hk.2 j.isLt)
      calc
        (∑ k ∈ Finset.range n, hilbertRNat i.val k * hilbertRInvNat k j.val) =
            ∑ k ∈ Finset.Icc i.val j.val,
              hilbertRNat i.val k * hilbertRInvNat k j.val := by
          symm
          apply Finset.sum_subset hsub
          intro k hkn hkIcc
          by_cases hik : i.val ≤ k
          · have hkj : ¬k ≤ j.val := by
              intro h
              exact hkIcc (Finset.mem_Icc.mpr ⟨hik, h⟩)
            simp [hilbertRNat, hilbertRInvNat, hik, hkj]
          · simp [hilbertRNat, hik]
        _ = (Real.sqrt (2 * i.val + 1 : ℕ) *
              Real.sqrt (2 * j.val + 1 : ℕ)) *
            ∑ k ∈ Finset.Icc i.val j.val,
              hilbertRCore i.val k * hilbertRInvCore k j.val := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          simp [hilbertRNat, hilbertRInvNat, hk'.1, hk'.2]
          ring
        _ = 0 := by rw [hilbert_core_sum_Icc_eq_zero i.val j.val hijlt, mul_zero]
        _ = (1 : RSqMat n) i j := by simp [hij]
    · have hzero :
          (∑ k ∈ Finset.range n,
            hilbertRNat i.val k * hilbertRInvNat k j.val) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hik : i.val ≤ k
        · have hkj : ¬k ≤ j.val := by omega
          simp [hilbertRNat, hilbertRInvNat, hik, hkj]
        · simp [hilbertRNat, hik]
      rw [hzero]
      simp [hij]

/-- The printed inverse is two-sided. -/
theorem hilbertCholeskyFactorInverse_mul (n : ℕ) :
    hilbertCholeskyFactorInverse n * hilbertCholeskyFactor n = 1 := by
  exact mul_eq_one_comm.mp (hilbertCholeskyFactor_mul_inverse n)

/-- Higham, 2nd ed., Section 28.1, pp. 514-515: a rectangular Cauchy matrix
`C_ij = 1/(x_i+y_j)`. -/
noncomputable def cauchyMatrix {m n : ℕ} (x : RVec m) (y : RVec n) : RMat m n :=
  fun i j => 1 / (x i + y j)

@[simp] theorem cauchyMatrix_apply {m n : ℕ} (x : RVec m) (y : RVec n)
    (i : Fin m) (j : Fin n) :
    cauchyMatrix x y i j = 1 / (x i + y j) := rfl

/-- Transposition swaps the two node families in a rectangular Cauchy matrix. -/
theorem cauchyMatrix_transpose {m n : ℕ} (x : RVec m) (y : RVec n) :
    (cauchyMatrix x y).transpose = cauchyMatrix y x := by
  ext i j
  simp [cauchyMatrix, add_comm]

/-- The exact determinant product printed in Section 28.1 for a square Cauchy
matrix.  The filtered products use the natural `Fin n` order. -/
noncomputable def cauchyDetFormula (n : ℕ) (x y : RVec n) : ℝ :=
  (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (x j - x i) * (y j - y i)) /
    (∏ i : Fin n, ∏ j : Fin n, (x i + y j))

/-- The entrywise inverse formula printed for a nonsingular square Cauchy
matrix.  In an inverse entry `(i,j)`, `i` indexes the `y` nodes and `j` the
`x` nodes. -/
noncomputable def cauchyInverseEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  (∏ k : Fin n, (x j + y k) * (x k + y i)) /
    ((x j + y i) *
      (∏ k ∈ Finset.univ.erase j, (x j - x k)) *
      (∏ k ∈ Finset.univ.erase i, (y i - y k)))

noncomputable def cauchyInverseFormula
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j => cauchyInverseEntry n x y i j

/-- Base-order validation of the generic Cauchy inverse formula. -/
theorem cauchy_order_one_inverse_formula
    (x y : RVec 1) (hxy : x 0 + y 0 ≠ 0) :
    cauchyMatrix x y * cauchyInverseFormula 1 x y = (1 : RSqMat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, cauchyMatrix, cauchyInverseFormula,
    cauchyInverseEntry, hxy]

/-- Base-order validation of the Cauchy determinant product. -/
theorem cauchy_order_one_det_formula (x y : RVec 1) :
    Matrix.det (cauchyMatrix x y) = cauchyDetFormula 1 x y := by
  simp [cauchyMatrix, cauchyDetFormula]

/-! ## Randsvd matrices and Stewart products -/

/-- A rectangular diagonal matrix, with a source-indexed singular-value
function.  Entries outside the common diagonal are zero. -/
noncomputable def rectangularDiagonal {m n : ℕ} (σ : ℕ → ℝ) : RMat m n :=
  fun i j => if i.val = j.val then σ i.val else 0

/-- Higham, 2nd ed., Section 28.3, p. 517: `A = U Σ Vᵀ`. -/
noncomputable def randsvdMatrix {m n : ℕ} (U : RSqMat m) (σ : ℕ → ℝ)
    (V : RSqMat n) : RMat m n :=
  U * (rectangularDiagonal (m := m) (n := n) σ) * V.transpose

/-- One-large-singular-value distribution from Section 28.3. -/
noncomputable def oneLargeSingularValues (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | _ + 1 => α⁻¹

/-- One-small-singular-value distribution, parameterized by the matrix order. -/
noncomputable def oneSmallSingularValues (n : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  if i + 1 = n then α⁻¹ else 1

/-- Geometrically distributed singular values from Section 28.3.  The source
parameter is `β = α^(1/(n-1))`, and zero-based index `i` has value `β⁻ⁱ`. -/
noncomputable def geometricSingularValues (n : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  let β := α ^ (1 / (n - 1 : ℝ))
  (β⁻¹) ^ i

/-- Arithmetically distributed singular values from Section 28.3, translated
to zero-based index `i`. -/
noncomputable def arithmeticSingularValues (n : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  1 - (1 - α⁻¹) * i / (n - 1 : ℝ)

/-- Product of a list of square matrices, in source order. -/
noncomputable def matrixListProduct {n : ℕ} :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => idMatrix n
  | A :: As => matMul n A (matrixListProduct As)

/-- A finite product of orthogonal matrices is orthogonal. -/
theorem matrixListProduct_isOrthogonal {n : ℕ}
    (Ps : List (Fin n → Fin n → ℝ))
    (hPs : ∀ P ∈ Ps, IsOrthogonal n P) :
    IsOrthogonal n (matrixListProduct Ps) := by
  induction Ps with
  | nil => exact IsOrthogonal.id n
  | cons P Ps ih =>
      exact (hPs P (by simp)).mul
        (ih (fun Q hQ => hPs Q (by simp [hQ])))

/-- The deterministic product in Stewart's Theorem 28.1: `Q = D P₁...Pₙ₋₁`. -/
noncomputable def stewartOrthogonalProduct {n : ℕ}
    (D : Fin n → Fin n → ℝ) (Ps : List (Fin n → Fin n → ℝ)) :
    Fin n → Fin n → ℝ :=
  matMul n D (matrixListProduct Ps)

/-- Higham, 2nd ed., Section 28.3, p. 517, Theorem 28.1 (deterministic
orthogonality component): an orthogonal sign diagonal times the embedded
Householder transformations is orthogonal.  This theorem assumes only the
elementary orthogonality premises, not the source's probabilistic Haar
conclusion. -/
theorem higham28_theorem28_1_product_orthogonal {n : ℕ}
    (D : Fin n → Fin n → ℝ) (Ps : List (Fin n → Fin n → ℝ))
    (hD : IsOrthogonal n D)
    (hPs : ∀ P ∈ Ps, IsOrthogonal n P) :
    IsOrthogonal n (stewartOrthogonalProduct D Ps) := by
  exact hD.mul (matrixListProduct_isOrthogonal Ps hPs)

/-! ## Pascal, Toeplitz, and companion matrices -/

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

/-- Higham, 2nd ed., Section 28.5, p. 521: the tridiagonal Toeplitz matrix
`T_n(c,d,e)`. -/
noncomputable def tridiagonalToeplitz (n : ℕ) (c d e : ℝ) : RSqMat n :=
  fun i j =>
    if i = j then d
    else if i.val + 1 = j.val then e
    else if j.val + 1 = i.val then c
    else 0

@[simp] theorem tridiagonalToeplitz_diag {n : ℕ} (c d e : ℝ) (i : Fin n) :
    tridiagonalToeplitz n c d e i i = d := by
  simp [tridiagonalToeplitz]

/-- Transposition interchanges the sub- and superdiagonal parameters. -/
theorem tridiagonalToeplitz_transpose (n : ℕ) (c d e : ℝ) :
    (tridiagonalToeplitz n c d e).transpose =
      tridiagonalToeplitz n e d c := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [tridiagonalToeplitz]
  · by_cases hij1 : i.val + 1 = j.val
    · have hji1 : ¬j.val + 1 = i.val := by omega
      have hji : j ≠ i := Ne.symm hij
      simp [Matrix.transpose_apply, tridiagonalToeplitz, hij, hji, hij1, hji1]
    · by_cases hji1 : j.val + 1 = i.val
      · have hji : j ≠ i := Ne.symm hij
        simp [Matrix.transpose_apply, tridiagonalToeplitz, hij, hji, hij1, hji1]
      · have hji : j ≠ i := Ne.symm hij
        simp [Matrix.transpose_apply, tridiagonalToeplitz, hij, hji, hij1, hji1]

/-- The numerator in Higham's p. 522 Green-function inverse of
`Tₙ(-1,2,-1)`, expressed with zero-based indices. -/
def secondDifferenceGreenNum (n i j : ℕ) : ℕ :=
  Nat.min (i + 1) (j + 1) * (n - Nat.max i j)

/-- Higham, 2nd ed., Section 28.5, p. 522: the entrywise inverse candidate
`min(i,j) * (n - max(i,j) + 1) / (n + 1)`, translated to zero-based indices. -/
noncomputable def secondDifferenceInverse (n : ℕ) : RSqMat n :=
  fun i j => (secondDifferenceGreenNum n i.val j.val : ℝ) / (n + 1 : ℕ)

theorem secondDifferenceGreenNum_of_le (n i j : ℕ) (hij : i ≤ j) :
    secondDifferenceGreenNum n i j = (i + 1) * (n - j) := by
  have hmin : Nat.min (i + 1) (j + 1) = i + 1 := Nat.min_eq_left (by omega)
  have hmax : Nat.max i j = j := Nat.max_eq_right hij
  simp only [secondDifferenceGreenNum, hmin, hmax]

theorem secondDifferenceGreenNum_of_ge (n i j : ℕ) (hji : j ≤ i) :
    secondDifferenceGreenNum n i j = (j + 1) * (n - i) := by
  have hmin : Nat.min (i + 1) (j + 1) = j + 1 := Nat.min_eq_right (by omega)
  have hmax : Nat.max i j = i := Nat.max_eq_left hji
  simp only [secondDifferenceGreenNum, hmin, hmax]

/-- The discrete second difference of the Green numerator is `(n + 1)δᵢⱼ`.
This is the arithmetic core of the inverse verification. -/
theorem secondDifferenceGreenNum_recurrence
    (n i j : ℕ) (hi : i < n) (hj : j < n) :
    (2 : ℤ) * secondDifferenceGreenNum n i j -
        secondDifferenceGreenNum n (i + 1) j -
        (if 0 < i then (secondDifferenceGreenNum n (i - 1) j : ℤ) else 0) =
      if i = j then (n + 1 : ℕ) else 0 := by
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · subst j
      rw [secondDifferenceGreenNum_of_le n 0 0 (by omega)]
      rw [secondDifferenceGreenNum_of_ge n 1 0 (by omega)]
      simp
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    · rw [secondDifferenceGreenNum_of_le n 0 j (by omega)]
      rw [secondDifferenceGreenNum_of_le n 1 j (by omega)]
      have h0j : (0 : ℕ) ≠ j := by omega
      simp [h0j]
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    rcases lt_trichotomy i j with hij | hij | hji
    · rw [secondDifferenceGreenNum_of_le n i j (by omega)]
      rw [secondDifferenceGreenNum_of_le n (i + 1) j (by omega)]
      rw [secondDifferenceGreenNum_of_le n (i - 1) j (by omega)]
      simp [hipos, hij.ne]
      ring
    · subst j
      rw [secondDifferenceGreenNum_of_le n i i (by omega)]
      rw [secondDifferenceGreenNum_of_ge n (i + 1) i (by omega)]
      rw [secondDifferenceGreenNum_of_le n (i - 1) i (by omega)]
      simp [hipos]
      push_cast [Nat.cast_sub (by omega : i + 1 ≤ n),
        Nat.cast_sub (by omega : i ≤ n)]
      ring
    · rw [secondDifferenceGreenNum_of_ge n i j (by omega)]
      rw [secondDifferenceGreenNum_of_ge n (i + 1) j (by omega)]
      rw [secondDifferenceGreenNum_of_ge n (i - 1) j (by omega)]
      have hijne : i ≠ j := by omega
      simp [hipos, hijne]
      push_cast [Nat.cast_sub (by omega : i + 1 ≤ n),
        Nat.cast_sub (by omega : i ≤ n),
        Nat.cast_sub (by omega : i - 1 ≤ n)]
      have himCast : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
      rw [himCast]
      ring

/-- Multiplication on the right by a tridiagonal Toeplitz matrix reduces to
the diagonal and its at most two neighboring rows. -/
theorem tridiagonalToeplitz_mul_apply_right
    (n : ℕ) (c d e : ℝ) (A : RSqMat n) (i j : Fin n) :
    (tridiagonalToeplitz n c d e * A) i j =
      d * A i j +
        (if h : i.val + 1 < n then e * A ⟨i.val + 1, h⟩ j else 0) +
        (if h : 0 < i.val then c * A ⟨i.val - 1, by omega⟩ j else 0) := by
  simp only [Matrix.mul_apply]
  calc
    (∑ x, tridiagonalToeplitz n c d e i x * A x j) =
        ∑ x, ((if i = x then d else 0) +
          (if i.val + 1 = x.val then e else 0) +
          (if x.val + 1 = i.val then c else 0)) * A x j := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hix : i = x
      · subst x
        simp [tridiagonalToeplitz]
      · by_cases hs : i.val + 1 = x.val
        · have hb : ¬x.val + 1 = i.val := by omega
          simp [tridiagonalToeplitz, hix, hs, hb]
        · by_cases hp : x.val + 1 = i.val
          · simp [tridiagonalToeplitz, hix, hs, hp]
          · simp [tridiagonalToeplitz, hix, hs, hp]
    _ = (∑ x, (if i = x then d else 0) * A x j) +
          (∑ x, (if i.val + 1 = x.val then e else 0) * A x j) +
          (∑ x, (if x.val + 1 = i.val then c else 0) * A x j) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = d * A i j +
        (if h : i.val + 1 < n then e * A ⟨i.val + 1, h⟩ j else 0) +
        (if h : 0 < i.val then c * A ⟨i.val - 1, by omega⟩ j else 0) := by
      simp only [ite_mul, zero_mul]
      have hdiag : (∑ x : Fin n, if i = x then d * A x j else 0) =
          d * A i j := by simp
      rw [hdiag]
      by_cases hs : i.val + 1 < n
      · let ip : Fin n := ⟨i.val + 1, hs⟩
        have hsUnique : ∀ x : Fin n, i.val + 1 = x.val ↔ x = ip := by
          intro x
          constructor
          · intro h
            apply Fin.ext
            simpa [ip] using h.symm
          · intro h
            subst x
            simp [ip]
        simp_rw [hsUnique]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ x : Fin n, x.val + 1 = i.val ↔ x = im := by
            intro x
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst x
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, ip, im]
        · have hpNone : ∀ x : Fin n, ¬x.val + 1 = i.val := by
            intro x h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp, ip]
      · have hsNone : ∀ x : Fin n, ¬i.val + 1 = x.val := by
          intro x h
          omega
        simp_rw [if_neg (hsNone _)]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ x : Fin n, x.val + 1 = i.val ↔ x = im := by
            intro x
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst x
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, im]
        · have hpNone : ∀ x : Fin n, ¬x.val + 1 = i.val := by
            intro x h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp]

theorem secondDifferenceGreenNum_succ_zero
    (n i j : ℕ) (hi : i < n) (hj : j < n) (hs : ¬i + 1 < n) :
    secondDifferenceGreenNum n (i + 1) j = 0 := by
  rw [secondDifferenceGreenNum_of_ge n (i + 1) j (by omega)]
  simp [show n - (i + 1) = 0 by omega]

/-- The p. 522 Green matrix is a right inverse of `Tₙ(-1,2,-1)`. -/
theorem tridiagonalToeplitz_mul_secondDifferenceInverse (n : ℕ) :
    tridiagonalToeplitz n (-1) 2 (-1) * secondDifferenceInverse n = 1 := by
  ext i j
  rw [tridiagonalToeplitz_mul_apply_right]
  have hrec := secondDifferenceGreenNum_recurrence n i.val j.val i.isLt j.isLt
  have hrecR := congrArg (fun z : ℤ => (z : ℝ)) hrec
  norm_num at hrecR
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp] using hrecR
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp] using hrecR
  · have hsz := secondDifferenceGreenNum_succ_zero n i.val j.val i.isLt j.isLt hs
    by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp, hsz] using hrecR
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp, hsz] using hrecR

/-- The Green matrix is also a left inverse; finite square matrices over `ℝ`
are Dedekind-finite. -/
theorem secondDifferenceInverse_mul_tridiagonalToeplitz (n : ℕ) :
    secondDifferenceInverse n * tridiagonalToeplitz n (-1) 2 (-1) = 1 := by
  exact mul_eq_one_comm.mp (tridiagonalToeplitz_mul_secondDifferenceInverse n)

/-- Higham, 2nd ed., Section 28.6, pp. 522-523: the companion matrix for
coefficients `a₀,...,aₙ₋₁`.  A natural-indexed coefficient function avoids a
spurious nonempty-dimension hypothesis in the definition. -/
noncomputable def companionMatrix (n : ℕ) (a : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if i.val = 0 then a (n - 1 - j.val)
    else if i.val = j.val + 1 then 1
    else 0

/-- The power vector printed on p. 523, translated to zero-based indices. -/
noncomputable def companionEigenvector (n : ℕ) (z : ℂ) : Fin n → ℂ :=
  fun i => z ^ (n - 1 - i.val)

/-- Higham, Section 28.6, p. 523: if `z` satisfies the monic polynomial root
equation associated with the displayed companion matrix, then
`[z^(n-1), z^(n-2), ..., z, 1]ᵀ` is an eigenvector with eigenvalue `z`.
The hypothesis is the polynomial equation, not the eigenvector conclusion. -/
theorem companionMatrix_mulVec_companionEigenvector
    {n : ℕ} (a : ℕ → ℂ) (z : ℂ)
    (hroot : (∑ j : Fin n, a (n - 1 - j.val) * z ^ (n - 1 - j.val)) = z ^ n) :
    Matrix.mulVec (companionMatrix n a) (companionEigenvector n z) =
      z • companionEigenvector n z := by
  funext i
  by_cases hi : i.val = 0
  · simp only [Matrix.mulVec, dotProduct, companionMatrix, companionEigenvector,
      hi, if_pos]
    rw [hroot]
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    change z ^ n = z * z ^ (n - 1 - i.val)
    rw [hi, Nat.sub_zero, show n = (n - 1) + 1 by omega, pow_succ]
    exact mul_comm _ _
  · simp only [Matrix.mulVec, dotProduct, companionMatrix, companionEigenvector,
      hi, if_false]
    simp only [ite_mul, one_mul, zero_mul, Pi.smul_apply, smul_eq_mul]
    have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
    let k : Fin n := ⟨i.val - 1, by omega⟩
    rw [Finset.sum_eq_single k]
    · simp only [k, Nat.sub_add_cancel hipos, ↓reduceIte]
      rw [show n - 1 - (i.val - 1) = (n - 1 - i.val) + 1 by omega, pow_succ]
      exact mul_comm _ _
    · intro j _ hjk
      have hneq : ¬i.val = j.val + 1 := by
        intro hij
        apply hjk
        apply Fin.ext
        simp only [k]
        omega
      simp [hneq]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim

end NumStability
