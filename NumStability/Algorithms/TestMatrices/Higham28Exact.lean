/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28

/-! # Higham Chapter 28: exact Hilbert identities

This companion module proves the generic factorization, determinant, and
entrywise inverse formulas (28.1)-(28.4).  It is separated from `Higham28` to
keep the foundational definitions and the long factorial telescoping proofs
independently checkable.
-/

namespace NumStability

noncomputable def hilbertGramTelescoper (i j k : ℕ) : ℝ :=
  if k ≤ i then
    -((Nat.factorial i : ℝ) ^ 2 * (Nat.factorial j : ℝ) ^ 2) /
      ((Nat.factorial (i + k) : ℝ) * Nat.factorial (i - k) *
        Nat.factorial (j + k) * Nat.factorial (j - k) * (i + j + 1 : ℕ))
  else 0

theorem hilbert_gram_term_eq_telescoper_sub
    (i j k : ℕ) (hk : k ≤ i) (hij : i ≤ j) :
    (2 * k + 1 : ℝ) * hilbertRCore k i * hilbertRCore k j =
      hilbertGramTelescoper i j (k + 1) - hilbertGramTelescoper i j k := by
  have hfact : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  by_cases hki : k = i
  · subst k
    simp only [hilbertGramTelescoper, le_refl, ↓reduceIte,
      show ¬i + 1 ≤ i by omega]
    unfold hilbertRCore
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
    rw [show i + i + 1 = (i + i) + 1 by omega, Nat.factorial_succ]
    rw [show i + j + 1 = (i + j) + 1 by omega, Nat.factorial_succ]
    push_cast
    field_simp [hfact]
    norm_num
    ring_nf
  · have hlt : k < i := lt_of_le_of_ne hk hki
    simp only [hilbertGramTelescoper, hk, ↓reduceIte,
      show k + 1 ≤ i by omega]
    unfold hilbertRCore
    have hfi : Nat.factorial (k + i + 1) =
        (i + k + 1) * Nat.factorial (i + k) := by
      rw [show k + i + 1 = (i + k) + 1 by omega, Nat.factorial_succ]
    have hfj : Nat.factorial (k + j + 1) =
        (j + k + 1) * Nat.factorial (j + k) := by
      rw [show k + j + 1 = (j + k) + 1 by omega, Nat.factorial_succ]
    have hfinext : Nat.factorial (i + (k + 1)) =
        (i + k + 1) * Nat.factorial (i + k) := by
      rw [show i + (k + 1) = (i + k) + 1 by omega, Nat.factorial_succ]
    have hfjnext : Nat.factorial (j + (k + 1)) =
        (j + k + 1) * Nat.factorial (j + k) := by
      rw [show j + (k + 1) = (j + k) + 1 by omega, Nat.factorial_succ]
    have hfisub : Nat.factorial (i - k) =
        (i - k) * Nat.factorial (i - (k + 1)) := by
      conv_lhs => rw [show i - k = (i - (k + 1)) + 1 by omega,
        Nat.factorial_succ]
      rw [show i - (k + 1) + 1 = i - k by omega]
    have hfjsub : Nat.factorial (j - k) =
        (j - k) * Nat.factorial (j - (k + 1)) := by
      conv_lhs => rw [show j - k = (j - (k + 1)) + 1 by omega,
        Nat.factorial_succ]
      rw [show j - (k + 1) + 1 = j - k by omega]
    rw [hfi, hfj, hfinext, hfjnext, hfisub, hfjsub]
    push_cast [Nat.cast_sub hk,
      Nat.cast_sub (by omega : k + 1 ≤ i),
      Nat.cast_sub (by omega : k ≤ j),
      Nat.cast_sub (by omega : k + 1 ≤ j)]
    have hikR : (i : ℝ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show i ≠ k by omega))
    have hjkR : (j : ℝ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show j ≠ k by omega))
    field_simp [hfact, hikR, hjkR]
    norm_num
    ring

theorem hilbert_gram_sum (i j : ℕ) (hij : i ≤ j) :
    (∑ k ∈ Finset.range (i + 1),
      (2 * k + 1 : ℝ) * hilbertRCore k i * hilbertRCore k j) =
      1 / (i + j + 1 : ℕ) := by
  calc
    (∑ k ∈ Finset.range (i + 1),
      (2 * k + 1 : ℝ) * hilbertRCore k i * hilbertRCore k j) =
        ∑ k ∈ Finset.range (i + 1),
          (hilbertGramTelescoper i j (k + 1) - hilbertGramTelescoper i j k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hilbert_gram_term_eq_telescoper_sub i j k
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hij
    _ = hilbertGramTelescoper i j (i + 1) - hilbertGramTelescoper i j 0 := by
      exact Finset.sum_range_sub (hilbertGramTelescoper i j) (i + 1)
    _ = 1 / (i + j + 1 : ℕ) := by
      simp [hilbertGramTelescoper]
      field_simp

theorem hilbert_choleskyGram_apply_of_le
    {n : ℕ} (i j : Fin n) (hij : i.val ≤ j.val) :
    ((hilbertCholeskyFactor n).transpose * hilbertCholeskyFactor n) i j =
      hilbertMatrix n i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hilbertCholeskyFactor,
    hilbertInvCholeskyEntry]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => hilbertRNat k i.val * hilbertRNat k j.val) n]
  have hsubset : Finset.range (i.val + 1) ⊆ Finset.range n :=
    Finset.range_mono (Nat.succ_le_of_lt i.isLt)
  calc
    (∑ k ∈ Finset.range n, hilbertRNat k i.val * hilbertRNat k j.val) =
        ∑ k ∈ Finset.range (i.val + 1),
          hilbertRNat k i.val * hilbertRNat k j.val := by
      symm
      apply Finset.sum_subset hsubset
      intro k hkn hki
      have hik : ¬k ≤ i.val := by
        have hnmem : ¬k < i.val + 1 := by simpa using hki
        omega
      simp [hilbertRNat, hik]
    _ = ∑ k ∈ Finset.range (i.val + 1),
          (2 * k + 1 : ℝ) * hilbertRCore k i.val * hilbertRCore k j.val := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≤ i.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hkj : k ≤ j.val := le_trans hki hij
      simp only [hilbertRNat, hki, hkj, ↓reduceIte]
      have hsqrt : Real.sqrt (2 * k + 1 : ℕ) ^ 2 =
          ((2 * k + 1 : ℕ) : ℝ) := by
        rw [Real.sq_sqrt]
        positivity
      calc
        Real.sqrt (2 * k + 1 : ℕ) * hilbertRCore k i.val *
            (Real.sqrt (2 * k + 1 : ℕ) * hilbertRCore k j.val) =
          Real.sqrt (2 * k + 1 : ℕ) ^ 2 *
            hilbertRCore k i.val * hilbertRCore k j.val := by ring
        _ = (2 * k + 1 : ℝ) * hilbertRCore k i.val *
            hilbertRCore k j.val := by
              rw [hsqrt]
              push_cast
              ring
    _ = 1 / (i.val + j.val + 1 : ℕ) := hilbert_gram_sum i.val j.val hij
    _ = hilbertMatrix n i j := rfl

/-- Higham equation (28.3), generic factorization bridge:
`Hₙ = RᵀR` for the printed upper-triangular factor. -/
theorem hilbertMatrix_eq_choleskyGram (n : ℕ) :
    hilbertMatrix n =
      (hilbertCholeskyFactor n).transpose * hilbertCholeskyFactor n := by
  have hsymm :
      ((hilbertCholeskyFactor n).transpose * hilbertCholeskyFactor n).transpose =
        (hilbertCholeskyFactor n).transpose * hilbertCholeskyFactor n := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  ext i j
  by_cases hij : i.val ≤ j.val
  · exact (hilbert_choleskyGram_apply_of_le i j hij).symm
  · calc
      hilbertMatrix n i j = hilbertMatrix n j i := by
        simp only [hilbertMatrix_apply]
        rw [add_comm i.val j.val]
      _ = ((hilbertCholeskyFactor n).transpose * hilbertCholeskyFactor n) j i :=
        (hilbert_choleskyGram_apply_of_le j i (by omega)).symm
      _ = ((hilbertCholeskyFactor n).transpose * hilbertCholeskyFactor n) i j := by
        have happ := congrArg (fun M : RSqMat n => M i j) hsymm
        simpa [Matrix.transpose_apply] using happ

theorem hilbertCholeskyFactor_blockTriangular (n : ℕ) :
    (hilbertCholeskyFactor n).BlockTriangular id := by
  intro i j hji
  simp [hilbertCholeskyFactor, hilbertInvCholeskyEntry, hilbertRNat,
    show ¬i.val ≤ j.val by exact not_le_of_gt hji]

theorem hilbertCholeskyFactor_det (n : ℕ) :
    Matrix.det (hilbertCholeskyFactor n) =
      ∏ i : Fin n, hilbertRNat i.val i.val := by
  rw [Matrix.det_of_upperTriangular (hilbertCholeskyFactor_blockTriangular n)]
  rfl

theorem hilbertRNat_diag_sq (i : ℕ) :
    hilbertRNat i i ^ 2 =
      (Nat.factorial i : ℝ) ^ 4 /
        ((Nat.factorial (2 * i) : ℝ) * Nat.factorial (2 * i + 1)) := by
  simp only [hilbertRNat, le_refl, ↓reduceIte]
  unfold hilbertRCore
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
  have hsqrt : Real.sqrt (2 * i + 1 : ℕ) ^ 2 =
      ((2 * i + 1 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  rw [show i + i + 1 = 2 * i + 1 by omega]
  rw [show 2 * i + 1 = (2 * i) + 1 by omega, Nat.factorial_succ]
  field_simp
  rw [hsqrt]
  push_cast
  ring

theorem hilbertDetFormula_succ (n : ℕ) :
    hilbertDetFormula (n + 1) =
      hilbertDetFormula n * hilbertRNat n n ^ 2 := by
  rw [hilbertRNat_diag_sq]
  unfold hilbertDetFormula factorialProduct
  rw [Finset.prod_range_succ]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Finset.prod_range_succ, Finset.prod_range_succ]
  have hfact : ∀ k : ℕ, (Nat.factorial k : ℝ) ≠ 0 := by
    intro k
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfact]

theorem hilbert_diag_sq_product_nat (n : ℕ) :
    (∏ i ∈ Finset.range n, hilbertRNat i i ^ 2) = hilbertDetFormula n := by
  induction n with
  | zero => simp [hilbertDetFormula, factorialProduct]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, hilbertDetFormula_succ]

/-- Higham equation (28.2), exact generic determinant formula. -/
theorem hilbert_det_formula (n : ℕ) :
    Matrix.det (hilbertMatrix n) = hilbertDetFormula n := by
  rw [hilbertMatrix_eq_choleskyGram, Matrix.det_mul, Matrix.det_transpose,
    hilbertCholeskyFactor_det]
  rw [← pow_two]
  rw [Fin.prod_univ_eq_prod_range (fun i => hilbertRNat i i) n]
  rw [← Finset.prod_pow]
  exact hilbert_diag_sq_product_nat n

/-- The factor inverse from (28.4) gives a concrete generic inverse of the
Hilbert matrix. -/
theorem hilbertMatrix_mul_factorInverseGram (n : ℕ) :
    hilbertMatrix n *
      (hilbertCholeskyFactorInverse n *
        (hilbertCholeskyFactorInverse n).transpose) = 1 := by
  rw [hilbertMatrix_eq_choleskyGram]
  calc
    (hilbertCholeskyFactor n).transpose * hilbertCholeskyFactor n *
        (hilbertCholeskyFactorInverse n *
          (hilbertCholeskyFactorInverse n).transpose) =
      (hilbertCholeskyFactor n).transpose *
        (hilbertCholeskyFactor n * hilbertCholeskyFactorInverse n) *
          (hilbertCholeskyFactorInverse n).transpose := by noncomm_ring
    _ = (hilbertCholeskyFactor n).transpose *
          (hilbertCholeskyFactorInverse n).transpose := by
      rw [hilbertCholeskyFactor_mul_inverse, mul_one]
    _ = 1 := by
      rw [← Matrix.transpose_mul, hilbertCholeskyFactorInverse_mul,
        Matrix.transpose_one]

theorem factorInverseGram_mul_hilbertMatrix (n : ℕ) :
    (hilbertCholeskyFactorInverse n *
        (hilbertCholeskyFactorInverse n).transpose) * hilbertMatrix n = 1 := by
  exact mul_eq_one_comm.mp (hilbertMatrix_mul_factorInverseGram n)

noncomputable def hilbertRInvAbsCore (i k : ℕ) : ℝ :=
  Nat.choose (i + k) i * Nat.choose k i

noncomputable def hilbertInverseTelescoper (i j N : ℕ) : ℝ :=
  if j < N then
    ((Nat.factorial (N + i) : ℝ) * Nat.factorial (N + j)) /
      ((Nat.factorial (N - (j + 1)) : ℝ) * Nat.factorial (N - (i + 1)) *
        (Nat.factorial i : ℝ) ^ 2 * (Nat.factorial j : ℝ) ^ 2 *
        (i + j + 1 : ℕ))
  else 0

theorem hilbert_inverse_abs_term_eq_telescoper_sub
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    (2 * k + 1 : ℝ) * hilbertRInvAbsCore i k * hilbertRInvAbsCore j k =
      hilbertInverseTelescoper i j (k + 1) -
        hilbertInverseTelescoper i j k := by
  have hfact : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 := by
    intro m
    exact_mod_cast Nat.factorial_ne_zero m
  unfold hilbertRInvAbsCore
  rw [Nat.cast_choose ℝ (show i ≤ i + k by omega), Nat.cast_choose ℝ (by omega : i ≤ k),
    Nat.cast_choose ℝ (show j ≤ j + k by omega), Nat.cast_choose ℝ hjk]
  by_cases hkj : k = j
  · subst k
    simp only [hilbertInverseTelescoper, show j < j + 1 by omega,
      show ¬j < j by omega, if_pos]
    rw [show j + 1 + i = (i + j) + 1 by omega, Nat.factorial_succ]
    rw [show j + 1 + j = (2 * j) + 1 by omega, Nat.factorial_succ]
    simp only [Nat.add_sub_cancel_left, Nat.sub_self, Nat.factorial_zero,
      Nat.cast_one, one_mul]
    push_cast
    field_simp [hfact]
    norm_num
    try simp only [Nat.cast_ofNat]
    ring_nf
    simp
  · have hjklt : j < k := lt_of_le_of_ne hjk (Ne.symm hkj)
    simp only [hilbertInverseTelescoper, show j < k + 1 by omega,
      show j < k by omega, ↓reduceIte]
    have htopi : Nat.factorial (k + 1 + i) =
        (k + i + 1) * Nat.factorial (k + i) := by
      rw [show k + 1 + i = (k + i) + 1 by omega, Nat.factorial_succ]
    have htopj : Nat.factorial (k + 1 + j) =
        (k + j + 1) * Nat.factorial (k + j) := by
      rw [show k + 1 + j = (k + j) + 1 by omega, Nat.factorial_succ]
    have hsubj : Nat.factorial (k - j) =
        (k - j) * Nat.factorial (k - (j + 1)) := by
      conv_lhs => rw [show k - j = (k - (j + 1)) + 1 by omega,
        Nat.factorial_succ]
      rw [show k - (j + 1) + 1 = k - j by omega]
    have hsubi : Nat.factorial (k - i) =
        (k - i) * Nat.factorial (k - (i + 1)) := by
      conv_lhs => rw [show k - i = (k - (i + 1)) + 1 by omega,
        Nat.factorial_succ]
      rw [show k - (i + 1) + 1 = k - i by omega]
    simp only [show k + 1 - (j + 1) = k - j by omega,
      show k + 1 - (i + 1) = k - i by omega]
    rw [htopi, htopj, hsubj, hsubi]
    push_cast [Nat.cast_sub (by omega : j ≤ k),
      Nat.cast_sub (by omega : j + 1 ≤ k),
      Nat.cast_sub (by omega : i ≤ k),
      Nat.cast_sub (by omega : i + 1 ≤ k)]
    have hkjR : (k : ℝ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show k ≠ j by omega))
    have hkiR : (k : ℝ) - i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show k ≠ i by omega))
    field_simp [hfact, hkjR, hkiR]
    norm_num
    try simp only [Nat.cast_ofNat]
    rw [show i + k = k + i by omega, show j + k = k + j by omega]
    ring

theorem hilbert_inverse_abs_sum
    (i j n : ℕ) (hij : i ≤ j) (hjn : j < n) :
    (∑ k ∈ Finset.Ico j n,
      (2 * k + 1 : ℝ) * hilbertRInvAbsCore i k * hilbertRInvAbsCore j k) =
      hilbertInverseTelescoper i j n := by
  calc
    (∑ k ∈ Finset.Ico j n,
      (2 * k + 1 : ℝ) * hilbertRInvAbsCore i k * hilbertRInvAbsCore j k) =
        ∑ m ∈ Finset.range (n - j),
          (hilbertInverseTelescoper i j (j + m + 1) -
            hilbertInverseTelescoper i j (j + m)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simpa [add_assoc] using
        hilbert_inverse_abs_term_eq_telescoper_sub i j (j + m) hij (by omega)
    _ = hilbertInverseTelescoper i j (j + (n - j)) -
          hilbertInverseTelescoper i j j := by
      exact Finset.sum_range_sub (fun m => hilbertInverseTelescoper i j (j + m)) (n - j)
    _ = hilbertInverseTelescoper i j n := by
      rw [Nat.add_sub_of_le (le_of_lt hjn)]
      simp [hilbertInverseTelescoper]

theorem hilbertInverseTelescoper_eq_formula_abs
    (i j n : ℕ) (hij : i ≤ j) (hjn : j < n) :
    hilbertInverseTelescoper i j n =
      (i + j + 1 : ℝ) *
        Nat.choose (n + i) (n - (j + 1)) *
        Nat.choose (n + j) (n - (i + 1)) *
        (Nat.choose (i + j) i : ℝ) ^ 2 := by
  simp only [hilbertInverseTelescoper, hjn, ↓reduceIte]
  have hc1 := Nat.cast_choose ℝ
    (show n - (j + 1) ≤ n + i by omega)
  have hc2 := Nat.cast_choose ℝ
    (show n - (i + 1) ≤ n + j by omega)
  have hc3 := Nat.cast_choose ℝ (show i ≤ i + j by omega)
  rw [hc1, hc2, hc3]
  rw [show n + i - (n - (j + 1)) = i + j + 1 by omega]
  rw [show n + j - (n - (i + 1)) = i + j + 1 by omega]
  rw [show i + j - i = j by omega]
  rw [show i + j + 1 = (i + j) + 1 by omega, Nat.factorial_succ]
  have hfact : ∀ m : ℕ, (Nat.factorial m : ℝ) ≠ 0 := by
    intro m
    exact_mod_cast Nat.factorial_ne_zero m
  push_cast
  field_simp [hfact]

theorem hilbertRInvCore_mul_eq_sign_abs (i j k : ℕ) :
    hilbertRInvCore i k * hilbertRInvCore j k =
      (-1 : ℝ) ^ (i + j) * hilbertRInvAbsCore i k * hilbertRInvAbsCore j k := by
  unfold hilbertRInvCore hilbertRInvAbsCore
  have hsign : (-1 : ℝ) ^ (i + k) * (-1 : ℝ) ^ (j + k) =
      (-1 : ℝ) ^ (i + j) := by
    have hkk : (-1 : ℝ) ^ (k + k) = 1 := by
      exact Even.neg_one_pow (Even.add_self k)
    rw [← pow_add, show i + k + (j + k) = (i + j) + (k + k) by omega,
      pow_add, hkk, mul_one]
  calc
    (-1 : ℝ) ^ (i + k) * Nat.choose (i + k) i * Nat.choose k i *
        ((-1 : ℝ) ^ (j + k) * Nat.choose (j + k) j * Nat.choose k j) =
      ((-1 : ℝ) ^ (i + k) * (-1 : ℝ) ^ (j + k)) *
        (Nat.choose (i + k) i * Nat.choose k i) *
        (Nat.choose (j + k) j * Nat.choose k j) := by ring
    _ = (-1 : ℝ) ^ (i + j) *
        (Nat.choose (i + k) i * Nat.choose k i) *
        (Nat.choose (j + k) j * Nat.choose k j) := by rw [hsign]

theorem hilbertInverseEntry_comm {n : ℕ} (i j : Fin n) :
    hilbertInverseEntry n i j = hilbertInverseEntry n j i := by
  unfold hilbertInverseEntry
  simp only [add_comm j.val i.val]
  have hc : Nat.choose (i.val + j.val) i.val =
      Nat.choose (i.val + j.val) j.val := Nat.choose_symm_add
  rw [hc]
  ring

theorem factorInverseGram_apply_of_le
    {n : ℕ} (i j : Fin n) (hij : i.val ≤ j.val) :
    (hilbertCholeskyFactorInverse n *
        (hilbertCholeskyFactorInverse n).transpose) i j =
      hilbertInverseEntry n i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    hilbertCholeskyFactorInverse, hilbertInvCholeskyInverseEntry]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => hilbertRInvNat i.val k * hilbertRInvNat j.val k) n]
  have hsubset : Finset.Ico j.val n ⊆ Finset.range n := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  calc
    (∑ k ∈ Finset.range n, hilbertRInvNat i.val k * hilbertRInvNat j.val k) =
        ∑ k ∈ Finset.Ico j.val n,
          hilbertRInvNat i.val k * hilbertRInvNat j.val k := by
      symm
      apply Finset.sum_subset hsubset
      intro k hkn hkIco
      have hkj : ¬j.val ≤ k := by
        intro hjk
        exact hkIco (Finset.mem_Ico.mpr ⟨hjk, Finset.mem_range.mp hkn⟩)
      simp [hilbertRInvNat, hkj]
    _ = ∑ k ∈ Finset.Ico j.val n,
          (-1 : ℝ) ^ (i.val + j.val) *
            ((2 * k + 1 : ℝ) * hilbertRInvAbsCore i.val k *
              hilbertRInvAbsCore j.val k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : j.val ≤ k := (Finset.mem_Ico.mp hk).1
      have hki : i.val ≤ k := le_trans hij hkj
      simp only [hilbertRInvNat, hki, hkj, ↓reduceIte]
      have hsqrt : Real.sqrt (2 * k + 1 : ℕ) ^ 2 =
          ((2 * k + 1 : ℕ) : ℝ) := by
        rw [Real.sq_sqrt]
        positivity
      calc
        (Real.sqrt (2 * k + 1 : ℕ) * hilbertRInvCore i.val k) *
            (Real.sqrt (2 * k + 1 : ℕ) * hilbertRInvCore j.val k) =
          Real.sqrt (2 * k + 1 : ℕ) ^ 2 *
            (hilbertRInvCore i.val k * hilbertRInvCore j.val k) := by ring
        _ = (2 * k + 1 : ℝ) *
            (hilbertRInvCore i.val k * hilbertRInvCore j.val k) := by
          rw [hsqrt]
          push_cast
          ring
        _ = (-1 : ℝ) ^ (i.val + j.val) *
            ((2 * k + 1 : ℝ) * hilbertRInvAbsCore i.val k *
              hilbertRInvAbsCore j.val k) := by
          rw [hilbertRInvCore_mul_eq_sign_abs]
          ring
    _ = (-1 : ℝ) ^ (i.val + j.val) *
          ∑ k ∈ Finset.Ico j.val n,
            ((2 * k + 1 : ℝ) * hilbertRInvAbsCore i.val k *
              hilbertRInvAbsCore j.val k) := by rw [Finset.mul_sum]
    _ = (-1 : ℝ) ^ (i.val + j.val) *
          hilbertInverseTelescoper i.val j.val n := by
      rw [hilbert_inverse_abs_sum i.val j.val n hij j.isLt]
    _ = hilbertInverseEntry n i j := by
      rw [hilbertInverseTelescoper_eq_formula_abs i.val j.val n hij j.isLt]
      unfold hilbertInverseEntry
      ring

/-- The factor-derived inverse has exactly the entries printed in (28.1). -/
theorem factorInverseGram_eq_hilbertInverseFormula (n : ℕ) :
    hilbertCholeskyFactorInverse n *
        (hilbertCholeskyFactorInverse n).transpose =
      hilbertInverseFormula n := by
  have hsymm :
      (hilbertCholeskyFactorInverse n *
          (hilbertCholeskyFactorInverse n).transpose).transpose =
        hilbertCholeskyFactorInverse n *
          (hilbertCholeskyFactorInverse n).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  ext i j
  simp only [hilbertInverseFormula_apply]
  by_cases hij : i.val ≤ j.val
  · exact factorInverseGram_apply_of_le i j hij
  · calc
      (hilbertCholeskyFactorInverse n *
          (hilbertCholeskyFactorInverse n).transpose) i j =
        (hilbertCholeskyFactorInverse n *
          (hilbertCholeskyFactorInverse n).transpose) j i := by
            have happ := congrArg (fun M : RSqMat n => M j i) hsymm
            simpa [Matrix.transpose_apply] using happ
      _ = hilbertInverseEntry n j i :=
        factorInverseGram_apply_of_le j i (by omega)
      _ = hilbertInverseEntry n i j := hilbertInverseEntry_comm j i

/-- Higham equation (28.1), generic closure: the printed matrix is the inverse
of `Hₙ` for every order. -/
theorem hilbert_inverse_formula (n : ℕ) :
    hilbertMatrix n * hilbertInverseFormula n = 1 := by
  rw [← factorInverseGram_eq_hilbertInverseFormula]
  exact hilbertMatrix_mul_factorInverseGram n

theorem hilbert_inverse_formula_left (n : ℕ) :
    hilbertInverseFormula n * hilbertMatrix n = 1 := by
  exact mul_eq_one_comm.mp (hilbert_inverse_formula n)

/-! ### Positive definiteness -/

theorem hilbertCholeskyFactor_mulVec_injective (n : ℕ) :
    Function.Injective (hilbertCholeskyFactor n).mulVec := by
  intro x y hxy
  have h := congrArg (fun v => (hilbertCholeskyFactorInverse n).mulVec v) hxy
  simpa [Matrix.mulVec_mulVec, hilbertCholeskyFactorInverse_mul] using h

theorem hilbertMatrix_quadratic_eq_sum_sq
    (n : ℕ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, x i * hilbertMatrix n i j * x j) =
      ∑ k : Fin n, ((hilbertCholeskyFactor n).mulVec x k) ^ 2 := by
  rw [hilbertMatrix_eq_choleskyGram]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        x i * (hilbertCholeskyFactor n k i * hilbertCholeskyFactor n k j) * x j) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        x i * (hilbertCholeskyFactor n k i * hilbertCholeskyFactor n k j) * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        x i * (hilbertCholeskyFactor n k i * hilbertCholeskyFactor n k j) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ((fun j => hilbertCholeskyFactor n k j) ⬝ᵥ x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The Hilbert quadratic form is strictly positive on every nonzero vector. -/
theorem hilbertMatrix_quadratic_pos
    (n : ℕ) (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n, x i * hilbertMatrix n i j * x j := by
  rw [hilbertMatrix_quadratic_eq_sum_sq]
  have hx0 : x ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hx
    exact hi (congrFun h i)
  have hy0 : (hilbertCholeskyFactor n).mulVec x ≠ 0 := by
    intro h
    exact hx0 ((hilbertCholeskyFactor_mulVec_injective n)
      (h.trans (Matrix.mulVec_zero _).symm))
  have hy : ∃ i, (hilbertCholeskyFactor n).mulVec x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy0 (funext h)
  obtain ⟨i, hi⟩ := hy
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ?_
  exact ⟨i, Finset.mem_univ i,
    (sq_nonneg ((hilbertCholeskyFactor n).mulVec x i)).lt_of_ne
      (Ne.symm (pow_ne_zero 2 hi))⟩

/-- Section 28.1's SPD claim, in the repository's explicit real quadratic-form
surface. -/
theorem hilbertMatrix_isSymPosDef_explicit (n : ℕ) :
    (∀ i j : Fin n, hilbertMatrix n i j = hilbertMatrix n j i) ∧
      ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        0 < ∑ i : Fin n, ∑ j : Fin n, x i * hilbertMatrix n i j * x j := by
  constructor
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j) (hilbertMatrix_transpose n)
    simpa [Matrix.transpose_apply] using h.symm
  · exact hilbertMatrix_quadratic_pos n

/-! ### Pascal positive definiteness -/

/-- The transposed Pascal Cholesky factor acts injectively.  This is derived
from the already proved two-sided inverse of `pascalMatrix`, rather than from
an assumed spectral property. -/
theorem pascalLowerTranspose_mulVec_injective (n : ℕ) :
    Function.Injective ((pascalLower n).transpose).mulVec := by
  intro x y hxy
  have hP : (pascalMatrix n).mulVec x = (pascalMatrix n).mulVec y := by
    rw [pascalMatrix_eq_lower_mul_transpose]
    simpa [Matrix.mulVec_mulVec] using
      congrArg (fun v => (pascalLower n).mulVec v) hxy
  have h := congrArg
    (fun v => ((signedPascal n).transpose * signedPascal n).mulVec v) hP
  simpa [Matrix.mulVec_mulVec, signedGram_mul_pascalMatrix] using h

/-- The Pascal quadratic form is the squared Euclidean norm of the transposed
lower Pascal factor applied to the vector. -/
theorem pascalMatrix_quadratic_eq_sum_sq
    (n : ℕ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, x i * pascalMatrix n i j * x j) =
      ∑ k : Fin n, (((pascalLower n).transpose).mulVec x k) ^ 2 := by
  rw [pascalMatrix_eq_lower_mul_transpose]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        x i * (pascalLower n i k * pascalLower n j k) * x j) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        x i * (pascalLower n i k * pascalLower n j k) * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        x i * (pascalLower n i k * pascalLower n j k) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ((fun j => pascalLower n j k) ⬝ᵥ x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The Pascal quadratic form is strictly positive on every nonzero vector. -/
theorem pascalMatrix_quadratic_pos
    (n : ℕ) (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n, x i * pascalMatrix n i j * x j := by
  rw [pascalMatrix_quadratic_eq_sum_sq]
  have hx0 : x ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hx
    exact hi (congrFun h i)
  have hy0 : ((pascalLower n).transpose).mulVec x ≠ 0 := by
    intro h
    exact hx0 ((pascalLowerTranspose_mulVec_injective n)
      (h.trans (Matrix.mulVec_zero _).symm))
  have hy : ∃ i, ((pascalLower n).transpose).mulVec x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy0 (funext h)
  obtain ⟨i, hi⟩ := hy
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ?_
  exact ⟨i, Finset.mem_univ i,
    (sq_nonneg (((pascalLower n).transpose).mulVec x i)).lt_of_ne
      (Ne.symm (pow_ne_zero 2 hi))⟩

/-- Section 28.4's Pascal SPD claim on the repository's explicit real
quadratic-form surface. -/
theorem pascalMatrix_isSymPosDef_explicit (n : ℕ) :
    (∀ i j : Fin n, pascalMatrix n i j = pascalMatrix n j i) ∧
      ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        0 < ∑ i : Fin n, ∑ j : Fin n,
          x i * pascalMatrix n i j * x j := by
  constructor
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j) (pascalMatrix_transpose n)
    simpa [Matrix.transpose_apply] using h.symm
  · exact pascalMatrix_quadratic_pos n

end NumStability
