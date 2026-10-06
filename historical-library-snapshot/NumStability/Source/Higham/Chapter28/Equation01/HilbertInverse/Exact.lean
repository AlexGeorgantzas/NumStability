import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Basic
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Basic
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact
import NumStability.Source.Higham.Chapter28.Equation04.HilbertCholeskyInverse.Basic

/-!
# Chapter28 Equation01 HilbertInverse Exact

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Exact` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

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

end NumStability
