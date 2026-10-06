import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# NumStability Analysis TestMatrices Hilbert Exact

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Exact` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
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

end NumStability
