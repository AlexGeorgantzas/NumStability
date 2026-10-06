import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Basic
import NumStability.Source.Higham.Chapter28.Equation04.HilbertCholeskyInverse.Basic

/-!
# Chapter28 Equation03 HilbertCholeskyFactor Exact

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Exact` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

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

theorem hilbertCholeskyFactor_mulVec_injective (n : ℕ) :
    Function.Injective (hilbertCholeskyFactor n).mulVec := by
  intro x y hxy
  have h := congrArg (fun v => (hilbertCholeskyFactorInverse n).mulVec v) hxy
  simpa [Matrix.mulVec_mulVec, hilbertCholeskyFactorInverse_mul] using h

end NumStability
