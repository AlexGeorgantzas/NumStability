import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Basic

/-!
# Chapter28 Equation04 HilbertCholeskyInverse Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.1, p. 513, equation (28.4): the inverse of the
upper Cholesky-factor candidate, in zero-based indices. -/
noncomputable def hilbertInvCholeskyInverseEntry (n : ℕ) (i j : Fin n) : ℝ :=
  hilbertRInvNat i.val j.val

/-- Matrix form of (28.4). -/
noncomputable def hilbertCholeskyFactorInverse (n : ℕ) : RSqMat n :=
  fun i j => hilbertInvCholeskyInverseEntry n i j

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

end NumStability
