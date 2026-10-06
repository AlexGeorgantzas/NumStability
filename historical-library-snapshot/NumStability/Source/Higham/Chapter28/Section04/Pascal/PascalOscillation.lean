import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.TestMatrices.Pascal.PascalOscillation
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Chapter28 Section04 Pascal PascalOscillation

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28PascalOscillation` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Set

@[simp]
theorem pascalSortedEigenEquiv_apply (n : ℕ) (i : Fin n) :
    pascalSortedEigenEquiv n i = pascalSortedEigenIndex n i := rfl

/-- For an entrywise-positive finite matrix, an eigenvector belonging to the
eigenvalue of a strictly positive eigenvector is unique up to scale.  This is
the elementary ratio argument underlying the simple Perron root. -/
theorem positiveMatrix_eigenvector_unique_up_to_smul
    {n : ℕ} (hn : 0 < n) (A : RSqMat n) (rho : ℝ)
    (p : RVec n) (hp : ∀ i, 0 < p i)
    (hA : ∀ i j, 0 < A i j)
    (heigp : Matrix.mulVec A p = rho • p)
    (x : RVec n) (heigx : Matrix.mulVec A x = rho • x) :
    ∃ t : ℝ, x = t • p := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let ratio : Fin n → ℝ := fun i => x i / p i
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max ratio
  let t := ratio i₀
  let z : RVec n := t • p - x
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    change 0 ≤ t * p i - x i
    rw [sub_nonneg]
    apply (div_le_iff₀ (hp i)).mp
    exact hi₀ i
  have hz_i₀ : z i₀ = 0 := by
    change t * p i₀ - x i₀ = 0
    dsimp [t, ratio]
    rw [div_mul_cancel₀ _ (hp i₀).ne']
    ring
  have heigz : Matrix.mulVec A z = rho • z := by
    rw [show z = t • p - x by rfl, Matrix.mulVec_sub,
      Matrix.mulVec_smul, heigp, heigx]
    module
  have hz_zero : z = 0 := by
    by_contra hz
    have hex : ∃ j, z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    obtain ⟨j, hj⟩ := hex
    have hzj : 0 < z j := lt_of_le_of_ne (hz_nonneg j) (Ne.symm hj)
    have hAz : 0 < Matrix.mulVec A z i₀ := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_pos'
      · intro q _
        exact mul_nonneg (le_of_lt (hA i₀ q)) (hz_nonneg q)
      · exact ⟨j, Finset.mem_univ j, mul_pos (hA i₀ j) hzj⟩
    have heigz_i := congrFun heigz i₀
    simp only [Pi.smul_apply, smul_eq_mul, hz_i₀, mul_zero] at heigz_i
    exact (ne_of_gt hAz) heigz_i
  refine ⟨t, ?_⟩
  have := sub_eq_zero.mp hz_zero
  exact this.symm

end NumStability
