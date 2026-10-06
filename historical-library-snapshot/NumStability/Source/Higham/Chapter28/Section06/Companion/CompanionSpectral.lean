import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Companion.Basic
import NumStability.Analysis.TestMatrices.Companion.CompanionSpectral
import NumStability.Analysis.TestMatrices.Companion.Contracts
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
# Chapter28 Section06 Companion CompanionSpectral

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28CompanionSpectral` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open scoped BigOperators ComplexConjugate

open Matrix Module Polynomial

theorem companionSquaredSingularValues_nonneg
    (m : ℕ) (a : ℕ → ℂ) (i : Fin (m + 2)) :
    0 ≤ companionSquaredSingularValues m a i := by
  exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg
    (companionMatrix (m + 2) a) i

theorem companionExceptionalSquaredSingularValuePlus_isRoot
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValuePlus m a ^ 2 -
        companionSingularAlpha (m + 2) a *
          companionExceptionalSquaredSingularValuePlus m a + ‖a 0‖ ^ 2 = 0 := by
  have hsqrt := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalSquaredSingularValuePlus
  unfold companionExceptionalDiscriminant at hsqrt ⊢
  nlinarith

theorem companionExceptionalSquaredSingularValueMinus_isRoot
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValueMinus m a ^ 2 -
        companionSingularAlpha (m + 2) a *
          companionExceptionalSquaredSingularValueMinus m a + ‖a 0‖ ^ 2 = 0 := by
  have hsqrt := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalSquaredSingularValueMinus
  unfold companionExceptionalDiscriminant at hsqrt ⊢
  nlinarith

theorem companionExceptionalSquaredSingularValueMinus_nonneg
    (m : ℕ) (a : ℕ → ℂ) :
    0 ≤ companionExceptionalSquaredSingularValueMinus m a := by
  have hq : 0 ≤ ‖a 0‖ ^ 2 := sq_nonneg _
  have halpha : 0 ≤ companionSingularAlpha (m + 2) a := by
    unfold companionSingularAlpha
    positivity
  have hr0 :
      0 ≤ Real.sqrt (companionExceptionalDiscriminant m a) :=
    Real.sqrt_nonneg _
  have hr2 := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalDiscriminant at hr0 hr2
  have hrle :
      Real.sqrt
          (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) ≤
        companionSingularAlpha (m + 2) a := by
    have hsquare :
        Real.sqrt
              (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) ^ 2 ≤
          companionSingularAlpha (m + 2) a ^ 2 := by
      rw [hr2]
      nlinarith
    nlinarith [sq_nonneg
      (Real.sqrt
          (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) +
        companionSingularAlpha (m + 2) a)]
  unfold companionExceptionalSquaredSingularValueMinus
  unfold companionExceptionalDiscriminant
  exact div_nonneg (sub_nonneg.mpr hrle) (by norm_num)

theorem companionExceptionalSquaredSingularValueMinus_le_plus
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValueMinus m a ≤
      companionExceptionalSquaredSingularValuePlus m a := by
  have hsqrt :
      0 ≤ Real.sqrt (companionExceptionalDiscriminant m a) :=
    Real.sqrt_nonneg _
  unfold companionExceptionalSquaredSingularValueMinus
    companionExceptionalSquaredSingularValuePlus
  linarith

/-- Exact order-two correction to the false normality characterization on
Higham p. 523. At order two, normality permits a nonzero higher coefficient:
the complete condition is `|a₀|²=1` together with
`conj(a₁) a₀ = a₁`. -/
theorem companion_orderTwo_isStarNormal_iff (a : ℕ → ℂ) :
    IsStarNormal (companionMatrix 2 a) ↔
      star (a 0) * a 0 = 1 ∧ star (a 1) * a 0 = a 1 := by
  rw [isStarNormal_iff]
  change
    (companionMatrix 2 a).conjTranspose * companionMatrix 2 a =
        companionMatrix 2 a * (companionMatrix 2 a).conjTranspose ↔ _
  constructor
  · intro h
    constructor
    · have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
      simpa [companionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply] using h11
    · have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
      simpa [companionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply] using h01
  · rintro ⟨h0, h1⟩
    have h0' : a 0 * star (a 0) = 1 := by simpa [mul_comm] using h0
    have h1star := congrArg star h1
    simp only [star_mul, star_star] at h1star
    ext i j
    fin_cases i <;> fin_cases j
    · simp [companionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
      change star (a 1) * a 1 + 1 =
        a 1 * star (a 1) + a 0 * star (a 0)
      rw [h0']
      ring
    · simpa [companionMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply] using h1
    · simpa [companionMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply] using h1star
    · simpa [companionMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply] using h0

end NumStability

end
