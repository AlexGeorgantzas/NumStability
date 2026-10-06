import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedRank

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreSignedExpectation

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedExpectation` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

/-- Alternating one-root observable on an `n × n` matrix. -/
def ginibreAlternatingEigenvalueCount (n : ℕ) (A : RSqMat n) : ℝ :=
  ginibreAlternatingCount (realEigenvalueCount n A)

/-- Alternating ordered-pair observable on an `n × n` matrix. -/
def ginibreAlternatingPairEigenvalueCount (n : ℕ) (A : RSqMat n) : ℝ :=
  ginibreAlternatingPairCount (realEigenvalueCount n A)

/-- A crude sharp-enough bound for the alternating one-root sum. -/
theorem abs_ginibreAlternatingCount_le (r : ℕ) :
    |ginibreAlternatingCount r| ≤ (r : ℝ) := by
  unfold ginibreAlternatingCount
  calc
    |∑ j ∈ Finset.range r, (-1 : ℝ) ^ j| ≤
        ∑ j ∈ Finset.range r, |(-1 : ℝ) ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (r : ℝ) := by simp

/-- The alternating ordered-pair sum is bounded by the square of the number
of roots. -/
theorem abs_ginibreAlternatingPairCount_le_sq (r : ℕ) :
    |ginibreAlternatingPairCount r| ≤ (r : ℝ) ^ 2 := by
  unfold ginibreAlternatingPairCount
  calc
    |∑ j ∈ Finset.range r,
        ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)| ≤
        ∑ j ∈ Finset.range r,
          |∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range r, (r : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        |∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)| ≤
            ∑ i ∈ Finset.range j, |(-1 : ℝ) ^ (i + j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = (j : ℝ) := by simp
        _ ≤ (r : ℝ) := by
          exact_mod_cast (Nat.le_of_lt (Finset.mem_range.1 hj))
    _ = (r : ℝ) ^ 2 := by simp [pow_two]

theorem ginibreAlternatingCount_add_two (r : ℕ) :
    ginibreAlternatingCount (r + 2) = ginibreAlternatingCount r := by
  unfold ginibreAlternatingCount
  rw [show r + 2 = (r + 1) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]
  ring

theorem ginibreAlternatingCount_add_two_mul (r c : ℕ) :
    ginibreAlternatingCount (r + 2 * c) = ginibreAlternatingCount r := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.mul_succ]
      rw [show r + (2 * c + 2) = (r + 2 * c) + 2 by omega,
        ginibreAlternatingCount_add_two, ih]

end NumStability

end
