import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.Ginibre
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreRecurrence

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreRecurrence` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory ProbabilityTheory

open scoped ENNReal BigOperators

/-- Shifting the lower hypergeometric parameter by two multiplies each scalar
series coefficient by an explicit rational factor. -/
theorem ginibreHypergeometricTerm_shift_two (m k : ℕ) (hm : 0 < m) :
    ginibreHypergeometricTerm (m + 2) k =
      ginibreHypergeometricTerm m k *
        ((m : ℝ) * (m + 1) /
          (((m : ℝ) + k) * ((m : ℝ) + k + 1))) := by
  induction k with
  | zero =>
      rw [ginibreHypergeometricTerm_zero,
        ginibreHypergeometricTerm_zero]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  | succ k ih =>
      rw [ginibreHypergeometricTerm_succ,
        ginibreHypergeometricTerm_succ, ih]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hmk : (m : ℝ) + k ≠ 0 := by positivity
      have hmks : (m : ℝ) + k + 1 ≠ 0 := by positivity
      have hmks2 : (m : ℝ) + k + 2 ≠ 0 := by positivity
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
      field_simp
      ring

/-- The certificate whose consecutive difference is the shifted-series
coefficient difference. -/
noncomputable def ginibreHypergeometricTelescopeTerm (m k : ℕ) : ℝ :=
  (((2 : ℝ) * k - 1) / ((m : ℝ) + k)) *
    ginibreHypergeometricTerm m k

/-- Termwise telescoping identity behind the two-step hypergeometric
recurrence. -/
theorem ginibreHypergeometricTerm_shift_two_telescope
    (m k : ℕ) (hm : 0 < m) :
    (((m : ℝ) + 1 / 2) * ((m : ℝ) + 3 / 2) /
        ((m : ℝ) * ((m : ℝ) + 1))) *
          ginibreHypergeometricTerm (m + 2) k -
        ginibreHypergeometricTerm m k =
      ginibreHypergeometricTelescopeTerm m (k + 1) -
        ginibreHypergeometricTelescopeTerm m k := by
  rw [ginibreHypergeometricTerm_shift_two m k hm]
  unfold ginibreHypergeometricTelescopeTerm
  rw [ginibreHypergeometricTerm_succ]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hmk : (m : ℝ) + k ≠ 0 := by positivity
  have hmks : (m : ℝ) + k + 1 ≠ 0 := by positivity
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
  field_simp
  ring

/-- Every real `1 × 1` matrix has exactly one algebraic real eigenvalue. -/
theorem realEigenvalueCount_one (A : RSqMat 1) :
    realEigenvalueCount 1 A = 1 := by
  unfold realEigenvalueCount
  rw [show Matrix.charpoly A = Polynomial.X - Polynomial.C (A 0 0) by
    rw [Matrix.charpoly]
    simp]
  rw [Polynomial.roots_X_sub_C]
  simp

end NumStability
