import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Cauchy.Basic
import NumStability.Analysis.TestMatrices.Cauchy.Cauchy
import NumStability.Analysis.TestMatrices.Cauchy.Contracts
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
# Chapter28 Section01 Cauchy Cauchy

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Cauchy` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

open Matrix

theorem sum_cauchyInverseFormula
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    (∑ i : Fin n, ∑ j : Fin n, cauchyInverseFormula n x y i j) =
      ∑ i : Fin n, (x i + y i) := by
  rw [← sum_cauchyInverseOnesEntry h]
  apply Finset.sum_congr rfl
  intro i _
  have hrow := congrFun (cauchyInverseFormula_mulVec_one h) i
  simpa [Matrix.mulVec, dotProduct] using hrow

theorem cauchyLower_mul_cauchyUpper
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyLower n x y * cauchyUpper n x y = cauchyMatrix x y := by
  ext i j
  rw [Matrix.mul_apply]
  calc
    (∑ k, cauchyLower n x y i k * cauchyUpper n x y k j) =
        ∑ k, cauchyChoTerm x y i j k := by
      apply Finset.sum_congr rfl
      intro k _
      exact cauchyLower_mul_cauchyUpper_term h i j k
    _ = cauchyMatrix x y i j := sum_cauchyChoTerm h i j

end NumStability
