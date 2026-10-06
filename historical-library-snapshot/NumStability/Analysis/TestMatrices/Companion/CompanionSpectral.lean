import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Companion.Basic
import NumStability.Analysis.TestMatrices.Companion.Contracts

/-!
# NumStability Analysis TestMatrices Companion CompanionSpectral

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

/-- The canonical squared singular values of an order-at-least-two companion:
the Hermitian eigenvalues of `CᴴC`. -/
noncomputable def companionSquaredSingularValues
    (m : ℕ) (a : ℕ → ℂ) : Fin (m + 2) → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self
    (companionMatrix (m + 2) a)).eigenvalues

noncomputable def companionExceptionalDiscriminant
    (m : ℕ) (a : ℕ → ℂ) : ℝ :=
  companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2

noncomputable def companionExceptionalSquaredSingularValuePlus
    (m : ℕ) (a : ℕ → ℂ) : ℝ :=
  (companionSingularAlpha (m + 2) a +
    Real.sqrt (companionExceptionalDiscriminant m a)) / 2

noncomputable def companionExceptionalSquaredSingularValueMinus
    (m : ℕ) (a : ℕ → ℂ) : ℝ :=
  (companionSingularAlpha (m + 2) a -
    Real.sqrt (companionExceptionalDiscriminant m a)) / 2

theorem companionExceptionalDiscriminant_nonneg
    (m : ℕ) (a : ℕ → ℂ) :
    0 ≤ companionExceptionalDiscriminant m a := by
  have hmem : 0 ∈ Finset.range (m + 2) := by simp
  have hsum : ‖a 0‖ ^ 2 ≤
      ∑ k ∈ Finset.range (m + 2), ‖a k‖ ^ 2 := by
    exact Finset.single_le_sum (fun k hk => sq_nonneg ‖a k‖) hmem
  have halpha : 1 + ‖a 0‖ ^ 2 ≤ companionSingularAlpha (m + 2) a := by
    unfold companionSingularAlpha
    linarith
  have hq : 0 ≤ ‖a 0‖ ^ 2 := sq_nonneg _
  unfold companionExceptionalDiscriminant
  nlinarith [sq_nonneg (‖a 0‖ ^ 2 - 1)]

theorem companionExceptionalSquaredSingularValues_sum
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValuePlus m a +
        companionExceptionalSquaredSingularValueMinus m a =
      companionSingularAlpha (m + 2) a := by
  unfold companionExceptionalSquaredSingularValuePlus
    companionExceptionalSquaredSingularValueMinus
  ring

theorem companionExceptionalSquaredSingularValues_mul
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValuePlus m a *
        companionExceptionalSquaredSingularValueMinus m a = ‖a 0‖ ^ 2 := by
  have hsqrt := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalSquaredSingularValuePlus
    companionExceptionalSquaredSingularValueMinus
  unfold companionExceptionalDiscriminant at hsqrt ⊢
  nlinarith

/-- The exceptional quadratic is exactly the product of Higham's two
displayed linear factors. -/
theorem companionExceptionalQuadratic_eq_mul
    (m : ℕ) (a : ℕ → ℂ) :
    X ^ 2 - C (companionSingularAlpha (m + 2) a : ℂ) * X +
        C ((‖a 0‖ ^ 2 : ℝ) : ℂ) =
      (X - C (companionExceptionalSquaredSingularValuePlus m a : ℂ)) *
        (X - C (companionExceptionalSquaredSingularValueMinus m a : ℂ)) := by
  have hsum :
      (companionExceptionalSquaredSingularValuePlus m a : ℂ) +
          companionExceptionalSquaredSingularValueMinus m a =
        (companionSingularAlpha (m + 2) a : ℂ) := by
    exact_mod_cast companionExceptionalSquaredSingularValues_sum m a
  have hmul :
      (companionExceptionalSquaredSingularValuePlus m a : ℂ) *
          companionExceptionalSquaredSingularValueMinus m a =
        ((‖a 0‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast companionExceptionalSquaredSingularValues_mul m a
  rw [← hsum, ← hmul]
  rw [Polynomial.C_add, Polynomial.C_mul]
  ring

/-- Singular values themselves, obtained as the nonnegative square roots of
the canonical Gram eigenvalues. -/
noncomputable def companionSingularValues
    (m : ℕ) (a : ℕ → ℂ) (i : Fin (m + 2)) : ℝ :=
  Real.sqrt (companionSquaredSingularValues m a i)

end NumStability

end
