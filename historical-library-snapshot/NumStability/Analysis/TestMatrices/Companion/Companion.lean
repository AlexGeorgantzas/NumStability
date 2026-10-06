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
# NumStability Analysis TestMatrices Companion Companion

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Companion` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open scoped BigOperators ComplexConjugate

open Matrix Module Polynomial

/-- The source polynomial is monic of exactly the matrix order. -/
theorem companionCharacteristicFormula_monic
    (n : ℕ) (a : ℕ → ℂ) :
    (companionCharacteristicFormula n a).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [companionCharacteristicFormula_coeff]
    simp [ne_of_gt hN, not_lt_of_ge hN.le]
  · rw [companionCharacteristicFormula_coeff]
    simp

theorem companionCharacteristicFormula_natDegree
    (n : ℕ) (a : ℕ → ℂ) :
    (companionCharacteristicFormula n a).natDegree = n := by
  apply le_antisymm
  · exact (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
      rw [companionCharacteristicFormula_coeff]
      simp [ne_of_gt hN, not_lt_of_ge hN.le])
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [companionCharacteristicFormula_coeff]
    simp

/-- The source's `compan(poly(A))`: build a companion matrix from the
nonleading coefficients of a matrix characteristic polynomial. -/
noncomputable def companionOfMatrix
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  companionMatrix n (fun k => -M.charpoly.coeff k)

/-- Similarity preserves matrix rank. -/
theorem Matrix.IsSimilar.rank_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : Matrix.IsSimilar A B) :
    A.rank = B.rank := by
  obtain ⟨P, hP⟩ := h
  have hPdet : IsUnit (P : Matrix n n ℂ).det := by
    have hunit : IsUnit (P : Matrix n n ℂ) := P.isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at hunit
    exact hunit
  have hPidet : IsUnit (↑P⁻¹ : Matrix n n ℂ).det := by
    have hunit : IsUnit (↑P⁻¹ : Matrix n n ℂ) := P⁻¹.isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at hunit
    exact hunit
  calc
    A.rank = ((↑P⁻¹ : Matrix n n ℂ) * A).rank := by
      symm
      exact Matrix.rank_mul_eq_right_of_isUnit_det
        (↑P⁻¹ : Matrix n n ℂ) A hPidet
    _ = ((↑P⁻¹ : Matrix n n ℂ) * A * (↑P : Matrix n n ℂ)).rank := by
      symm
      exact Matrix.rank_mul_eq_left_of_isUnit_det
        (↑P : Matrix n n ℂ) ((↑P⁻¹ : Matrix n n ℂ) * A) hPdet
    _ = B.rank := congrArg Matrix.rank hP

/-- Similarity preserves the scalar-shift ranks used in Higham's
nonderogatoriness characterization. -/
theorem Matrix.IsSimilar.rank_sub_scalar_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : Matrix.IsSimilar A B) (lambda : ℂ) :
    (A - lambda • (1 : Matrix n n ℂ)).rank =
      (B - lambda • (1 : Matrix n n ℂ)).rank := by
  have hs := (Matrix.IsSimilar.add_scalar (-lambda) h).rank_eq
  have hAeq : A - lambda • (1 : Matrix n n ℂ) =
      (-lambda) • (1 : Matrix n n ℂ) + A := by
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  have hBeq : B - lambda • (1 : Matrix n n ℂ) =
      (-lambda) • (1 : Matrix n n ℂ) + B := by
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  rw [hAeq, hBeq]
  exact hs

/-- A concrete order-two counterexample to the source's printed complex
normality characterization: `a₀=a₁=1` gives a real symmetric (hence normal)
companion although the higher coefficient is nonzero. -/
def companionOrderTwoNormalCounterexampleCoefficients : ℕ → ℂ :=
  fun k => if k = 0 ∨ k = 1 then 1 else 0

theorem companionOrderTwoNormalCounterexample_isSelfAdjoint :
    IsSelfAdjoint
      (companionMatrix 2 companionOrderTwoNormalCounterexampleCoefficients) := by
  rw [isSelfAdjoint_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [companionMatrix, companionOrderTwoNormalCounterexampleCoefficients,
      Matrix.conjTranspose_apply]

end NumStability

end
