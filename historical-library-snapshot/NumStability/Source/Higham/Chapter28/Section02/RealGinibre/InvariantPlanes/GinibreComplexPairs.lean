import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.RealGinibre.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.GinibreRoots

/-!
# Chapter28 Section02 RealGinibre InvariantPlanes GinibreComplexPairs

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreComplexPairs` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory Polynomial

open scoped ComplexConjugate

/-- Number of characteristic roots in the open upper half-plane, counted
with algebraic multiplicity. -/
def complexUpperEigenvalueCount (n : ℕ) (A : GinibreRawMatrix n) : ℕ :=
  ((complexMatrixCharpoly A).roots.filter fun z => 0 < z.im).card

/-- Mapping the complex characteristic polynomial of a real matrix through
complex conjugation leaves the polynomial unchanged. -/
theorem map_complexMatrixCharpoly_conj {n : ℕ} (A : GinibreRawMatrix n) :
    (complexMatrixCharpoly A).map Complex.conjAe.toRingEquiv.toRingHom =
      complexMatrixCharpoly A := by
  rw [complexMatrixCharpoly, Polynomial.map_map]
  congr 1
  ext x
  simp [Complex.conjAe_coe]

/-- The complete complex root multiset of a real characteristic polynomial
is invariant under conjugation.  Since this is a multiset equality, it
retains algebraic multiplicities. -/
theorem roots_complexMatrixCharpoly_map_conj {n : ℕ}
    (A : GinibreRawMatrix n) :
    (complexMatrixCharpoly A).roots.map (starRingEnd ℂ) =
      (complexMatrixCharpoly A).roots := by
  have h := (IsAlgClosed.splits (complexMatrixCharpoly A)).roots_map_of_injective
    Complex.conjAe.toRingEquiv.injective
  rw [show (starRingEnd ℂ) = Complex.conjAe.toRingEquiv.toRingHom by ext; rfl,
    map_complexMatrixCharpoly_conj A] at h
  exact h.symm

/-- Conjugate roots occur with exactly equal algebraic multiplicity. -/
theorem complexMatrixCharpoly_rootMultiplicity_conj
    {n : ℕ} (A : GinibreRawMatrix n) (z : ℂ) :
    (complexMatrixCharpoly A).roots.count ((starRingEnd ℂ) z) =
      (complexMatrixCharpoly A).roots.count z := by
  classical
  have hcount := Multiset.count_map_eq_count'
    (starRingEnd ℂ) (complexMatrixCharpoly A).roots
    Complex.conjAe.toRingEquiv.injective z
  rw [roots_complexMatrixCharpoly_map_conj A] at hcount
  exact hcount

/-- The roots of the complexified characteristic polynomial on the real axis
are exactly the roots of the original real characteristic polynomial. -/
theorem card_filter_im_eq_zero_complexMatrixCharpoly
    {n : ℕ} (A : GinibreRawMatrix n) :
    ((complexMatrixCharpoly A).roots.filter fun z => z.im = 0).card =
      realEigenvalueCount n A := by
  classical
  have hf := Polynomial.filter_roots_map_range_eq_map_roots
    Complex.ofRealHom.injective (Matrix.charpoly (Matrix.of A))
  have hc := congrArg Multiset.card hf
  rw [show (Matrix.charpoly (Matrix.of A)).map Complex.ofRealHom =
      complexMatrixCharpoly A by rfl, Multiset.card_map] at hc
  simpa only [mem_range_complexOfReal_iff] using hc

end NumStability

end
