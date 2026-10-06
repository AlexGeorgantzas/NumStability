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
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreAtlas

/-!
# Chapter28 Section02 RealGinibre RootMeasurability GinibreMultiplicity

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreMultiplicity` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory Set

theorem ginibre_normalized_eigenpair
    {n : ℕ} (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (v : Fin n ⊕ Unit → ℝ) (l : ℝ)
    (heig : A.mulVec v = l • v) (hlast : v (Sum.inr ()) ≠ 0) :
    let y : Fin n → ℝ := fun i => v (Sum.inl i) / v (Sum.inr ())
    A.mulVec (ginibreAffineEigenvector y) =
      l • ginibreAffineEigenvector y := by
  dsimp only
  let c := v (Sum.inr ())
  have hc : c ≠ 0 := hlast
  have haff : ginibreAffineEigenvector (fun i => v (Sum.inl i) / c) =
      c⁻¹ • v := by
    funext i
    rcases i with i | i
    · simp [ginibreAffineEigenvector, div_eq_inv_mul]
    · rcases i with ⟨⟩
      simp [ginibreAffineEigenvector, c, hc]
  rw [haff, Matrix.mulVec_smul, heig]
  ext i
  simp [Pi.smul_apply]
  ring

theorem exists_regular_incidence_preimage_of_root
    {n : ℕ} (p : GinibreIncidenceCoordinates n) (l : ℝ)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet n)
    (hcritical : p ∉
      ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ)
    (hroot : (ginibreCoordinatesMatrix p).charpoly.IsRoot l) :
    ∃ q : GinibreIncidenceCoordinates n,
      q ∈ ginibreIncidenceRegularSet n ∧
      ginibreIncidenceChart q = p ∧
      ginibreIncidenceEigenvalue q = l := by
  have hhas : Module.End.HasEigenvalue
      (Matrix.toLin' (ginibreCoordinatesMatrix p)) l := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨v, hv⟩ := hhas.exists_hasEigenvector
  have hv_ne : v ≠ 0 := hv.2
  have heig : (ginibreCoordinatesMatrix p).mulVec v = l • v := by
    simpa [Matrix.toLin'_apply] using hv.apply_eq_smul
  have hlast : v (Sum.inr ()) ≠ 0 := by
    intro hz
    apply hboundary
    exact ⟨v, l, hv_ne, heig, hz⟩
  let y : Fin n → ℝ := fun i => v (Sum.inl i) / v (Sum.inr ())
  let q : GinibreIncidenceCoordinates n := (p.1, y)
  have heig' : (ginibreCoordinatesMatrix p).mulVec
      (ginibreAffineEigenvector y) = l • ginibreAffineEigenvector y :=
    ginibre_normalized_eigenpair (ginibreCoordinatesMatrix p) v l heig hlast
  have hlam : ginibreIncidenceEigenvalue q = l :=
    ginibreIncidenceEigenvalue_eq_of_affine_eigenpair p y l heig'
  have hchart : ginibreIncidenceChart q = p := by
    apply (ginibreIncidenceChart_fiber_iff_affine_eigenpair p y).2
    rw [hlam]
    exact heig'
  have hreg : q ∈ ginibreIncidenceRegularSet n := by
    by_contra hq
    apply hcritical
    exact ⟨q, hq, hchart⟩
  exact ⟨q, hreg, hchart, hlam⟩

/-- Number of regular affine-chart sheets above a matrix coordinate point,
after splitting the chart by real-root rank. -/
noncomputable def ginibreRegularFiberMultiplicity (n : ℕ)
    (p : GinibreIncidenceCoordinates n) : ℕ := by
  classical
  exact ∑ k : Fin (n + 2),
    if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k then 1 else 0

end NumStability

end
