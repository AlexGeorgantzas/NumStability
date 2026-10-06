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
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedRankTransfer

/-!
# Chapter28 Section02 RealGinibre Incidence GinibreTruncatedIncidence

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreTruncatedIncidence` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory Set Filter

open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Frobenius

/-- Truncated rank sheets partition the regular incidence set below the
external threshold. -/
theorem iUnion_ginibreIncidenceRankPieceBelow (m : ℕ) (x : ℝ) :
    (⋃ k : Fin (m + 2), ginibreIncidenceRankPieceBelow m k x) =
      ginibreIncidenceRegularSet m ∩
        {q | ginibreIncidenceEigenvalue q < x} := by
  ext q
  constructor
  · intro hq
    rcases Set.mem_iUnion.1 hq with ⟨k, hk⟩
    exact ⟨hk.1.1, hk.2⟩
  · rintro ⟨hreg, hlt⟩
    rw [← iUnion_ginibreIncidenceRankPiece] at hreg
    rcases Set.mem_iUnion.1 hreg with ⟨k, hk⟩
    exact Set.mem_iUnion.2 ⟨k, ⟨hk, hlt⟩⟩

/-- Truncated rank sheets remain pairwise disjoint. -/
theorem pairwiseDisjoint_ginibreIncidenceRankPieceBelow (m : ℕ) (x : ℝ) :
    Pairwise (fun i j : Fin (m + 2) =>
      Disjoint (ginibreIncidenceRankPieceBelow m i x)
        (ginibreIncidenceRankPieceBelow m j x)) := by
  intro i j hij
  exact (pairwiseDisjoint_ginibreIncidenceRankPiece m hij).mono
    inter_subset_left inter_subset_left

end NumStability

end
