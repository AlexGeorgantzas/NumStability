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
import NumStability.Analysis.TestMatrices.RealGinibre.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedRank

/-!
# Chapter28 Section02 RealGinibre SignedIncidence GinibreSignedRankTransfer

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRankTransfer` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory Set

open scoped BigOperators

/-- A finite signed prefix indexed by `Fin M` is the alternating count of the
prefix.  The weak bound is convenient when the ambient finite type has no
unused endpoint. -/
theorem sum_fin_ite_lt_eq_ginibreAlternatingCount
    (M r : ℕ) (hr : r ≤ M) :
    (∑ k : Fin M, if k.val < r then (-1 : ℝ) ^ k.val else 0) =
      ginibreAlternatingCount r := by
  change (∑ k : Fin M,
    (fun j : ℕ => if j < r then (-1 : ℝ) ^ j else 0) k) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < r then (-1 : ℝ) ^ j else 0) M]
  unfold ginibreAlternatingCount
  calc
    (∑ j ∈ Finset.range M, if j < r then (-1 : ℝ) ^ j else 0) =
        ∑ j ∈ Finset.range r,
          if j < r then (-1 : ℝ) ^ j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hr)
      intro k hkM hkr
      simp only [Finset.mem_range] at hkM hkr
      simp [hkr]
    _ = ∑ j ∈ Finset.range r, (-1 : ℝ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      simp [hj]

/-- The ordered-pair alternating count is the signed sum of the one-root
alternating prefixes at the second root. -/
theorem ginibreAlternatingPairCount_eq_sum_rankPrefixes (r : ℕ) :
    ginibreAlternatingPairCount r =
      ∑ j ∈ Finset.range r,
        (-1 : ℝ) ^ j * ginibreAlternatingCount j := by
  unfold ginibreAlternatingPairCount ginibreAlternatingCount
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

/-- Finite-sheet version of the preceding pair-prefix identity. -/
theorem sum_fin_ite_lt_eq_ginibreAlternatingPairCount
    (M r : ℕ) (hr : r ≤ M) :
    (∑ k : Fin M, if k.val < r then
        (-1 : ℝ) ^ k.val * ginibreAlternatingCount k.val else 0) =
      ginibreAlternatingPairCount r := by
  change (∑ k : Fin M,
    (fun j : ℕ => if j < r then
      (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0) k) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < r then
      (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0) M]
  rw [ginibreAlternatingPairCount_eq_sum_rankPrefixes]
  calc
    (∑ j ∈ Finset.range M,
        if j < r then
          (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0) =
        ∑ j ∈ Finset.range r,
          if j < r then
            (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hr)
      intro k hkM hkr
      simp only [Finset.mem_range] at hkM hkr
      simp [hkr]
    _ = ∑ j ∈ Finset.range r,
        (-1 : ℝ) ^ j * ginibreAlternatingCount j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      simp [hj]

/-- The rank of the marked root in the full incidence matrix is already the
number of real roots of the deflated block strictly below that mark.  No
regularity hypothesis is needed. -/
theorem ginibreIncidenceRootRank_eq_deflatedBelowCount
    {m : ℕ} (q : GinibreIncidenceCoordinates m) :
    ginibreIncidenceRootRank q =
      realEigenvalueBelowCount
        (ginibreIncidenceDeflatedBlock q, ginibreIncidenceEigenvalue q) := by
  let D : RSqMat m := ginibreIncidenceDeflatedBlock q
  let l : ℝ := ginibreIncidenceEigenvalue q
  let P : Polynomial ℝ := D.charpoly
  have hPne : P ≠ 0 := (Matrix.charpoly_monic D).ne_zero
  have hlinear :
      (Polynomial.X - Polynomial.C l : Polynomial ℝ) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero l
  have hfullRoots :
      (ginibreIncidenceMatrix q).charpoly.roots = P.roots + {l} := by
    rw [ginibreIncidenceMatrix_charpoly_factor]
    change (D.charpoly * (Polynomial.X - Polynomial.C l)).roots = _
    rw [Polynomial.roots_mul (mul_ne_zero hPne hlinear),
      Polynomial.roots_X_sub_C]
  unfold ginibreIncidenceRootRank realEigenvalueBelowCount
  rw [ginibreCoordinatesFinMatrix_charpoly,
    ginibreCoordinatesMatrix_chart, hfullRoots,
    Multiset.filter_add, Multiset.card_add,
    Multiset.filter_singleton, if_neg (lt_irrefl l)]
  rfl

/-- The part of the `k`th regular incidence sheet whose marked root lies
strictly below an external threshold. -/
def ginibreIncidenceRankPieceBelow (m : ℕ) (k : Fin (m + 2)) (x : ℝ) :
    Set (GinibreIncidenceCoordinates m) :=
  ginibreIncidenceRankPiece m k ∩
    {q | ginibreIncidenceEigenvalue q < x}

end NumStability

end
