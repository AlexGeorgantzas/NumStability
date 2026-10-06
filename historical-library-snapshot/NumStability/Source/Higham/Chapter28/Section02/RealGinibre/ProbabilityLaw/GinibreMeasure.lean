import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter28 Section02 RealGinibre ProbabilityLaw GinibreMeasure

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

open MeasureTheory

open scoped ENNReal

/-- A finite product of integrable nonnegative real densities is the density
of the corresponding finite product measure. -/
theorem MeasureTheory.Measure.pi_withDensity_ofReal
    {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, α i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity
        (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  refine Measure.pi_eq fun s hs => ?_
  have hrect : MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.univ_pi fun i => hs i
  rw [withDensity_apply _ hrect]
  have hprod_nonneg : ∀ x : ∀ i, α i, 0 ≤ ∏ i, f i (x i) := by
    intro x
    exact Finset.prod_nonneg fun i _ => hf0 i (x i)
  have hprod_int : Integrable (fun x : ∀ i, α i => ∏ i, f i (x i))
      (Measure.pi μ) :=
    Integrable.fintype_prod_dep hf
  rw [← ofReal_integral_eq_lintegral_ofReal
    hprod_int.restrict (ae_of_all _ hprod_nonneg)]
  rw [Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod]
  simp_rw [withDensity_apply _ (hs _)]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (hf0 i))]
  congr 1
  funext i
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hf i).restrict (ae_of_all _ (hf0 i))]

namespace NumStability

open ProbabilityTheory

/-- The ordinary real-valued standard-Gaussian joint density of an `n × n`
matrix with respect to `realGinibreLebesgueMeasure`. -/
noncomputable def realGinibreDensityReal (n : ℕ) (A : RSqMat n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, gaussianPDFReal 0 1 (A i j)

theorem realGinibreDensityReal_pos (n : ℕ) (A : RSqMat n) :
    0 < realGinibreDensityReal n A := by
  unfold realGinibreDensityReal
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact gaussianPDFReal_pos 0 1 (A i j) (by norm_num)

end NumStability

end
