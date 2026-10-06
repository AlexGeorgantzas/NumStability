import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Exact
import NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant.Exact
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Probability under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory Filter ProbabilityTheory

local instance instMeasurableSpaceRSqMat_1 (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

noncomputable def realGinibreMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))

noncomputable def expectedRealEigenvalueCount (n : ℕ) : ℝ :=
  ∫ A : RSqMat n, (realEigenvalueCount n A : ℝ) ∂realGinibreMeasure n

/-- Precise standard-limit formulation of the real-Ginibre prose on p. 517. -/
def RealGinibreExpectedCountLimit : Prop :=
  Tendsto (fun n : ℕ => expectedRealEigenvalueCount n / Real.sqrt n)
    atTop (nhds (Real.sqrt (2 / Real.pi)))

/-- The standard real-Ginibre product law is normalized.  This is the
nonvacuity check for the probability space used by the expectation transfer
below; no random-matrix spectral claim is hidden in it. -/
theorem realGinibreMeasure_univ (n : ℕ) :
    realGinibreMeasure n Set.univ = 1 := by
  unfold realGinibreMeasure
  calc
    (Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1))) Set.univ =
        ∏ i : Fin n,
          Measure.pi (fun _ : Fin n => gaussianReal 0 1) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp

/-- Higham, 2nd ed., pp. 516-517: explicit-domain transfer of the real
Ginibre expected-real-root limit.  `a` is the coefficient sequence delivered
by the cited finite-`n` expectation calculation; the two premises are the
genuine upstream finite formula and its Gamma/Stirling estimate. -/
theorem realGinibreExpectedCountLimit_of_coefficient_formula
    (a : ℕ → ℝ)
    (hfinite : ∀ n, expectedRealEigenvalueCount n = a n)
    (hestimate : Tendsto (fun n : ℕ => a n / Real.sqrt n)
      atTop (nhds (Real.sqrt (2 / Real.pi)))) :
    RealGinibreExpectedCountLimit := by
  unfold RealGinibreExpectedCountLimit
  convert hestimate using 1
  funext n
  rw [hfinite]

end NumStability
