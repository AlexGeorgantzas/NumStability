import NumStability.Analysis.TestMatrices.RandomSVD.StewartMeasurability
import NumStability.Source.Higham.Chapter28.Section03.Theorem01.StewartHaar.Stewart

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Stewart under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

private local instance instMeasurableSpaceRSqMat_relocated_HaarConclusion (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- The exact group-level, normalized Haar endpoint of Theorem 28.1.

The downstream theorem `stewartTheorem28_1HaarConclusion` proves this
proposition by a Gaussian/Householder induction and Haar-fiber uniqueness. -/
def StewartTheorem28_1HaarConclusion (n : ℕ) : Prop :=
  (stewartOrthogonalGroupLaw n).IsHaarMeasure ∧
    stewartOrthogonalGroupLaw n Set.univ = 1

/-- With normalization already built into the concrete push-forward, the
endpoint is equivalent to its Haar-invariance conjunct. -/
theorem stewartTheorem28_1HaarConclusion_iff_isHaarMeasure (n : ℕ) :
    StewartTheorem28_1HaarConclusion n ↔
      (stewartOrthogonalGroupLaw n).IsHaarMeasure := by
  simp [StewartTheorem28_1HaarConclusion, stewartOrthogonalGroupLaw_univ]

end NumStability
