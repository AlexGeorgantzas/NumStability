import NumStability.Algorithms.LinearSystems.Triangular.ComparisonBounds
import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Exact
import NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant.Exact
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.ProductLaw

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Probability under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory Filter ProbabilityTheory

private local instance instMeasurableSpaceRSqMat_1_relocated_NormalizedOrthogonalMatrixLaw (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- An ambient-matrix compatibility predicate for a normalized orthogonally
supported, left-invariant law.  This is useful as a transfer surface, but is
not Mathlib's group-level `Measure.IsHaarMeasure` endpoint and does not by
itself prove Stewart's Theorem 28.1.  The exact source push-forward and exact
group-level endpoint are `stewartOrthogonalGroupLaw` and
`StewartTheorem28_1HaarConclusion`. -/
def IsNormalizedOrthogonalHaarLaw (n : ℕ) (mu : Measure (RSqMat n)) : Prop :=
  mu Set.univ = 1 ∧
    mu {Q | IsOrthogonal n Q} = 1 ∧
    ∀ (U : RSqMat n), IsOrthogonal n U →
      ∀ s : Set (RSqMat n), MeasurableSet s →
        mu ((fun Q => U * Q) ⁻¹' s) = mu s

/-- Constructor for the ambient compatibility predicate from its three
fields.  This is a packaging lemma only: callers must still produce
normalization, orthogonal support, and left invariance, and the theorem does
not identify Stewart's Gaussian push-forward with group Haar measure. -/
theorem stewartLaw_isNormalizedOrthogonalHaarLaw
    {n : ℕ} (mu : Measure (RSqMat n))
    (hmass : mu Set.univ = 1)
    (hsupport : mu {Q | IsOrthogonal n Q} = 1)
    (hinvariant : ∀ (U : RSqMat n), IsOrthogonal n U →
      ∀ s : Set (RSqMat n), MeasurableSet s →
        mu ((fun Q => U * Q) ⁻¹' s) = mu s) :
    IsNormalizedOrthogonalHaarLaw n mu :=
  ⟨hmass, hsupport, hinvariant⟩

/-- The ambient compatibility predicate is inhabited in dimension zero: the
matrix space is a singleton, so the Dirac law at the identity has all three
fields.  This is not a nonvacuity witness for Stewart's positive-dimensional
Gaussian producer or its Haar conclusion. -/
theorem diracIdentity_isNormalizedOrthogonalHaarLaw_zero :
    IsNormalizedOrthogonalHaarLaw 0
      (Measure.dirac (1 : RSqMat 0)) := by
  refine ⟨by simp, ?_, ?_⟩
  · have horth : ∀ Q : RSqMat 0, IsOrthogonal 0 Q := by
      intro Q
      rw [Subsingleton.elim Q (1 : RSqMat 0)]
      exact IsOrthogonal.id 0
    have hset : {Q : RSqMat 0 | IsOrthogonal 0 Q} = Set.univ := by
      ext Q
      simp [horth Q]
    rw [hset]
    simp
  · intro U hU s hs
    have hpre : (fun Q : RSqMat 0 => U * Q) ⁻¹' s = s := by
      ext Q
      have hmul : U * Q = Q := Subsingleton.elim _ _
      change U * Q ∈ s ↔ Q ∈ s
      rw [hmul]
    rw [hpre]

end NumStability
