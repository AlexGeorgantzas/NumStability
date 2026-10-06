import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Exact
import NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant.Exact
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.ProductLaw

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Probability under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory Filter ProbabilityTheory

private local instance instMeasurableSpaceRSqMat_1_relocated_PerronAlmostSure (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

noncomputable def uniformUnitIntervalMatrixMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))

/-- Precise almost-sure formulation of the iid-uniform Perron prose on p. 517. -/
def UniformPositivePerronAlmostSure : Prop :=
  ∀ n : ℕ, 0 < n →
    uniformUnitIntervalMatrixMeasure n
      (strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n) = 1

/-- The standard iid restricted-volume matrix law is normalized. -/
theorem uniformUnitIntervalMatrixMeasure_univ (n : ℕ) :
    uniformUnitIntervalMatrixMeasure n Set.univ = 1 := by
  unfold uniformUnitIntervalMatrixMeasure
  calc
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n =>
        volume.restrict (Set.Icc (0 : ℝ) 1)))) Set.univ =
        ∏ i : Fin n, Measure.pi (fun _ : Fin n =>
          volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp [MeasureTheory.Measure.pi_univ]

/-- Every entry is strictly positive almost surely under the actual iid
uniform-`[0,1]` product law.  The only excluded boundary is the zero endpoint,
whose one-dimensional restricted-volume measure is zero. -/
theorem uniformUnitIntervalMatrixMeasure_strictlyPositive (n : ℕ) :
    uniformUnitIntervalMatrixMeasure n (strictlyPositiveMatrixSet n) = 1 := by
  have hset : strictlyPositiveMatrixSet n =
      Set.pi Set.univ (fun _ : Fin n ↦
        Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ))) := by
    ext A
    constructor
    · intro h i _ j _
      exact h i j
    · intro h i j
      exact h i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]
  unfold uniformUnitIntervalMatrixMeasure
  have hcoord :
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ioi 0) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioi]
    have hinter : Set.Ioi (0 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc 0 1 := by
      ext x
      constructor
      · rintro ⟨hx, -, hx1⟩
        exact ⟨hx, hx1⟩
      · rintro ⟨hx, hx1⟩
        exact ⟨hx, hx.le, hx1⟩
    rw [hinter, Real.volume_Ioc]
    norm_num
    rfl
  calc
    (Measure.pi (fun _ : Fin n ↦
        Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1))))
        (Set.pi Set.univ (fun _ : Fin n ↦
          Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)))) =
      ∏ _ : Fin n,
        Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1))
          (Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ))) := by
            exact Measure.pi_pi _ _
    _ = ∏ _ : Fin n, ∏ _ : Fin n,
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ioi 0) := by
          congr 1
          funext i
          exact Measure.pi_pi _ _
    _ = 1 := by simp [hcoord]

/-- Higham, 2nd ed., p. 517: explicit-domain transfer from the two missing
foundations, namely boundary-nullness of the product law and the deterministic
Perron theorem for entrywise-positive matrices.  Neither premise restates the
almost-sure intersection conclusion. -/
theorem uniformPositivePerronAlmostSure_of_boundary_null_of_perron
    (hpositive : ∀ n : ℕ, 0 < n →
      uniformUnitIntervalMatrixMeasure n (strictlyPositiveMatrixSet n) = 1)
    (hperron : ∀ {n : ℕ} (A : RSqMat n),
      A ∈ strictlyPositiveMatrixSet n → HasPositiveDominantEigenvalue A) :
    UniformPositivePerronAlmostSure := by
  intro n hn
  have hset : strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n =
      strictlyPositiveMatrixSet n := by
    ext A
    constructor
    · exact fun h => h.1
    · intro hA
      exact ⟨hA, hperron A hA⟩
  rw [hset, hpositive n hn]

/-- Higham, 2nd ed., p. 517: an iid uniform-`[0,1]` matrix is entrywise
positive and hence has a positive dominant Perron root almost surely in every
positive dimension. -/
theorem uniformPositivePerronAlmostSure :
    UniformPositivePerronAlmostSure := by
  intro n hn
  have hset : strictlyPositiveMatrixSet n ∩ positiveDominantEigenvalueSet n =
      strictlyPositiveMatrixSet n := by
    ext A
    constructor
    · exact fun h => h.1
    · intro hA
      exact ⟨hA, hasPositiveDominantEigenvalue_of_strictlyPositive hn A hA⟩
  rw [hset, uniformUnitIntervalMatrixMeasure_strictlyPositive]

end NumStability
