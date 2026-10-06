import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Haar.HomogeneousSpaceUniqueness
import NumStability.Analysis.TestMatrices.Gaussian.GaussianOrthogonal
import NumStability.Analysis.TestMatrices.RandomSVD.Stewart

/-!
# NumStability Analysis TestMatrices RandomSVD StewartHaar

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28StewartHaar` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace

/-- Coordinate casts identifying the tail at old stage `j+1` with the tail
at new stage `j`. -/
noncomputable def stewartTailCoordinateCastEquiv (d : ℕ) (j : Fin d) :
    (Fin (d + 1 - (j.val + 1)) → ℝ) ≃ᵐ
      (Fin (d - j.val) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin (d - j.val) => ℝ)
    (Equiv.cast (congrArg Fin (by omega :
      d + 1 - (j.val + 1) = d - j.val)))

/-- The collection of all noninitial tails is measurably equivalent to the
dimension-`d` Stewart input space. -/
noncomputable def stewartTailCastEquiv (d : ℕ) :
    ((j : Fin d) → Fin (d + 1 - (j.val + 1)) → ℝ) ≃ᵐ
      StewartGaussianInputs d :=
  MeasurableEquiv.piCongrRight (fun j => stewartTailCoordinateCastEquiv d j)

/-- Split a dimension-`d+1` Stewart input into its first Gaussian vector and
the remaining dimension-`d` Stewart input. -/
noncomputable def stewartInputSplitEquiv (d : ℕ) :
    StewartGaussianInputs (d + 1) ≃ᵐ
      (Fin (d + 1) → ℝ) × StewartGaussianInputs d := by
  let α : Fin (d + 1) → Type := fun i => Fin (d + 1 - i.val) → ℝ
  exact (MeasurableEquiv.piFinSuccAbove α (0 : Fin (d + 1))).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (stewartTailCastEquiv d))

theorem stewartTailCoordinateCastEquiv_measurePreserving (d : ℕ)
    (j : Fin d) :
    MeasurePreserving (stewartTailCoordinateCastEquiv d j)
      (standardGaussianVectorMeasure (d + 1 - (j.val + 1)))
      (standardGaussianVectorMeasure (d - j.val)) := by
  unfold stewartTailCoordinateCastEquiv standardGaussianVectorMeasure
  simpa using MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin (d - j.val) => gaussianReal 0 1)
    (Equiv.cast (congrArg Fin (by omega :
      d + 1 - (j.val + 1) = d - j.val)))

theorem stewartTailCastEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (stewartTailCastEquiv d)
      (Measure.pi (fun j : Fin d =>
        standardGaussianVectorMeasure (d + 1 - (j.val + 1))))
      (stewartGaussianInputMeasure d) := by
  unfold stewartTailCastEquiv stewartGaussianInputMeasure
  simpa [StewartGaussianInputs, standardGaussianVectorMeasure] using
    MeasureTheory.measurePreserving_pi
      (fun j : Fin d => standardGaussianVectorMeasure (d + 1 - (j.val + 1)))
      (fun j : Fin d => standardGaussianVectorMeasure (d - j.val))
      (stewartTailCoordinateCastEquiv_measurePreserving d)

theorem stewartInputSplitEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (stewartInputSplitEquiv d)
      (stewartGaussianInputMeasure (d + 1))
      ((standardGaussianVectorMeasure (d + 1)).prod
        (stewartGaussianInputMeasure d)) := by
  let α : Fin (d + 1) → Type := fun i => Fin (d + 1 - i.val) → ℝ
  let μ : (i : Fin (d + 1)) → Measure (α i) := fun i =>
    standardGaussianVectorMeasure (d + 1 - i.val)
  have hsplit := MeasureTheory.measurePreserving_piFinSuccAbove μ
    (0 : Fin (d + 1))
  have htail := stewartTailCastEquiv_measurePreserving d
  letI : IsProbabilityMeasure (standardGaussianVectorMeasure (d + 1)) :=
    standardGaussianVectorMeasure_isProbabilityMeasure (d + 1)
  letI : SFinite (standardGaussianVectorMeasure (d + 1)) := inferInstance
  letI : SFinite (stewartGaussianInputMeasure d) := inferInstance
  exact ((MeasurePreserving.id
    (standardGaussianVectorMeasure (d + 1))).prod htail).comp hsplit

@[simp] theorem stewartInputSplitEquiv_fst (d : ℕ)
    (z : StewartGaussianInputs (d + 1)) :
    (stewartInputSplitEquiv d z).1 = z 0 := rfl

@[simp] theorem stewartInputSplitEquiv_snd (d : ℕ)
    (z : StewartGaussianInputs (d + 1)) (j : Fin d) :
    (stewartInputSplitEquiv d z).2 j =
      stewartTailCoordinateCastEquiv d j (z j.succ) := rfl

@[simp] theorem stewartInputSplitEquiv_symm_zero (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d) :
    (stewartInputSplitEquiv d).symm (x, t) 0 = x := by
  let z := (stewartInputSplitEquiv d).symm (x, t)
  have h := (stewartInputSplitEquiv d).apply_symm_apply (x, t)
  have hfst := congrArg Prod.fst h
  change z 0 = x
  change z 0 = x at hfst
  exact hfst

@[simp] theorem stewartInputSplitEquiv_symm_succ (d : ℕ)
    (x : Fin (d + 1) → ℝ) (t : StewartGaussianInputs d)
    (j : Fin d) :
    stewartTailCoordinateCastEquiv d j
        ((stewartInputSplitEquiv d).symm (x, t) j.succ) = t j := by
  let z := (stewartInputSplitEquiv d).symm (x, t)
  have h := (stewartInputSplitEquiv d).apply_symm_apply (x, t)
  have hsnd := congrArg Prod.snd h
  have hj := congrFun hsnd j
  change stewartTailCoordinateCastEquiv d j (z j.succ) = t j
  change stewartTailCoordinateCastEquiv d j (z j.succ) = t j at hj
  exact hj

end NumStability
