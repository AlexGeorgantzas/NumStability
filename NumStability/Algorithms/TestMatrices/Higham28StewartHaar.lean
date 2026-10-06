/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalFibers

namespace NumStability

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-! # Stewart's Gaussian Householder producer has normalized Haar law -/

/-! ## Splitting the independent Gaussian tails -/

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
