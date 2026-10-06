/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Ginibre
import Mathlib.MeasureTheory.Integral.Pi

/-! # Higham Chapter 28: the finite real-Ginibre joint density

This file proves the unconditional measure-theoretic input to the finite
real-Ginibre eigenvalue calculation.  The iid Gaussian matrix law is exactly
the finite-product Lebesgue measure weighted by the product Gaussian density.
In particular, the Gaussian and Lebesgue matrix measures have the same null
sets, and the expected real-eigenvalue count is a density-weighted Lebesgue
integral.

The Kac--Rice/coarea evaluation of that integral is a separate geometric
step; it is not assumed here.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

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

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- The nested finite product of one-dimensional Lebesgue measures on real
`n × n` matrices. -/
noncomputable def realGinibreLebesgueMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => volume))

/-- The ordinary real-valued standard-Gaussian joint density of an `n × n`
matrix with respect to `realGinibreLebesgueMeasure`. -/
noncomputable def realGinibreDensityReal (n : ℕ) (A : RSqMat n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, gaussianPDFReal 0 1 (A i j)

theorem measurable_realGinibreDensityReal (n : ℕ) :
    Measurable (realGinibreDensityReal n) := by
  unfold realGinibreDensityReal
  fun_prop

theorem realGinibreDensityReal_pos (n : ℕ) (A : RSqMat n) :
    0 < realGinibreDensityReal n A := by
  unfold realGinibreDensityReal
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact gaussianPDFReal_pos 0 1 (A i j) (by norm_num)

theorem integrable_realGinibreDensityReal (n : ℕ) :
    Integrable (realGinibreDensityReal n) (realGinibreLebesgueMeasure n) := by
  unfold realGinibreDensityReal realGinibreLebesgueMeasure
  refine Integrable.fintype_prod
    (f := fun _ : Fin n => fun row : Fin n → ℝ =>
      ∏ j : Fin n, gaussianPDFReal 0 1 (row j))
    (μ := fun _ : Fin n => Measure.pi (fun _ : Fin n => volume)) ?_
  intro i
  refine Integrable.fintype_prod
    (f := fun _ : Fin n => gaussianPDFReal 0 1)
    (μ := fun _ : Fin n => volume) ?_
  intro j
  exact integrable_gaussianPDFReal 0 1

/-- Exact joint-density identity for the standard real-Ginibre matrix law. -/
theorem realGinibreMeasure_eq_withDensity (n : ℕ) :
    realGinibreMeasure n =
      (realGinibreLebesgueMeasure n).withDensity
        (fun A => ENNReal.ofReal (realGinibreDensityReal n A)) := by
  let rowLebesgue : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => volume)
  let rowDensity : (Fin n → ℝ) → ℝ :=
    fun x => ∏ j : Fin n, gaussianPDFReal 0 1 (x j)
  have hrowIntegrable : Integrable rowDensity rowLebesgue := by
    dsimp [rowDensity, rowLebesgue]
    apply Integrable.fintype_prod
    intro j
    exact integrable_gaussianPDFReal 0 1
  have hrowNonneg : ∀ x, 0 ≤ rowDensity x := by
    intro x
    exact Finset.prod_nonneg fun j _ => gaussianPDFReal_nonneg 0 1 (x j)
  have hrow : Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      rowLebesgue.withDensity (fun x => ENNReal.ofReal (rowDensity x)) := by
    have h := Measure.pi_withDensity_ofReal
      (fun _ : Fin n => volume)
      (fun _ : Fin n => gaussianPDFReal 0 1)
      (fun _ => integrable_gaussianPDFReal 0 1)
      (fun _ => gaussianPDFReal_nonneg 0 1)
    simpa [rowLebesgue, rowDensity, gaussianReal_of_var_ne_zero,
      gaussianPDF] using h
  unfold realGinibreMeasure realGinibreLebesgueMeasure realGinibreDensityReal
  rw [show (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      (fun _ : Fin n => rowLebesgue.withDensity
        (fun x => ENNReal.ofReal (rowDensity x))) by
    funext i
    exact hrow]
  simpa [rowLebesgue, rowDensity] using
    (Measure.pi_withDensity_ofReal
      (fun _ : Fin n => rowLebesgue)
      (fun _ : Fin n => rowDensity)
      (fun _ => hrowIntegrable)
      (fun _ => hrowNonneg))

/-- Every Lebesgue-null matrix event is real-Ginibre-null. -/
theorem realGinibreMeasure_absolutelyContinuous_lebesgue (n : ℕ) :
    realGinibreMeasure n ≪ realGinibreLebesgueMeasure n := by
  rw [realGinibreMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The strictly positive Gaussian density also gives the converse null-set
transfer: real-Ginibre and matrix Lebesgue measure are equivalent. -/
theorem realGinibreLebesgueMeasure_absolutelyContinuous (n : ℕ) :
    realGinibreLebesgueMeasure n ≪ realGinibreMeasure n := by
  rw [realGinibreMeasure_eq_withDensity]
  apply withDensity_absolutelyContinuous'
  · exact (measurable_realGinibreDensityReal n).ennreal_ofReal.aemeasurable
  · filter_upwards with A
    exact (ENNReal.ofReal_pos.2 (realGinibreDensityReal_pos n A)).ne'

/-- The expected real-eigenvalue count is exactly its density-weighted
Lebesgue matrix integral.  This is the measure-theoretic starting point for
the missing Kac--Rice/coarea evaluation. -/
theorem expectedRealEigenvalueCount_eq_lebesgue (n : ℕ) :
    expectedRealEigenvalueCount n =
      ∫ A : RSqMat n,
        realGinibreDensityReal n A * (realEigenvalueCount n A : ℝ)
        ∂realGinibreLebesgueMeasure n := by
  unfold expectedRealEigenvalueCount
  rw [realGinibreMeasure_eq_withDensity]
  calc
    (∫ A : RSqMat n, (realEigenvalueCount n A : ℝ)
        ∂(realGinibreLebesgueMeasure n).withDensity
          (fun A => ENNReal.ofReal (realGinibreDensityReal n A))) =
        ∫ A : RSqMat n,
          (ENNReal.ofReal (realGinibreDensityReal n A)).toReal •
            (realEigenvalueCount n A : ℝ)
          ∂realGinibreLebesgueMeasure n :=
      integral_withDensity_eq_integral_toReal_smul
        (measurable_realGinibreDensityReal n).ennreal_ofReal
        (ae_of_all _ fun A => ENNReal.ofReal_lt_top)
        (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with A
      rw [ENNReal.toReal_ofReal (le_of_lt (realGinibreDensityReal_pos n A))]
      simp [smul_eq_mul]

end NumStability
