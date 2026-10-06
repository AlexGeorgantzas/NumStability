/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreIncidence

/-! # Higham Chapter 28: the finite affine atlas for real Ginibre eigenpairs

This module closes the genericity layer behind the Ginibre incidence chart.
If a real eigenvector misses the distinguished affine coordinate, a finite
coordinate swap moves a nonzero coordinate into that position.  The original
boundary condition then becomes one coordinate hyperplane in the incidence
domain.  Haar-null hyperplanes have Haar-null differentiable images, so the
entire missing-affine-eigenvector event is null. -/

namespace NumStability

open MeasureTheory Set

noncomputable section

def ginibreMatrixCoordinates {n : ℕ}
    (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ) :
    GinibreIncidenceCoordinates n :=
  (((fun i j => A (Sum.inl i) (Sum.inl j),
      fun j => A (Sum.inr ()) (Sum.inl j)),
    A (Sum.inr ()) (Sum.inr ())),
    fun i => A (Sum.inl i) (Sum.inr ()))

@[simp] theorem ginibreMatrixCoordinates_coordinatesMatrix {n : ℕ}
    (p : GinibreIncidenceCoordinates n) :
    ginibreMatrixCoordinates (ginibreCoordinatesMatrix p) = p := by
  rfl

@[simp] theorem ginibreCoordinatesMatrix_matrixCoordinates {n : ℕ}
    (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ) :
    ginibreCoordinatesMatrix (ginibreMatrixCoordinates A) = A := by
  ext (i | i) (j | j)
  · rfl
  · rcases j with ⟨⟩
    rfl
  · rcases i with ⟨⟩
    rfl
  · rcases i with ⟨⟩
    rcases j with ⟨⟩
    rfl

def ginibreSwapIndex (n : ℕ) (j : Fin n) :
    Fin n ⊕ Unit ≃ Fin n ⊕ Unit :=
  Equiv.swap (Sum.inl j) (Sum.inr ())

@[simp] theorem ginibreSwapIndex_symm_apply_last (n : ℕ) (j : Fin n) :
    (ginibreSwapIndex n j).symm (Sum.inr ()) = Sum.inl j := by
  simp [ginibreSwapIndex]

@[simp] theorem ginibreSwapIndex_symm_apply_chosen (n : ℕ) (j : Fin n) :
    (ginibreSwapIndex n j).symm (Sum.inl j) = Sum.inr () := by
  simp [ginibreSwapIndex]

def ginibreCoordinateSwap {n : ℕ} (j : Fin n)
    (p : GinibreIncidenceCoordinates n) : GinibreIncidenceCoordinates n :=
  ginibreMatrixCoordinates <|
    Matrix.reindex (ginibreSwapIndex n j) (ginibreSwapIndex n j)
      (ginibreCoordinatesMatrix p)

@[simp] theorem ginibreCoordinatesMatrix_coordinateSwap {n : ℕ}
    (j : Fin n) (p : GinibreIncidenceCoordinates n) :
    ginibreCoordinatesMatrix (ginibreCoordinateSwap j p) =
      Matrix.reindex (ginibreSwapIndex n j) (ginibreSwapIndex n j)
        (ginibreCoordinatesMatrix p) := by
  simp [ginibreCoordinateSwap]

theorem ginibreCoordinateSwap_involutive {n : ℕ} (j : Fin n)
    (p : GinibreIncidenceCoordinates n) :
    ginibreCoordinateSwap j (ginibreCoordinateSwap j p) = p := by
  apply (Function.LeftInverse.injective
    (@ginibreMatrixCoordinates_coordinatesMatrix n))
  rw [ginibreCoordinatesMatrix_coordinateSwap,
    ginibreCoordinatesMatrix_coordinateSwap]
  ext i k
  simp [Matrix.reindex_apply, ginibreSwapIndex]

theorem Matrix.reindex_mulVec_comp_symm
    {m : Type*} [Fintype m] [DecidableEq m]
    (e : m ≃ m) (A : Matrix m m ℝ) (v : m → ℝ) :
    (Matrix.reindex e e A).mulVec (v ∘ e.symm) =
      A.mulVec v ∘ e.symm := by
  ext i
  change (∑ j, A (e.symm i) (e.symm j) * v (e.symm j)) =
    ∑ j, A (e.symm i) j * v j
  exact e.symm.sum_comp (fun j => A (e.symm i) j * v j)

theorem ginibreSwap_normalized_eigenpair
    {n : ℕ} (j : Fin n)
    (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (v : Fin n ⊕ Unit → ℝ) (l : ℝ)
    (heig : A.mulVec v = l • v) (hj : v (Sum.inl j) ≠ 0) :
    let y : Fin n → ℝ := fun i =>
      v ((ginibreSwapIndex n j).symm (Sum.inl i)) / v (Sum.inl j)
    (Matrix.reindex (ginibreSwapIndex n j) (ginibreSwapIndex n j) A).mulVec
        (ginibreAffineEigenvector y) =
      l • ginibreAffineEigenvector y := by
  dsimp only
  let e := ginibreSwapIndex n j
  let c := v (Sum.inl j)
  have hc : c ≠ 0 := hj
  have haff : ginibreAffineEigenvector
        (fun i => v (e.symm (Sum.inl i)) / c) =
      c⁻¹ • (v ∘ e.symm) := by
    funext i
    rcases i with i | i
    · simp [ginibreAffineEigenvector, div_eq_inv_mul]
    · rcases i with ⟨⟩
      simp [ginibreAffineEigenvector, e, c, hc]
  rw [haff, Matrix.mulVec_smul, Matrix.reindex_mulVec_comp_symm,
    heig]
  ext i
  simp [Pi.smul_apply]
  ring

theorem ginibreIncidenceEigenvalue_eq_of_affine_eigenpair
    {n : ℕ} (p : GinibreIncidenceCoordinates n) (y : Fin n → ℝ)
    (l : ℝ)
    (heig : (ginibreCoordinatesMatrix p).mulVec
      (ginibreAffineEigenvector y) = l • ginibreAffineEigenvector y) :
    ginibreIncidenceEigenvalue (p.1, y) = l := by
  have hlast := congrFun heig (Sum.inr ())
  simpa [ginibreCoordinatesMatrix, ginibreAffineEigenvector,
    ginibreIncidenceEigenvalue, Matrix.mulVec, dotProduct, add_comm] using hlast

/-- Matrices admitting an eigenvector wholly contained in the boundary
hyperplane of the affine chart. -/
def ginibreAffineBoundaryEigenpairSet (n : ℕ) :
    Set (GinibreIncidenceCoordinates n) :=
  {p | ∃ (v : Fin n ⊕ Unit → ℝ) (l : ℝ),
    v ≠ 0 ∧
      (ginibreCoordinatesMatrix p).mulVec v = l • v ∧
      v (Sum.inr ()) = 0}

theorem ginibreAffineBoundaryEigenpairSet_subset_iUnion_swappedImages
    (n : ℕ) :
    ginibreAffineBoundaryEigenpairSet n ⊆
      ⋃ j : Fin n,
        (fun q => ginibreCoordinateSwap j (ginibreIncidenceChart q)) ''
          {q | q.2 j = 0} := by
  intro p hp
  rcases hp with ⟨v, l, hv, heig, hlast⟩
  have hex : ∃ j : Fin n, v (Sum.inl j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    rcases i with i | i
    · exact h i
    · rcases i with ⟨⟩
      exact hlast
  rcases hex with ⟨j, hj⟩
  let p' := ginibreCoordinateSwap j p
  let y : Fin n → ℝ := fun i =>
    v ((ginibreSwapIndex n j).symm (Sum.inl i)) / v (Sum.inl j)
  let q : GinibreIncidenceCoordinates n := (p'.1, y)
  have heig' : (ginibreCoordinatesMatrix p').mulVec
      (ginibreAffineEigenvector y) = l • ginibreAffineEigenvector y := by
    rw [ginibreCoordinatesMatrix_coordinateSwap]
    exact ginibreSwap_normalized_eigenpair j
      (ginibreCoordinatesMatrix p) v l heig hj
  have hlam : ginibreIncidenceEigenvalue q = l := by
    exact ginibreIncidenceEigenvalue_eq_of_affine_eigenpair p' y l heig'
  have hchart : ginibreIncidenceChart q = p' := by
    apply (ginibreIncidenceChart_fiber_iff_affine_eigenpair p' y).2
    rw [hlam]
    exact heig'
  have hq : q ∈ {q | q.2 j = 0} := by
    change y j = 0
    simp [y, hlast]
  apply Set.mem_iUnion.2
  refine ⟨j, ⟨q, hq, ?_⟩⟩
  change ginibreCoordinateSwap j (ginibreIncidenceChart q) = p
  rw [hchart]
  exact ginibreCoordinateSwap_involutive j p

theorem differentiable_ginibreCoordinateSwap {n : ℕ} (j : Fin n) :
    Differentiable ℝ (@ginibreCoordinateSwap n j) := by
  apply Differentiable.prodMk
  · apply Differentiable.prodMk
    · apply Differentiable.prodMk
      · rw [differentiable_pi]
        intro i
        rw [differentiable_pi]
        intro k
        simp only [Matrix.reindex_apply, ginibreCoordinatesMatrix]
        let ii := (ginibreSwapIndex n j).symm (Sum.inl i)
        let kk := (ginibreSwapIndex n j).symm (Sum.inl k)
        change Differentiable ℝ fun x => ginibreCoordinatesMatrix x ii kk
        rcases ii with ii | ii <;> rcases kk with kk | kk
        all_goals simp [ginibreCoordinatesMatrix]
        all_goals fun_prop
      · rw [differentiable_pi]
        intro k
        simp only [Matrix.reindex_apply, ginibreCoordinatesMatrix]
        let ii := (ginibreSwapIndex n j).symm (Sum.inr ())
        let kk := (ginibreSwapIndex n j).symm (Sum.inl k)
        change Differentiable ℝ fun x => ginibreCoordinatesMatrix x ii kk
        rcases ii with ii | ii <;> rcases kk with kk | kk
        all_goals simp [ginibreCoordinatesMatrix]
        all_goals fun_prop
    · simp only [Matrix.reindex_apply, ginibreCoordinatesMatrix]
      let ii := (ginibreSwapIndex n j).symm (Sum.inr ())
      let kk := (ginibreSwapIndex n j).symm (Sum.inr ())
      change Differentiable ℝ fun x => ginibreCoordinatesMatrix x ii kk
      rcases ii with ii | ii <;> rcases kk with kk | kk
      all_goals simp [ginibreCoordinatesMatrix]
      all_goals fun_prop
  · rw [differentiable_pi]
    intro i
    simp only [Matrix.reindex_apply, ginibreCoordinatesMatrix]
    let ii := (ginibreSwapIndex n j).symm (Sum.inl i)
    let kk := (ginibreSwapIndex n j).symm (Sum.inr ())
    change Differentiable ℝ fun x => ginibreCoordinatesMatrix x ii kk
    rcases ii with ii | ii <;> rcases kk with kk | kk
    all_goals simp [ginibreCoordinatesMatrix]
    all_goals fun_prop

def ginibreAffineCoordinateLinearMap {n : ℕ} (j : Fin n) :
    GinibreIncidenceCoordinates n →ₗ[ℝ] ℝ :=
  (LinearMap.proj j).comp (LinearMap.snd ℝ _ _)

theorem ginibreAffineCoordinateLinearMap_ker_ne_top {n : ℕ} (j : Fin n) :
    (ginibreAffineCoordinateLinearMap j).ker ≠ ⊤ := by
  intro h
  have hmem : (((0, 0), 0), Pi.single j 1) ∈
      (ginibreAffineCoordinateLinearMap j).ker := by rw [h]; trivial
  simpa [ginibreAffineCoordinateLinearMap] using hmem

theorem measure_ginibreAffineCoordinateHyperplane_eq_zero
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] (j : Fin n) :
    μ {q | q.2 j = 0} = 0 := by
  change μ ((ginibreAffineCoordinateLinearMap j).ker :
    Set (GinibreIncidenceCoordinates n)) = 0
  exact MeasureTheory.Measure.addHaar_submodule μ _
    (ginibreAffineCoordinateLinearMap_ker_ne_top j)

theorem measure_ginibreSwappedAffineBoundaryImage_eq_zero
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] (j : Fin n) :
    μ ((fun q => ginibreCoordinateSwap j (ginibreIncidenceChart q)) ''
      {q | q.2 j = 0}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
  · exact ((differentiable_ginibreCoordinateSwap j).comp
      differentiable_ginibreIncidenceChart).differentiableOn
  · exact measure_ginibreAffineCoordinateHyperplane_eq_zero n μ j

theorem measure_ginibreAffineBoundaryEigenpairSet_eq_zero
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] :
    μ (ginibreAffineBoundaryEigenpairSet n) = 0 := by
  apply measure_mono_null
    (ginibreAffineBoundaryEigenpairSet_subset_iUnion_swappedImages n)
  exact measure_iUnion_null fun j =>
    measure_ginibreSwappedAffineBoundaryImage_eq_zero n μ j

end
end NumStability
