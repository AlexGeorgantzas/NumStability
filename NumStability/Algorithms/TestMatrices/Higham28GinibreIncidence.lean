/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreRoots
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Higham Chapter 28: affine real-eigenpair incidence chart

This module formalizes the affine chart used in the finite real-Ginibre
eigenvalue calculation.  A point `(((B, w), b), y)` represents the normalized
eigenvector `(y, 1)`.  The chart replaces `y` by the unique top-right column
that makes `(y, 1)` an eigenvector.  Its Fréchet derivative is block lower
triangular, with tangent block `λI - (B - y wᵀ)`, so the absolute Jacobian
is `|det(B - y wᵀ - λI)|`.

The final fiber theorem identifies chart preimages exactly with normalized
affine real eigenpairs.  A finite-to-one area/coarea theorem is still needed
to turn this incidence calculation into the expected-root integral.
-/

namespace NumStability

open scoped BigOperators
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Function

noncomputable section

local instance (n : ℕ) : MeasurableSpace (GinibreRawMatrix n) := MeasurableSpace.pi

section LowerBlock

variable {M Y : Type*}
  [AddCommGroup M] [Module ℝ M]
  [AddCommGroup Y] [Module ℝ Y]

def LinearMap.lowerBlock (C : M →ₗ[ℝ] Y) (D : Y →ₗ[ℝ] Y) :
    (M × Y) →ₗ[ℝ] (M × Y) :=
  (LinearMap.fst ℝ M Y).prod
    (C.comp (LinearMap.fst ℝ M Y) + D.comp (LinearMap.snd ℝ M Y))

@[simp] theorem LinearMap.lowerBlock_apply
    (C : M →ₗ[ℝ] Y) (D : Y →ₗ[ℝ] Y) (p : M × Y) :
    LinearMap.lowerBlock C D p = (p.1, C p.1 + D p.2) := rfl

theorem LinearMap.det_lowerBlock
    [Module.Free ℝ M] [Module.Finite ℝ M]
    [Module.Free ℝ Y] [Module.Finite ℝ Y]
    (C : M →ₗ[ℝ] Y) (D : Y →ₗ[ℝ] Y) :
    (LinearMap.lowerBlock C D).det = D.det := by
  classical
  let bM := Module.Free.chooseBasis ℝ M
  let bY := Module.Free.chooseBasis ℝ Y
  rw [← LinearMap.det_toMatrix (bM.prod bY)]
  rw [show LinearMap.toMatrix (bM.prod bY) (bM.prod bY)
      (LinearMap.lowerBlock C D) =
        Matrix.fromBlocks 1 0 (LinearMap.toMatrix bM bY C)
          (LinearMap.toMatrix bY bY D) by
    ext (i | i) (j | j) <;>
      simp [LinearMap.lowerBlock, LinearMap.toMatrix_apply,
        Matrix.one_apply, Finsupp.single_eq_pi_single, Pi.single_apply]]
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
  exact LinearMap.det_toMatrix bY D

end LowerBlock

abbrev GinibreIncidenceNuisance (n : ℕ) :=
  (((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ)

abbrev GinibreIncidenceCoordinates (n : ℕ) :=
  GinibreIncidenceNuisance n × (Fin n → ℝ)

def ginibreIncidenceEigenvalue {n : ℕ}
    (q : GinibreIncidenceCoordinates n) : ℝ :=
  q.1.2 + ∑ j : Fin n, q.1.1.2 j * q.2 j

def ginibreIncidenceDeflatedBlock {n : ℕ}
    (q : GinibreIncidenceCoordinates n) : RSqMat n :=
  fun i j => q.1.1.1 i j - q.2 i * q.1.1.2 j

def ginibreIncidenceTopRight {n : ℕ}
    (q : GinibreIncidenceCoordinates n) : Fin n → ℝ :=
  fun i => ginibreIncidenceEigenvalue q * q.2 i -
    ∑ j : Fin n, q.1.1.1 i j * q.2 j

def ginibreIncidenceChart {n : ℕ}
    (q : GinibreIncidenceCoordinates n) : GinibreIncidenceCoordinates n :=
  (q.1, ginibreIncidenceTopRight q)

def ginibreIncidenceTangentMatrix {n : ℕ}
    (q : GinibreIncidenceCoordinates n) : RSqMat n :=
  ginibreIncidenceEigenvalue q • (1 : RSqMat n) -
    ginibreIncidenceDeflatedBlock q

def ginibreIncidenceNuisanceDerivative {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    GinibreIncidenceNuisance n →ₗ[ℝ] (Fin n → ℝ) where
  toFun dq := fun i =>
    dq.2 * q.2 i + (∑ j : Fin n, dq.1.2 j * q.2 j) * q.2 i -
      ∑ j : Fin n, dq.1.1 i j * q.2 j
  map_add' p r := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    ext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    have hw : (∑ j : Fin n, c * p.1.2 j * q.2 j) =
        c * ∑ j : Fin n, p.1.2 j * q.2 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hB : (∑ j : Fin n, c * p.1.1 i j * q.2 j) =
        c * ∑ j : Fin n, p.1.1 i j * q.2 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hw, hB]
    ring

def ginibreIncidenceDerivativeLinearMap {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    GinibreIncidenceCoordinates n →ₗ[ℝ] GinibreIncidenceCoordinates n :=
  LinearMap.lowerBlock (ginibreIncidenceNuisanceDerivative q)
    (Matrix.toLin' (ginibreIncidenceTangentMatrix q))

theorem ginibreIncidenceDerivativeLinearMap_det {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    (ginibreIncidenceDerivativeLinearMap q).det =
      (ginibreIncidenceTangentMatrix q).det := by
  rw [ginibreIncidenceDerivativeLinearMap, LinearMap.det_lowerBlock,
    LinearMap.det_toLin']

theorem ginibreIncidenceTangentMatrix_eq {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    ginibreIncidenceTangentMatrix q =
      ginibreIncidenceEigenvalue q • (1 : RSqMat n) -
        ginibreIncidenceDeflatedBlock q := rfl

theorem abs_ginibreIncidenceDerivativeLinearMap_det {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    |(ginibreIncidenceDerivativeLinearMap q).det| =
      |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| := by
  rw [ginibreIncidenceDerivativeLinearMap_det]
  have hneg : ginibreIncidenceTangentMatrix q =
      -(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)) := by
    ext i j
    simp [ginibreIncidenceTangentMatrix]
  rw [hneg, Matrix.det_neg]
  simp

set_option maxHeartbeats 800000 in
theorem hasFDerivAt_ginibreIncidenceTopRight {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    HasFDerivAt ginibreIncidenceTopRight
      ((ContinuousLinearMap.snd ℝ (GinibreIncidenceNuisance n) (Fin n → ℝ)).comp
        (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap) q := by
  change HasFDerivAt (fun q' => fun i => ginibreIncidenceTopRight q' i)
    ((ContinuousLinearMap.snd ℝ (GinibreIncidenceNuisance n) (Fin n → ℝ)).comp
      (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap) q
  refine hasFDerivAt_pi'' (𝕜 := ℝ) (E := GinibreIncidenceCoordinates n)
    (ι := Fin n) (F' := fun _ : Fin n => ℝ) (x := q)
    (Φ := fun q' i => ginibreIncidenceTopRight q' i)
    (Φ' := (ContinuousLinearMap.snd ℝ
      (GinibreIncidenceNuisance n) (Fin n → ℝ)).comp
        (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap) ?_
  intro i
  let fstQ : GinibreIncidenceCoordinates n →L[ℝ] GinibreIncidenceNuisance n :=
    ContinuousLinearMap.fst ℝ _ _
  let sndQ : GinibreIncidenceCoordinates n →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.snd ℝ _ _
  let fstN : GinibreIncidenceNuisance n →L[ℝ]
      ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) :=
    ContinuousLinearMap.fst ℝ _ _
  let sndN : GinibreIncidenceNuisance n →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ _ _
  let fstBW : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ]
      (Fin n → Fin n → ℝ) :=
    ContinuousLinearMap.fst ℝ _ _
  let sndBW : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ]
      (Fin n → ℝ) :=
    ContinuousLinearMap.snd ℝ _ _
  let BEntry (a b : Fin n) : GinibreIncidenceCoordinates n →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj b).comp <|
      (ContinuousLinearMap.proj a).comp <| fstBW.comp <| fstN.comp fstQ
  let wEntry (j : Fin n) : GinibreIncidenceCoordinates n →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j).comp <| sndBW.comp <| fstN.comp fstQ
  let bEntry : GinibreIncidenceCoordinates n →L[ℝ] ℝ := sndN.comp fstQ
  let yEntry (j : Fin n) : GinibreIncidenceCoordinates n →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j).comp sndQ
  have hB (a b : Fin n) :
      HasFDerivAt (fun q' : GinibreIncidenceCoordinates n => q'.1.1.1 a b)
        (BEntry a b) q := by
    simpa [BEntry, fstBW, fstN, fstQ] using (BEntry a b).hasFDerivAt
  have hw (j : Fin n) :
      HasFDerivAt (fun q' : GinibreIncidenceCoordinates n => q'.1.1.2 j)
        (wEntry j) q := by
    simpa [wEntry, sndBW, fstN, fstQ] using (wEntry j).hasFDerivAt
  have hb : HasFDerivAt (fun q' : GinibreIncidenceCoordinates n => q'.1.2)
      bEntry q := by
    simpa [bEntry, sndN, fstQ] using bEntry.hasFDerivAt
  have hy (j : Fin n) :
      HasFDerivAt (fun q' : GinibreIncidenceCoordinates n => q'.2 j)
        (yEntry j) q := by
    simpa [yEntry, sndQ] using (yEntry j).hasFDerivAt
  have hwy : HasFDerivAt
      (fun q' : GinibreIncidenceCoordinates n =>
        ∑ j : Fin n, q'.1.1.2 j * q'.2 j)
      (∑ j : Fin n, (q.1.1.2 j • yEntry j + q.2 j • wEntry j)) q := by
    convert HasFDerivAt.sum (u := Finset.univ)
      (fun j hj => (hw j).mul (hy j)) using 1
    funext q'
    simp [Finset.sum_apply]
  have hlam : HasFDerivAt ginibreIncidenceEigenvalue
      (bEntry + ∑ j : Fin n,
        (q.1.1.2 j • yEntry j + q.2 j • wEntry j)) q := by
    simpa [ginibreIncidenceEigenvalue] using hb.add hwy
  have hBy : HasFDerivAt
      (fun q' : GinibreIncidenceCoordinates n =>
        ∑ j : Fin n, q'.1.1.1 i j * q'.2 j)
      (∑ j : Fin n,
        (q.1.1.1 i j • yEntry j + q.2 j • BEntry i j)) q := by
    convert HasFDerivAt.sum (u := Finset.univ)
      (fun j hj => (hB i j).mul (hy j)) using 1
    funext q'
    simp [Finset.sum_apply]
  have hcoord := (hlam.mul (hy i)).sub hBy
  convert hcoord using 1
  · apply ContinuousLinearMap.ext
    intro dq
    simp [ginibreIncidenceDerivativeLinearMap, LinearMap.lowerBlock,
      ginibreIncidenceNuisanceDerivative, ginibreIncidenceTangentMatrix,
      ginibreIncidenceDeflatedBlock, ginibreIncidenceEigenvalue,
      BEntry, wEntry, bEntry, yEntry, fstQ, sndQ, fstN, sndN, fstBW, sndBW,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp_rw [Finset.sum_add_distrib]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have hfactor : (∑ x : Fin n, q.2 i * q.1.1.2 x * dq.2 x) =
        q.2 i * ∑ x : Fin n, q.1.1.2 x * dq.2 x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hfactor]
    have hcommw : (∑ x : Fin n, dq.1.1.2 x * q.2 x) =
        ∑ x : Fin n, q.2 x * dq.1.1.2 x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    have hcommB : (∑ x : Fin n, dq.1.1.1 i x * q.2 x) =
        ∑ x : Fin n, q.2 x * dq.1.1.1 i x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hcommw, hcommB]
    ring

set_option maxHeartbeats 800000 in
theorem hasFDerivAt_ginibreIncidenceChart {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    HasFDerivAt ginibreIncidenceChart
      (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap q := by
  let fstQ : GinibreIncidenceCoordinates n →L[ℝ] GinibreIncidenceNuisance n :=
    ContinuousLinearMap.fst ℝ _ _
  let sndOut : GinibreIncidenceCoordinates n →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.snd ℝ _ _
  have hpair := (hasFDerivAt_fst (p := q)).prodMk
    (hasFDerivAt_ginibreIncidenceTopRight q)
  have hderiv : fstQ.prod
      (sndOut.comp (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap) =
      (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro dq
    rfl
  rw [hderiv] at hpair
  simpa [ginibreIncidenceChart] using hpair

theorem fderiv_ginibreIncidenceChart {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    fderiv ℝ ginibreIncidenceChart q =
      (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap :=
  (hasFDerivAt_ginibreIncidenceChart q).fderiv

theorem abs_det_fderiv_ginibreIncidenceChart {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    |(fderiv ℝ ginibreIncidenceChart q).det| =
      |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| := by
  rw [fderiv_ginibreIncidenceChart]
  exact abs_ginibreIncidenceDerivativeLinearMap_det q

theorem differentiable_ginibreIncidenceChart {n : ℕ} :
    Differentiable ℝ (@ginibreIncidenceChart n) :=
  fun q => (hasFDerivAt_ginibreIncidenceChart q).differentiableAt

theorem continuous_ginibreIncidenceChart {n : ℕ} :
    Continuous (@ginibreIncidenceChart n) :=
  differentiable_ginibreIncidenceChart.continuous

theorem measurable_ginibreIncidenceChart {n : ℕ} :
    Measurable (@ginibreIncidenceChart n) :=
  continuous_ginibreIncidenceChart.measurable

def ginibreIncidenceMatrix {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks q.1.1.1
    (fun i _ => ginibreIncidenceTopRight q i)
    (fun _ j => q.1.1.2 j)
    (fun _ _ => q.1.2)

/-- Interpret the target coordinates of the incidence chart as a block
matrix: the last coordinate is now the top-right matrix column. -/
def ginibreCoordinatesMatrix {n : ℕ}
    (p : GinibreIncidenceCoordinates n) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks p.1.1.1
    (fun i _ => p.2 i)
    (fun _ j => p.1.1.2 j)
    (fun _ _ => p.1.2)

def unitEquivFinOne : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := (Fin.eq_zero i).symm

def ginibreBlockIndexEquiv (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) unitEquivFinOne).trans finSumFinEquiv

/-- Reindex the affine block matrix by `Fin (n+1)`, so the root-count
measurability producer can be applied without changing its characteristic
polynomial. -/
def ginibreCoordinatesFinMatrix {n : ℕ}
    (p : GinibreIncidenceCoordinates n) : GinibreRawMatrix (n + 1) :=
  Matrix.reindex (ginibreBlockIndexEquiv n) (ginibreBlockIndexEquiv n)
    (ginibreCoordinatesMatrix p)

theorem ginibreCoordinatesFinMatrix_charpoly {n : ℕ}
    (p : GinibreIncidenceCoordinates n) :
    (Matrix.of (ginibreCoordinatesFinMatrix p)).charpoly =
      (ginibreCoordinatesMatrix p).charpoly :=
  Matrix.charpoly_reindex (ginibreBlockIndexEquiv n) _

theorem measurable_ginibreCoordinatesFinMatrix {n : ℕ} :
    Measurable (@ginibreCoordinatesFinMatrix n) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  change Measurable (fun p : GinibreIncidenceCoordinates n =>
    ginibreCoordinatesMatrix p
      ((ginibreBlockIndexEquiv n).symm i)
      ((ginibreBlockIndexEquiv n).symm j))
  generalize (ginibreBlockIndexEquiv n).symm i = ii
  generalize (ginibreBlockIndexEquiv n).symm j = jj
  rcases ii with ii | ii <;> rcases jj with jj | jj
  · simp [ginibreCoordinatesMatrix]
    fun_prop
  · rcases ii with ⟨⟩
    simp [ginibreCoordinatesMatrix]
    fun_prop
  · rcases jj with ⟨⟩
    simp [ginibreCoordinatesMatrix]
    fun_prop
  · rcases ii with ⟨⟩
    rcases jj with ⟨⟩
    simp [ginibreCoordinatesMatrix]
    fun_prop

theorem continuous_ginibreIncidenceEigenvalue {n : ℕ} :
    Continuous (@ginibreIncidenceEigenvalue n) := by
  unfold ginibreIncidenceEigenvalue
  fun_prop

theorem measurable_ginibreIncidenceEigenvalue {n : ℕ} :
    Measurable (@ginibreIncidenceEigenvalue n) :=
  continuous_ginibreIncidenceEigenvalue.measurable

/-- Rank of the chart eigenvalue among the real characteristic roots lying
strictly below it.  Algebraic multiplicity is retained. -/
def ginibreIncidenceRootRank {n : ℕ}
    (q : GinibreIncidenceCoordinates n) : ℕ :=
  realEigenvalueBelowCount
    (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q),
      ginibreIncidenceEigenvalue q)

theorem measurable_ginibreIncidenceRootRank (n : ℕ) :
    Measurable (@ginibreIncidenceRootRank n) := by
  apply (measurable_realEigenvalueBelowCount (n + 1)).comp
  exact (measurable_ginibreCoordinatesFinMatrix.comp
    measurable_ginibreIncidenceChart).prodMk
      measurable_ginibreIncidenceEigenvalue

def ginibreIncidenceRegularSet (n : ℕ) : Set (GinibreIncidenceCoordinates n) :=
  {q | (ginibreIncidenceTangentMatrix q).det ≠ 0}

theorem continuous_ginibreIncidenceTangentDet {n : ℕ} :
    Continuous (fun q : GinibreIncidenceCoordinates n =>
      (ginibreIncidenceTangentMatrix q).det) := by
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  unfold ginibreIncidenceTangentMatrix ginibreIncidenceDeflatedBlock
    ginibreIncidenceEigenvalue
  by_cases hij : i = j
  · subst j
    simp
    fun_prop
  · simp [hij]
    fun_prop

theorem measurableSet_ginibreIncidenceRegularSet (n : ℕ) :
    MeasurableSet (ginibreIncidenceRegularSet n) := by
  exact (measurableSet_eq_fun
    continuous_ginibreIncidenceTangentDet.measurable measurable_const).compl

/-- The `k`th measurable rank piece of the regular incidence chart.  There
are at most `n+2` pieces; the harmless extra endpoint avoids a separate
simple-root bound in the covering argument. -/
def ginibreIncidenceRankPiece (n : ℕ) (k : Fin (n + 2)) :
    Set (GinibreIncidenceCoordinates n) :=
  ginibreIncidenceRegularSet n ∩ {q | ginibreIncidenceRootRank q = k.val}

theorem measurableSet_ginibreIncidenceRankPiece (n : ℕ) (k : Fin (n + 2)) :
    MeasurableSet (ginibreIncidenceRankPiece n k) := by
  exact (measurableSet_ginibreIncidenceRegularSet n).inter
    (measurableSet_eq_fun (measurable_ginibreIncidenceRootRank n) measurable_const)

theorem pairwiseDisjoint_ginibreIncidenceRankPiece (n : ℕ) :
    Pairwise (fun i j => Disjoint (ginibreIncidenceRankPiece n i)
      (ginibreIncidenceRankPiece n j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro q hqi hqj
  have hrank : i.val = j.val := hqi.2.symm.trans hqj.2
  exact hij (Fin.ext hrank)

theorem iUnion_ginibreIncidenceRankPiece (n : ℕ) :
    (⋃ k : Fin (n + 2), ginibreIncidenceRankPiece n k) =
      ginibreIncidenceRegularSet n := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun k => Set.inter_subset_left
  · intro q hq
    have hrank : ginibreIncidenceRootRank q < n + 2 := by
      have hle := realEigenvalueBelowCount_le
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q),
          ginibreIncidenceEigenvalue q)
      change ginibreIncidenceRootRank q ≤ n + 1 at hle
      omega
    exact Set.mem_iUnion.2
      ⟨⟨ginibreIncidenceRootRank q, hrank⟩, hq, rfl⟩

theorem ginibreCoordinatesMatrix_chart {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    ginibreCoordinatesMatrix (ginibreIncidenceChart q) =
      ginibreIncidenceMatrix q := rfl

/-! ## Exact characteristic-polynomial factorization -/

/-- The elementary shear whose last column is the normalized affine
eigenvector `(y,1)`. -/
def ginibreIncidenceShear {n : ℕ} (q : GinibreIncidenceCoordinates n) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 (fun i _ => q.2 i) 0 1

def ginibreIncidenceShearInv {n : ℕ} (q : GinibreIncidenceCoordinates n) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 (fun i _ => -q.2 i) 0 1

/-- After shearing by the affine eigenvector, the incidence matrix is block
lower triangular with the deflated block in the upper-left corner. -/
def ginibreIncidenceTriangular {n : ℕ} (q : GinibreIncidenceCoordinates n) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks (ginibreIncidenceDeflatedBlock q) 0
    (fun _ j => q.1.1.2 j) (fun _ _ => ginibreIncidenceEigenvalue q)

theorem ginibreIncidenceShear_mul_inv {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    ginibreIncidenceShear q * ginibreIncidenceShearInv q = 1 := by
  simp [ginibreIncidenceShear, ginibreIncidenceShearInv,
    Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem ginibreIncidence_inv_mul_matrix_mul_shear {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    ginibreIncidenceShearInv q * ginibreIncidenceMatrix q * ginibreIncidenceShear q =
      ginibreIncidenceTriangular q := by
  simp [ginibreIncidenceShear, ginibreIncidenceShearInv,
    ginibreIncidenceMatrix, ginibreIncidenceTriangular,
    ginibreIncidenceTopRight, ginibreIncidenceEigenvalue,
    Matrix.fromBlocks_multiply]
  constructor
  · ext i j
    simp [ginibreIncidenceDeflatedBlock, Matrix.mul_apply]
    ring_nf
  constructor
  · ext i u
    rcases u with ⟨⟩
    simp [Matrix.mul_apply]
    have hexpand :
        (∑ x : Fin n,
          (q.1.1.1 i x + -(q.2 i * q.1.1.2 x)) * q.2 x) =
          (∑ x : Fin n, q.1.1.1 i x * q.2 x) -
            q.2 i * ∑ x : Fin n, q.1.1.2 x * q.2 x := by
      calc
        _ = ∑ x : Fin n,
            (q.1.1.1 i x * q.2 x - q.2 i * (q.1.1.2 x * q.2 x)) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
        _ = (∑ x : Fin n, q.1.1.1 i x * q.2 x) -
            ∑ x : Fin n, q.2 i * (q.1.1.2 x * q.2 x) := by
              rw [Finset.sum_sub_distrib]
        _ = _ := by rw [Finset.mul_sum]
    rw [hexpand]
    ring
  · ext u v
    rcases u with ⟨⟩
    rcases v with ⟨⟩
    simp [Matrix.mul_apply]
    ring

/-- The characteristic polynomial factors into the distinguished linear
factor and the deflated-block characteristic polynomial.  Consequently the
incidence Jacobian is nonzero exactly when the distinguished root occurs
with multiplicity one. -/
theorem ginibreIncidenceMatrix_charpoly_factor {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    (ginibreIncidenceMatrix q).charpoly =
      (ginibreIncidenceDeflatedBlock q).charpoly *
        (Polynomial.X - Polynomial.C (ginibreIncidenceEigenvalue q)) := by
  have hcomm := Matrix.charpoly_mul_comm
    (ginibreIncidenceShearInv q * ginibreIncidenceMatrix q)
    (ginibreIncidenceShear q)
  rw [ginibreIncidence_inv_mul_matrix_mul_shear] at hcomm
  have hright : ginibreIncidenceShear q *
      (ginibreIncidenceShearInv q * ginibreIncidenceMatrix q) =
        ginibreIncidenceMatrix q := by
    rw [← Matrix.mul_assoc, ginibreIncidenceShear_mul_inv, one_mul]
  rw [hright] at hcomm
  rw [← hcomm]
  unfold ginibreIncidenceTriangular
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  congr 1
  have hdiag : (fun _ _ : Unit => ginibreIncidenceEigenvalue q) =
      Matrix.diagonal (fun _ : Unit => ginibreIncidenceEigenvalue q) := by
    ext i j
    rcases i with ⟨⟩
    rcases j with ⟨⟩
    simp
  rw [hdiag, Matrix.charpoly_diagonal]
  simp

/-- The chart Jacobian is nonzero precisely when its distinguished real root
has algebraic multiplicity one in the output matrix. -/
theorem mem_ginibreIncidenceRegularSet_iff_root_count_eq_one {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    q ∈ ginibreIncidenceRegularSet n ↔
      (ginibreIncidenceMatrix q).charpoly.roots.count
        (ginibreIncidenceEigenvalue q) = 1 := by
  let D := ginibreIncidenceDeflatedBlock q
  let l := ginibreIncidenceEigenvalue q
  have hD : D.charpoly ≠ 0 := (Matrix.charpoly_monic D).ne_zero
  have hlin : (Polynomial.X - Polynomial.C l : Polynomial ℝ) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero l
  have hroots : (ginibreIncidenceMatrix q).charpoly.roots =
      D.charpoly.roots + {l} := by
    rw [ginibreIncidenceMatrix_charpoly_factor]
    rw [Polynomial.roots_mul (mul_ne_zero hD hlin),
      Polynomial.roots_X_sub_C]
  rw [hroots, Multiset.count_add, Multiset.count_singleton]
  change q ∈ ginibreIncidenceRegularSet n ↔
    D.charpoly.roots.count l + (if l = l then 1 else 0) = 1
  simp only [ite_true]
  have hcount : D.charpoly.roots.count l + 1 = 1 ↔
      D.charpoly.roots.count l = 0 := by omega
  rw [hcount]
  change (ginibreIncidenceTangentMatrix q).det ≠ 0 ↔
    D.charpoly.roots.count l = 0
  rw [Multiset.count_eq_zero]
  rw [Polynomial.mem_roots hD]
  unfold Polynomial.IsRoot
  rw [Matrix.eval_charpoly]
  rw [show Matrix.scalar (Fin n) l - D =
      ginibreIncidenceTangentMatrix q by
    ext i j
    simp [D, l, ginibreIncidenceTangentMatrix, Matrix.scalar_apply,
      Matrix.one_apply, Matrix.diagonal_apply]]

def ginibreAffineEigenvector {n : ℕ} (y : Fin n → ℝ) :
    Fin n ⊕ Unit → ℝ :=
  Sum.elim y (fun _ => 1)

theorem ginibreIncidenceMatrix_has_eigenpair {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    (ginibreIncidenceMatrix q).mulVec (ginibreAffineEigenvector q.2) =
      ginibreIncidenceEigenvalue q • ginibreAffineEigenvector q.2 := by
  ext i
  rcases i with i | i
  · simp [ginibreIncidenceMatrix, ginibreAffineEigenvector,
      ginibreIncidenceTopRight, Matrix.mulVec, dotProduct]
  · rcases i with ⟨⟩
    simp [ginibreIncidenceMatrix, ginibreAffineEigenvector,
      ginibreIncidenceEigenvalue, Matrix.mulVec, dotProduct]
    ring

/-- A point lies in a fiber of the incidence chart exactly when its affine
coordinate is a normalized real eigenvector of the represented matrix. -/
theorem ginibreIncidenceChart_fiber_iff_affine_eigenpair {n : ℕ}
    (p : GinibreIncidenceCoordinates n) (y : Fin n → ℝ) :
    ginibreIncidenceChart (p.1, y) = p ↔
      (ginibreCoordinatesMatrix p).mulVec (ginibreAffineEigenvector y) =
        ginibreIncidenceEigenvalue (p.1, y) • ginibreAffineEigenvector y := by
  constructor
  · intro h
    rw [← h, ginibreCoordinatesMatrix_chart]
    exact ginibreIncidenceMatrix_has_eigenpair (p.1, y)
  · intro h
    apply Prod.ext
    · rfl
    · funext i
      have hi := congrFun h (Sum.inl i)
      simp [ginibreCoordinatesMatrix, ginibreAffineEigenvector,
        ginibreIncidenceChart, ginibreIncidenceTopRight,
        Matrix.mulVec, dotProduct] at hi ⊢
      linarith

/-- The eigenvalue distinguished by the incidence chart is a root of the
characteristic polynomial of its output matrix. -/
theorem ginibreIncidenceEigenvalue_isRoot_charpoly {n : ℕ}
    (q : GinibreIncidenceCoordinates n) :
    (Matrix.charpoly (Matrix.of
      (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))).IsRoot
        (ginibreIncidenceEigenvalue q) := by
  have hv_ne : ginibreAffineEigenvector q.2 ≠ 0 := by
    intro hv
    have hlast := congrFun hv (Sum.inr ())
    simpa [ginibreAffineEigenvector] using hlast
  have heig :
      Matrix.mulVec (ginibreIncidenceMatrix q) (ginibreAffineEigenvector q.2) =
        ginibreIncidenceEigenvalue q • ginibreAffineEigenvector q.2 :=
    ginibreIncidenceMatrix_has_eigenpair q
  have hhas : Module.End.HasEigenvalue
      (Matrix.toLin' (ginibreIncidenceMatrix q))
      (ginibreIncidenceEigenvalue q) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv_ne⟩
    simpa [Matrix.toLin'_apply] using heig
  have hroot : (Matrix.charpoly (ginibreIncidenceMatrix q)).IsRoot
      (ginibreIncidenceEigenvalue q) := by
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hhas
  rw [ginibreCoordinatesFinMatrix_charpoly,
    ginibreCoordinatesMatrix_chart]
  exact hroot

/-- Along one chart fiber, increasing the distinguished real eigenvalue
strictly increases its root rank. -/
theorem ginibreIncidenceRootRank_lt_of_chart_eq {n : ℕ}
    {q r : GinibreIncidenceCoordinates n}
    (hchart : ginibreIncidenceChart q = ginibreIncidenceChart r)
    (hlt : ginibreIncidenceEigenvalue q < ginibreIncidenceEigenvalue r) :
    ginibreIncidenceRootRank q < ginibreIncidenceRootRank r := by
  unfold ginibreIncidenceRootRank realEigenvalueBelowCount
  rw [hchart]
  let P := Matrix.charpoly (Matrix.of
    (ginibreCoordinatesFinMatrix (ginibreIncidenceChart r)))
  have hP : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hmem : ginibreIncidenceEigenvalue q ∈ P.roots := by
    apply (Polynomial.mem_roots hP).2
    simpa [P, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
  exact card_filter_lt_card_filter_of_mem P.roots hmem hlt

/-- On the regular locus, the chart output and distinguished eigenvalue
determine the affine eigenvector uniquely. -/
theorem ginibreIncidence_eq_of_chart_eq_of_eigenvalue_eq_of_regular {n : ℕ}
    {q r : GinibreIncidenceCoordinates n}
    (hchart : ginibreIncidenceChart q = ginibreIncidenceChart r)
    (hlam : ginibreIncidenceEigenvalue q = ginibreIncidenceEigenvalue r)
    (hreg : q ∈ ginibreIncidenceRegularSet n) : q = r := by
  rcases q with ⟨p, y⟩
  rcases r with ⟨p', z⟩
  have hp : p = p' := by
    simpa [ginibreIncidenceChart] using congrArg Prod.fst hchart
  subst p'
  have hg : ginibreIncidenceTopRight (p, y) =
      ginibreIncidenceTopRight (p, z) := by
    simpa [ginibreIncidenceChart] using congrArg Prod.snd hchart
  have hwy : (∑ j : Fin n, p.1.2 j * y j) =
      ∑ j : Fin n, p.1.2 j * z j := by
    simpa [ginibreIncidenceEigenvalue] using hlam
  have hzero : Matrix.toLin' (ginibreIncidenceTangentMatrix (p, y)) (y - z) = 0 := by
    ext i
    have hgi := congrFun hg i
    simp only [ginibreIncidenceTopRight] at hgi
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      ginibreIncidenceTangentMatrix, ginibreIncidenceDeflatedBlock,
      Pi.sub_apply]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have hwzero : (∑ j : Fin n, p.1.2 j * (y j - z j)) = 0 := by
      calc
        (∑ j : Fin n, p.1.2 j * (y j - z j)) =
            ∑ j : Fin n, (p.1.2 j * y j - p.1.2 j * z j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ j : Fin n, p.1.2 j * y j) -
            ∑ j : Fin n, p.1.2 j * z j := by
          rw [Finset.sum_sub_distrib]
        _ = 0 := by rw [hwy]; ring
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have hyfactor : (∑ x : Fin n, y i * p.1.2 x * y x) =
        y i * ∑ x : Fin n, p.1.2 x * y x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    have hzfactor : (∑ x : Fin n, y i * p.1.2 x * z x) =
        y i * ∑ x : Fin n, p.1.2 x * z x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hyfactor, hzfactor, hwy]
    rw [← hlam] at hgi
    linarith
  have hdet : (Matrix.toLin' (ginibreIncidenceTangentMatrix (p, y))).det ≠ 0 := by
    rwa [LinearMap.det_toLin']
  have hinj : Function.Injective
      (Matrix.toLin' (ginibreIncidenceTangentMatrix (p, y))) := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 hker)
  have hyz : y - z = 0 := hinj (hzero.trans (map_zero _).symm)
  have : y = z := sub_eq_zero.mp hyz
  subst z
  rfl

theorem injOn_ginibreIncidenceChart_rankPiece (n : ℕ) (k : Fin (n + 2)) :
    Set.InjOn ginibreIncidenceChart (ginibreIncidenceRankPiece n k) := by
  intro q hq r hr hchart
  rcases lt_trichotomy (ginibreIncidenceEigenvalue q)
      (ginibreIncidenceEigenvalue r) with hlt | heq | hgt
  · have hrank := ginibreIncidenceRootRank_lt_of_chart_eq hchart hlt
    rw [hq.2, hr.2] at hrank
    exact (lt_irrefl _ hrank).elim
  · exact ginibreIncidence_eq_of_chart_eq_of_eigenvalue_eq_of_regular
      hchart heq hq.1
  · have hrank := ginibreIncidenceRootRank_lt_of_chart_eq hchart.symm hgt
    rw [hq.2, hr.2] at hrank
    exact (lt_irrefl _ hrank).elim

/-! ## The finite-to-one area formula obtained from the rank partition -/

/-- Sum ordinary injective change-of-variables over a finite measurable
partition.  This is a local finite-to-one area formula and does not assume a
coarea API. -/
theorem lintegral_finite_partition_image_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    {ι : Type*} [Fintype ι]
    {f : E → E} {f' : E → E →L[ℝ] E}
    (s : ι → Set E)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Disjoint on s))
    (hf' : ∀ x, HasFDerivAt f (f' x) x)
    (hinj : ∀ i, InjOn f (s i))
    (g : E → ℝ≥0∞) :
    ∫⁻ x in ⋃ i, s i, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ =
      ∑ i, ∫⁻ y in f '' s i, g y ∂μ := by
  rw [lintegral_iUnion hs hdisj, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul
    μ (hs i) (fun x hx => (hf' x).hasFDerivWithinAt) (hinj i) g).symm

/-- Finite-to-one area identity for the regular Ginibre incidence chart,
proved by the explicit real-root-rank partition. -/
theorem lintegral_ginibreIncidence_regular_eq_sum_rank_images
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [IsAddHaarMeasure μ]
    (g : GinibreIncidenceCoordinates n → ℝ≥0∞) :
    ∫⁻ q in ginibreIncidenceRegularSet n,
        ENNReal.ofReal |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∑ k : Fin (n + 2),
        ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece n k,
          g p ∂μ := by
  rw [← iUnion_ginibreIncidenceRankPiece]
  exact lintegral_finite_partition_image_eq μ
    (ginibreIncidenceRankPiece n)
    (measurableSet_ginibreIncidenceRankPiece n)
    (pairwiseDisjoint_ginibreIncidenceRankPiece n)
    hasFDerivAt_ginibreIncidenceChart
    (injOn_ginibreIncidenceChart_rankPiece n) g

/-- Sard's lemma removes every critical value of the incidence chart.  In
particular, once a real eigenvalue is represented in this affine chart, a
multiple occurrence lies in a Haar-null matrix event by
`mem_ginibreIncidenceRegularSet_iff_root_count_eq_one`. -/
theorem measure_ginibreIncidence_criticalImage_eq_zero
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [IsAddHaarMeasure μ] :
    μ (ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun q =>
      (ginibreIncidenceDerivativeLinearMap q).toContinuousLinearMap)
  · intro q hq
    exact (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt
  · intro q hq
    change (ginibreIncidenceDerivativeLinearMap q).det = 0
    rw [ginibreIncidenceDerivativeLinearMap_det]
    simpa [ginibreIncidenceRegularSet] using hq

end
end NumStability
