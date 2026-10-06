/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreOrthogonalFiber
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedExpectation
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRankTransfer
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedKernel
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedIncidenceAlgebra
import NumStability.Algorithms.TestMatrices.Higham28GinibreJointDensity
import NumStability.Algorithms.TestMatrices.Higham28GinibreTruncatedIncidence

/-! # Higham Chapter 28: the signed two-incidence transfer

This file applies the real-eigenline incidence area formula twice, retaining
the parity of each marked root.  The two absolute Jacobians thereby become
signed characteristic determinants.  Orthogonal block coordinates then
leave the ordered two-Gaussian characteristic-product kernel.
-/

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Frobenius

noncomputable section

private local instance ginibreSignedIncidenceMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi
private local instance ginibreSignedIncidenceMeasureSpaceRSqMat (n : ℕ) :
    MeasureSpace (RSqMat n) := {
  toMeasurableSpace := MeasurableSpace.pi
  volume := realGinibreLebesgueMeasure n }
private local instance ginibreSignedIncidenceSigmaFiniteRSqMat (n : ℕ) :
    SigmaFinite (volume : Measure (RSqMat n)) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

private local instance ginibreSignedIncidenceStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod
private local instance ginibreSignedIncidenceStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

private local instance ginibreSignedIncidenceLebesgueHaar (n : ℕ) :
    (ginibreIncidenceLebesgueMeasure n).IsAddHaarMeasure := by
  unfold ginibreIncidenceLebesgueMeasure
  exact ContinuousLinearEquiv.isAddHaarMeasure_map
    (ginibreCoordinatesContinuousLinearEquiv n).symm
      (volume : Measure (GinibreRawMatrix (n + 1)))

private theorem ginibreIncidenceLebesgueMeasure_eq_signedVolume (n : ℕ) :
    ginibreIncidenceLebesgueMeasure n =
      (volume : Measure (GinibreIncidenceCoordinates n)) := by
  exact ginibreIncidenceLebesgueMeasure_eq_volume n

/-- The signed deflated determinant differs from the incidence derivative
determinant only by the dimension parity. -/
theorem det_ginibreIncidenceDeflatedShift_eq_negOnePow_mul_derivativeDet
    {n : ℕ} (q : GinibreIncidenceCoordinates n) :
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det =
      (-1 : ℝ) ^ n * (ginibreIncidenceDerivativeLinearMap q).det := by
  rw [ginibreIncidenceDerivativeLinearMap_det]
  have hneg : ginibreIncidenceDeflatedBlock q -
      ginibreIncidenceEigenvalue q • (1 : RSqMat n) =
      -(ginibreIncidenceTangentMatrix q) := by
    ext i j
    simp [ginibreIncidenceTangentMatrix]
  rw [hneg, Matrix.det_neg, Fintype.card_fin]

/-- Ordinary coordinate-density bridge for the alternating ordered-pair
observable. -/
theorem integral_ginibreCoordinate_alternatingPair_density_eq_expected
    (n : ℕ) :
    (∫ p : GinibreIncidenceCoordinates n,
      ginibreAlternatingPairCount
          (realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p)) *
        realGinibreDensityReal (n + 1) (ginibreCoordinatesFinMatrix p)
      ∂ginibreIncidenceLebesgueMeasure n) =
      expectedGinibreAlternatingPairCount (n + 1) := by
  let F : GinibreRawMatrix (n + 1) → ℝ := fun A =>
    ginibreAlternatingPairCount (realEigenvalueCount (n + 1) A) *
      realGinibreDensityReal (n + 1) A
  have hmp : MeasurePreserving ginibreCoordinatesFinMatrix
      (ginibreIncidenceLebesgueMeasure n)
      (realGinibreLebesgueMeasure (n + 1)) :=
    ⟨measurable_ginibreCoordinatesFinMatrix,
      ginibreIncidenceLebesgueMeasure_map n⟩
  calc
    (∫ p : GinibreIncidenceCoordinates n,
      ginibreAlternatingPairCount
          (realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p)) *
        realGinibreDensityReal (n + 1) (ginibreCoordinatesFinMatrix p)
      ∂ginibreIncidenceLebesgueMeasure n) =
        ∫ A : RSqMat (n + 1), F A
          ∂realGinibreLebesgueMeasure (n + 1) := by
      exact hmp.integral_comp
        (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.measurableEmbedding F
    _ = ∫ A : RSqMat (n + 1),
          ginibreAlternatingPairCount (realEigenvalueCount (n + 1) A)
          ∂realGinibreMeasure (n + 1) := by
      rw [realGinibreMeasure_eq_withDensity,
        integral_withDensity_eq_integral_toReal_smul]
      · apply integral_congr_ae
        filter_upwards with A
        simp [F, ENNReal.toReal_ofReal
          (le_of_lt (realGinibreDensityReal_pos (n + 1) A))]
        ring
      · exact (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal
      · filter_upwards with A
        exact ENNReal.ofReal_lt_top
    _ = expectedGinibreAlternatingPairCount (n + 1) := rfl

/-- The matrix Gaussian density pulled back to affine block coordinates is
integrable. -/
theorem integrable_ginibreCoordinate_density (n : ℕ) :
    Integrable (fun p : GinibreIncidenceCoordinates n =>
      realGinibreDensityReal (n + 1) (ginibreCoordinatesFinMatrix p))
      (ginibreIncidenceLebesgueMeasure n) := by
  have hmp : MeasurePreserving ginibreCoordinatesFinMatrix
      (ginibreIncidenceLebesgueMeasure n)
      (realGinibreLebesgueMeasure (n + 1)) :=
    ⟨measurable_ginibreCoordinatesFinMatrix,
      ginibreIncidenceLebesgueMeasure_map n⟩
  exact (hmp.integrable_comp_emb
    (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.measurableEmbedding).2
      (integrable_realGinibreDensityReal (n + 1))

/-- Signed outer incidence: the alternating pair count becomes a signed
deflated determinant weighted by the alternating number of roots below the
marked root. -/
theorem integral_ginibreAlternatingPair_eq_signedIncidence
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure]
    (h : GinibreIncidenceCoordinates m → ℝ) (hh : Integrable h μ) :
    (∫ p, ginibreAlternatingPairCount
          (realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)) *
        h p ∂μ) =
      ∫ q,
        (ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
          ginibreAlternatingCount (ginibreIncidenceRootRank q) *
          h (ginibreIncidenceChart q) ∂μ := by
  classical
  let image : Fin (m + 2) → Set (GinibreIncidenceCoordinates m) := fun k =>
    ginibreIncidenceChart '' ginibreIncidenceRankPiece m k
  let c : Fin (m + 2) → ℝ := fun k =>
    (-1 : ℝ) ^ k.val * ginibreAlternatingCount k.val
  let f : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      ginibreAlternatingCount (ginibreIncidenceRootRank q) *
      h (ginibreIncidenceChart q)
  have himageMeas (k : Fin (m + 2)) : MeasurableSet (image k) := by
    exact measurableSet_ginibreIncidenceRankImage m k
  have himageInt (k : Fin (m + 2)) :
      Integrable ((image k).indicator (fun p => c k * h p)) μ :=
    (hh.const_mul (c k)).indicator (himageMeas k)
  have hsourceInt (k : Fin (m + 2)) : IntegrableOn f
      (ginibreIncidenceRankPiece m k) μ := by
    have htarget : IntegrableOn (fun p => c k * h p) (image k) μ :=
      (hh.const_mul (c k)).integrableOn
    have hsource :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        μ (measurableSet_ginibreIncidenceRankPiece m k)
        (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
        (injOn_ginibreIncidenceChart_rankPiece m k)
        (fun p => c k * h p)).1 htarget
    refine hsource.congr_fun ?_
      (measurableSet_ginibreIncidenceRankPiece m k)
    intro q hq
    simp only [smul_eq_mul]
    have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1
    change |(ginibreIncidenceDerivativeLinearMap q).det| *
        (c k * h (ginibreIncidenceChart q)) = f q
    dsimp [c, f]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.2]
    calc
      |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            ginibreAlternatingCount (ginibreIncidenceRootRank q) *
            h (ginibreIncidenceChart q)) =
        ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
          |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
          ginibreAlternatingCount (ginibreIncidenceRootRank q) *
          h (ginibreIncidenceChart q) := by ring
      _ = _ := by rw [hsign]
  have hb : ∀ᵐ p ∂μ, p ∉ ginibreAffineBoundaryEigenpairSet m :=
    measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreAffineBoundaryEigenpairSet_eq_zero m μ)
  have hc : ∀ᵐ p ∂μ,
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ :=
    measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreIncidence_criticalImage_eq_zero m μ)
  calc
    (∫ p, ginibreAlternatingPairCount
          (realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)) *
        h p ∂μ) =
        ∫ p, ∑ k : Fin (m + 2),
          (image k).indicator (fun p => c k * h p) p ∂μ := by
      apply integral_congr_ae
      filter_upwards [hb, hc] with p hbp hcp
      have hcollapse :=
        sum_ginibreIncidenceRankImage_pairPrefix_eq_alternatingPairCount
          p hbp hcp
      dsimp [image, c]
      rw [← hcollapse, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hmem :
          p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m k
      · simp [hmem]
      · simp [hmem]
    _ = ∑ k : Fin (m + 2),
          ∫ p, (image k).indicator (fun p => c k * h p) p ∂μ := by
      exact integral_finset_sum Finset.univ (fun k hk => himageInt k)
    _ = ∑ k : Fin (m + 2),
          ∫ p in image k, c k * h p ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_indicator (himageMeas k)]
    _ = ∑ k : Fin (m + 2),
          ∫ q in ginibreIncidenceRankPiece m k,
            |(ginibreIncidenceDerivativeLinearMap q).det| *
              (c k * h (ginibreIncidenceChart q)) ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (integral_ginibreIncidence_rankPiece_eq_image m μ k
        (fun p => c k * h p)).symm
    _ = ∑ k : Fin (m + 2),
          ∫ q in ginibreIncidenceRankPiece m k, f q ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply setIntegral_congr_fun
        (measurableSet_ginibreIncidenceRankPiece m k)
      intro q hq
      have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1
      change |(ginibreIncidenceDerivativeLinearMap q).det| *
          (c k * h (ginibreIncidenceChart q)) = f q
      dsimp [c, f]
      rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.2]
      calc
        |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
            ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
              ginibreAlternatingCount (ginibreIncidenceRootRank q) *
              h (ginibreIncidenceChart q)) =
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            |(ginibreIncidenceDeflatedBlock q -
              ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
            ginibreAlternatingCount (ginibreIncidenceRootRank q) *
            h (ginibreIncidenceChart q) := by ring
        _ = _ := by rw [hsign]
    _ = ∫ q in ginibreIncidenceRegularSet m, f q ∂μ := by
      rw [← iUnion_ginibreIncidenceRankPiece]
      symm
      rw [integral_iUnion
        (measurableSet_ginibreIncidenceRankPiece m)
        (pairwiseDisjoint_ginibreIncidenceRankPiece m)]
      · rw [tsum_fintype]
      · exact integrableOn_iUnion_of_summable_integral_norm
          hsourceInt ((hasSum_fintype (fun k : Fin (m + 2) =>
            ∫ q in ginibreIncidenceRankPiece m k, ‖f q‖ ∂μ) _).summable)
    _ = ∫ q, f q ∂μ := by
      rw [← integral_indicator
        (measurableSet_ginibreIncidenceRegularSet m)]
      apply integral_congr_ae
      filter_upwards with q
      by_cases hq : q ∈ ginibreIncidenceRegularSet m
      · simp [hq]
      · rw [Set.indicator_of_notMem hq]
        have htan : (ginibreIncidenceTangentMatrix q).det = 0 := by
          simpa [ginibreIncidenceRegularSet] using hq
        have hderiv : (ginibreIncidenceDerivativeLinearMap q).det = 0 := by
          rw [ginibreIncidenceDerivativeLinearMap_det, htan]
        have hdet : (ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det = 0 := by
          rw [det_ginibreIncidenceDeflatedShift_eq_negOnePow_mul_derivativeDet,
            hderiv, mul_zero]
        simp [f, hdet]

/-- Integrability companion to the signed outer-incidence identity. -/
theorem integrable_ginibreSignedIncidence
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure]
    (h : GinibreIncidenceCoordinates m → ℝ) (hh : Integrable h μ) :
    Integrable (fun q : GinibreIncidenceCoordinates m =>
      (ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
        ginibreAlternatingCount (ginibreIncidenceRootRank q) *
        h (ginibreIncidenceChart q)) μ := by
  classical
  let f : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      ginibreAlternatingCount (ginibreIncidenceRootRank q) *
      h (ginibreIncidenceChart q)
  have hsourceInt (k : Fin (m + 2)) : IntegrableOn f
      (ginibreIncidenceRankPiece m k) μ := by
    let c : ℝ := (-1 : ℝ) ^ k.val * ginibreAlternatingCount k.val
    have htarget : IntegrableOn (fun p => c * h p)
        (ginibreIncidenceChart '' ginibreIncidenceRankPiece m k) μ :=
      (hh.const_mul c).integrableOn
    have hsource :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        μ (measurableSet_ginibreIncidenceRankPiece m k)
        (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
        (injOn_ginibreIncidenceChart_rankPiece m k)
        (fun p => c * h p)).1 htarget
    refine hsource.congr_fun ?_
      (measurableSet_ginibreIncidenceRankPiece m k)
    intro q hq
    simp only [smul_eq_mul]
    change |(ginibreIncidenceDerivativeLinearMap q).det| *
        (c * h (ginibreIncidenceChart q)) = f q
    have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1
    dsimp [c, f]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.2]
    calc
      |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            ginibreAlternatingCount (ginibreIncidenceRootRank q) *
            h (ginibreIncidenceChart q)) =
        ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
          |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
          ginibreAlternatingCount (ginibreIncidenceRootRank q) *
          h (ginibreIncidenceChart q) := by ring
      _ = _ := by rw [hsign]
  have hreg : IntegrableOn f (ginibreIncidenceRegularSet m) μ := by
    rw [← iUnion_ginibreIncidenceRankPiece]
    exact integrableOn_iUnion_of_summable_integral_norm
      hsourceInt ((hasSum_fintype (fun k : Fin (m + 2) =>
        ∫ q in ginibreIncidenceRankPiece m k, ‖f q‖ ∂μ) _).summable)
  have hcomp : IntegrableOn f (ginibreIncidenceRegularSet m)ᶜ μ := by
    have hz : IntegrableOn (fun _q : GinibreIncidenceCoordinates m => (0 : ℝ))
        (ginibreIncidenceRegularSet m)ᶜ μ :=
      (integrable_zero (GinibreIncidenceCoordinates m) ℝ μ).integrableOn
    refine hz.congr_fun ?_
      (measurableSet_ginibreIncidenceRegularSet m).compl
    intro q hq
    have htan : (ginibreIncidenceTangentMatrix q).det = 0 := by
      simpa [ginibreIncidenceRegularSet] using hq
    have hderiv : (ginibreIncidenceDerivativeLinearMap q).det = 0 := by
      rw [ginibreIncidenceDerivativeLinearMap_det, htan]
    have hdet : (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det = 0 := by
      rw [det_ginibreIncidenceDeflatedShift_eq_negOnePow_mul_derivativeDet,
        hderiv, mul_zero]
    simp [f, hdet]
  have hall := hreg.union hcomp
  simpa only [union_compl_self, integrableOn_univ] using hall

/-! ## Product-density and nuisance-coordinate bookkeeping -/

/-- The one-root signed moment left after the first incidence transfer. -/
def ginibreSignedOneRootMoment (n : ℕ) : ℝ :=
  ∫ p : RSqMat n × ℝ,
    (p.1 - p.2 • (1 : RSqMat n)).det *
      ginibreAlternatingCount (realEigenvalueBelowCount p)
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

/-- Characteristic-polynomial form of the alternating number of roots below
the marked scalar. -/
def ginibreAlternatingBelowCharpoly (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  ginibreAlternatingCount ((P.roots.filter fun z => z < x).card)

theorem ginibreAlternatingBelowCharpoly_charpoly (n : ℕ)
    (A : RSqMat n) (x : ℝ) :
    ginibreAlternatingBelowCharpoly (Matrix.charpoly (Matrix.of A)) x =
      ginibreAlternatingCount (realEigenvalueBelowCount (A, x)) := rfl

/-- Reorder `((C,z),x)` as `(z,(C,x))`. -/
def ginibreNuisanceReorder (n : ℕ) :
    GinibreIncidenceNuisance n ≃ᵐ
      (Fin n → ℝ) × (RSqMat n × ℝ) where
  toEquiv :=
    { toFun := fun v => (v.1.2, (v.1.1, v.2))
      invFun := fun p => ((p.2.1, p.1), p.2.2)
      left_inv := by intro v; rfl
      right_inv := by intro p; rfl }
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

@[simp] theorem ginibreNuisanceReorder_apply (n : ℕ)
    (v : GinibreIncidenceNuisance n) :
    ginibreNuisanceReorder n v = (v.1.2, (v.1.1, v.2)) := rfl

/-- The nuisance reordering preserves the canonical product Lebesgue
measure. -/
theorem measurePreserving_ginibreNuisanceReorder (n : ℕ) :
    MeasurePreserving (ginibreNuisanceReorder n)
      (volume : Measure (GinibreIncidenceNuisance n))
      ((volume : Measure (Fin n → ℝ)).prod
        ((volume : Measure (RSqMat n)).prod volume)) := by
  let A := RSqMat n
  let B := Fin n → ℝ
  let C := ℝ
  have hswap : MeasurePreserving
      (fun p : (A × B) × C => ((p.1.2, p.1.1), p.2)) :=
    (Measure.measurePreserving_swap
      (μ := (volume : Measure A)) (ν := (volume : Measure B))).prod
        (MeasurePreserving.id (volume : Measure C))
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (B × A) × C ≃ᵐ B × (A × C)) :=
    volume_preserving_prodAssoc
  have h := hassoc.comp hswap
  simpa [A, B, C, ginibreNuisanceReorder, Function.comp_def] using h

/-- Eliminating the auxiliary bottom row turns the nuisance-coordinate
integral into the signed one-root moment. -/
theorem integral_ginibreSignedNuisance_eq_oneRootMoment (n : ℕ) :
    (∫ v : GinibreIncidenceNuisance n,
      ((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det *
        ginibreAlternatingCount
          (realEigenvalueBelowCount
            ((show RSqMat n from v.1.1), v.2)) *
        realGinibreDensityReal n (show RSqMat n from v.1.1) *
        (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
        gaussianPDFReal 0 1 v.2) =
      ginibreSignedOneRootMoment n := by
  let Z : (Fin n → ℝ) → ℝ := fun z =>
    ∏ i : Fin n, gaussianPDFReal 0 1 (z i)
  let G : (RSqMat n × ℝ) → ℝ := fun p =>
    (p.1 - p.2 • (1 : RSqMat n)).det *
      ginibreAlternatingCount (realEigenvalueBelowCount p) *
      realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2
  have hmp := measurePreserving_ginibreNuisanceReorder n
  calc
    (∫ v : GinibreIncidenceNuisance n,
      ((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det *
        ginibreAlternatingCount
          (realEigenvalueBelowCount
            ((show RSqMat n from v.1.1), v.2)) *
        realGinibreDensityReal n (show RSqMat n from v.1.1) *
        (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
        gaussianPDFReal 0 1 v.2) =
        ∫ p : (Fin n → ℝ) × (RSqMat n × ℝ), Z p.1 * G p.2 := by
      have h := hmp.integral_comp
        (ginibreNuisanceReorder n).measurableEmbedding
        (fun p : (Fin n → ℝ) × (RSqMat n × ℝ) => Z p.1 * G p.2)
      calc
        (∫ v : GinibreIncidenceNuisance n,
          ((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det *
            ginibreAlternatingCount
              (realEigenvalueBelowCount
                ((show RSqMat n from v.1.1), v.2)) *
            realGinibreDensityReal n (show RSqMat n from v.1.1) *
            (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
            gaussianPDFReal 0 1 v.2) =
            ∫ v : GinibreIncidenceNuisance n,
              Z v.1.2 * G (v.1.1, v.2) := by
          apply integral_congr_ae
          filter_upwards with v
          dsimp [Z, G]
          ac_rfl
        _ = ∫ p : (Fin n → ℝ) × (RSqMat n × ℝ), Z p.1 * G p.2 := h
    _ = (∫ z : Fin n → ℝ, Z z) *
          ∫ p : RSqMat n × ℝ, G p := by
      exact integral_prod_mul Z G
    _ = ∫ p : RSqMat n × ℝ, G p := by
      rw [show (∫ z : Fin n → ℝ, Z z) = 1 by
        simpa [Z] using integral_standardGaussianVectorDensity_eq_one n]
      simp
    _ = ginibreSignedOneRootMoment n := by
      unfold ginibreSignedOneRootMoment
      rw [integral_realGinibre_prod_gaussian_eq_jointDensity]
      apply integral_congr_ae
      filter_upwards with p
      simp [G]
      ring

/-! ## The first signed incidence transfer -/

/-- Applying the signed incidence formula once converts the alternating pair
expectation in dimension `n+1` into the signed one-root moment in dimension
`n`, with the exact Corollary 3.1 normalization. -/
theorem expectedGinibreAlternatingPairCount_succ_eq_factor_mul_oneRootMoment
    (n : ℕ) :
    expectedGinibreAlternatingPairCount (n + 1) =
      ginibreCorollary31Factor (n + 1) * ginibreSignedOneRootMoment n := by
  let d : GinibreIncidenceCoordinates n → ℝ := fun p =>
    realGinibreDensityReal (n + 1) (ginibreCoordinatesFinMatrix p)
  let H : Polynomial ℝ → ℝ → ℝ := ginibreAlternatingBelowCharpoly
  let Φ : GinibreIncidenceCoordinates n → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det *
      H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock q)))
        (ginibreIncidenceEigenvalue q) *
      d (ginibreIncidenceChart q)
  have hd : Integrable d (ginibreIncidenceLebesgueMeasure n) := by
    simpa [d] using integrable_ginibreCoordinate_density n
  have harea := integral_ginibreAlternatingPair_eq_signedIncidence
    n (ginibreIncidenceLebesgueMeasure n) d hd
  have hbase : expectedGinibreAlternatingPairCount (n + 1) =
      ∫ q : GinibreIncidenceCoordinates n, Φ q
        ∂ginibreIncidenceLebesgueMeasure n := by
    calc
      expectedGinibreAlternatingPairCount (n + 1) =
          ∫ p : GinibreIncidenceCoordinates n,
            ginibreAlternatingPairCount
                (realEigenvalueCount (n + 1)
                  (ginibreCoordinatesFinMatrix p)) * d p
            ∂ginibreIncidenceLebesgueMeasure n := by
        symm
        simpa [d] using
          integral_ginibreCoordinate_alternatingPair_density_eq_expected n
      _ = ∫ q : GinibreIncidenceCoordinates n,
          (ginibreIncidenceDeflatedBlock q -
              ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det *
            ginibreAlternatingCount (ginibreIncidenceRootRank q) *
            d (ginibreIncidenceChart q)
          ∂ginibreIncidenceLebesgueMeasure n := harea
      _ = ∫ q : GinibreIncidenceCoordinates n, Φ q
          ∂ginibreIncidenceLebesgueMeasure n := by
        apply integral_congr_ae
        filter_upwards with q
        rw [ginibreIncidenceRootRank_eq_deflatedBelowCount]
        rfl
  have hΦ : Integrable Φ (ginibreIncidenceLebesgueMeasure n) := by
    have h := integrable_ginibreSignedIncidence
      n (ginibreIncidenceLebesgueMeasure n) d hd
    apply h.congr
    filter_upwards with q
    rw [ginibreIncidenceRootRank_eq_deflatedBelowCount]
    rfl
  have hΦvol : Integrable Φ (volume : Measure (GinibreIncidenceCoordinates n)) := by
    rw [← ginibreIncidenceLebesgueMeasure_eq_signedVolume]
    exact hΦ
  let J : ℝ := ∫ v : GinibreIncidenceNuisance n,
    ((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det *
      ginibreAlternatingCount
        (realEigenvalueBelowCount
          ((show RSqMat n from v.1.1), v.2)) *
      realGinibreDensityReal n (show RSqMat n from v.1.1) *
      (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
      gaussianPDFReal 0 1 v.2
  let W : (Fin n → ℝ) → ℝ := fun y =>
    (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  calc
    expectedGinibreAlternatingPairCount (n + 1) =
        ∫ q : GinibreIncidenceCoordinates n, Φ q
          ∂ginibreIncidenceLebesgueMeasure n := hbase
    _ = ∫ q : GinibreIncidenceCoordinates n, Φ q := by
      rw [ginibreIncidenceLebesgueMeasure_eq_signedVolume]
    _ = ∫ y : Fin n → ℝ,
          ∫ u : GinibreIncidenceNuisance n, Φ (u, y) := by
      exact integral_prod_symm Φ hΦvol
    _ = ∫ y : Fin n → ℝ,
          W y * (gaussianPDFReal 0 1 0) ^ n * J := by
      apply integral_congr_ae
      filter_upwards with y
      obtain ⟨Q, hQ, hcol⟩ := exists_orthogonal_lastColumn_affine n y
      have hfiber := integral_ginibreSignedFixedFiber_of_orthogonal
        n y Q hQ hcol H
      simpa [Φ, d, H, W, J,
        ginibreAlternatingBelowCharpoly_charpoly] using hfiber
    _ = (∫ y : Fin n → ℝ, W y) *
          ((gaussianPDFReal 0 1 0) ^ n * J) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ginibreCorollary31Factor (n + 1) * J := by
      have hnorm := gaussianZeroPow_mul_integral_ginibreProjectiveWeight n
      change (∫ y : Fin n → ℝ, W y) *
          ((gaussianPDFReal 0 1 0) ^ n * J) = _
      have hW : (∫ y : Fin n → ℝ, W y) =
          ∫ y : Fin n → ℝ,
            (1 + ∑ i : Fin n, y i ^ 2) ^
              (-(((n : ℝ) + 1) / 2)) := rfl
      rw [hW]
      rw [show ginibreCorollary31Factor (n + 1) =
          (gaussianPDFReal 0 1 0) ^ n *
            (∫ y : Fin n → ℝ,
              (1 + ∑ i : Fin n, y i ^ 2) ^
                (-(((n : ℝ) + 1) / 2))) by exact hnorm.symm]
      ring
    _ = ginibreCorollary31Factor (n + 1) *
          ginibreSignedOneRootMoment n := by
      rw [show J = ginibreSignedOneRootMoment n by
        simpa [J] using integral_ginibreSignedNuisance_eq_oneRootMoment n]

/-! ## The second signed incidence transfer -/

/-- The signed two-root slice at a fixed external spectral parameter `x`. -/
def ginibreSignedTwoRootSlice (m : ℕ) (x : ℝ) : ℝ :=
  ∫ p : RSqMat m × ℝ,
    if p.2 < x then
      (p.2 - x) *
        (p.1 - p.2 • (1 : RSqMat m)).det *
        (p.1 - x • (1 : RSqMat m)).det
    else 0
    ∂(realGinibreMeasure m).prod (gaussianReal 0 1)

/-- Polynomial weight which simultaneously imposes `u < x` and evaluates
the full shifted determinant after the second incidence factorization. -/
def ginibreTruncatedExternalShiftWeight (m : ℕ) (x : ℝ)
    (P : Polynomial ℝ) (u : ℝ) : ℝ :=
  if u < x then (u - x) * ((-1 : ℝ) ^ m * P.eval x) else 0

theorem ginibreTruncatedExternalShiftWeight_charpoly
    (m : ℕ) (x : ℝ) (A : RSqMat m) (u : ℝ) :
    ginibreTruncatedExternalShiftWeight m x
        (Matrix.charpoly (Matrix.of A)) u =
      if u < x then
        (u - x) * (A - x • (1 : RSqMat m)).det else 0 := by
  unfold ginibreTruncatedExternalShiftWeight
  by_cases hux : u < x
  · rw [if_pos hux, if_pos hux,
      det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval]
  · rw [if_neg hux, if_neg hux]

theorem ginibreTruncatedExternalShiftWeight_incidence
    {m : ℕ} (q : GinibreIncidenceCoordinates m) (x : ℝ) :
    ginibreTruncatedExternalShiftWeight m x
        (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock q)))
        (ginibreIncidenceEigenvalue q) =
      if ginibreIncidenceEigenvalue q < x then
        ((show RSqMat (m + 1) from
          ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)) -
            x • (1 : RSqMat (m + 1))).det
      else 0 := by
  rw [ginibreTruncatedExternalShiftWeight_charpoly]
  by_cases hux : ginibreIncidenceEigenvalue q < x
  · rw [if_pos hux, if_pos hux,
      det_ginibreIncidenceFull_sub_externalShift]
  · rw [if_neg hux, if_neg hux]

/-- Matrix-only coordinate-density bridge for an arbitrary observable. -/
theorem integral_realGinibre_eq_incidenceCoordinateDensity
    (n : ℕ) (g : RSqMat (n + 1) → ℝ) :
    (∫ A : RSqMat (n + 1), g A ∂realGinibreMeasure (n + 1)) =
      ∫ p : GinibreIncidenceCoordinates n,
        realGinibreDensityReal (n + 1) (ginibreCoordinatesFinMatrix p) *
          g (ginibreCoordinatesFinMatrix p)
        ∂ginibreIncidenceLebesgueMeasure n := by
  have hmp : MeasurePreserving ginibreCoordinatesFinMatrix
      (ginibreIncidenceLebesgueMeasure n)
      (realGinibreLebesgueMeasure (n + 1)) :=
    ⟨measurable_ginibreCoordinatesFinMatrix,
      ginibreIncidenceLebesgueMeasure_map n⟩
  calc
    (∫ A : RSqMat (n + 1), g A ∂realGinibreMeasure (n + 1)) =
        ∫ A : RSqMat (n + 1),
          realGinibreDensityReal (n + 1) A * g A
          ∂realGinibreLebesgueMeasure (n + 1) := by
      rw [realGinibreMeasure_eq_withDensity,
        integral_withDensity_eq_integral_toReal_smul]
      · apply integral_congr_ae
        filter_upwards with A
        simp [ENNReal.toReal_ofReal
          (le_of_lt (realGinibreDensityReal_pos (n + 1) A))]
      · exact (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal
      · filter_upwards with A
        exact ENNReal.ofReal_lt_top
    _ = ∫ p : GinibreIncidenceCoordinates n,
          realGinibreDensityReal (n + 1) (ginibreCoordinatesFinMatrix p) *
            g (ginibreCoordinatesFinMatrix p)
          ∂ginibreIncidenceLebesgueMeasure n := by
      symm
      exact hmp.integral_comp
        (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.measurableEmbedding
        (fun A => realGinibreDensityReal (n + 1) A * g A)

/-- Integrability form of the matrix coordinate-density bridge. -/
theorem integrable_incidenceCoordinateDensity_of_integrable_realGinibre
    (n : ℕ) {g : RSqMat (n + 1) → ℝ}
    (hg : Integrable g (realGinibreMeasure (n + 1))) :
    Integrable (fun p : GinibreIncidenceCoordinates n =>
      realGinibreDensityReal (n + 1) (ginibreCoordinatesFinMatrix p) *
        g (ginibreCoordinatesFinMatrix p))
      (ginibreIncidenceLebesgueMeasure n) := by
  have hLeb : Integrable (fun A : RSqMat (n + 1) =>
      realGinibreDensityReal (n + 1) A * g A)
      (realGinibreLebesgueMeasure (n + 1)) := by
    rw [realGinibreMeasure_eq_withDensity] at hg
    have h := (integrable_withDensity_iff
      (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal
      (ae_of_all _ fun A => ENNReal.ofReal_lt_top)).1 hg
    apply h.congr
    filter_upwards with A
    simp [ENNReal.toReal_ofReal
      (le_of_lt (realGinibreDensityReal_pos (n + 1) A))]
    ring
  have hmp : MeasurePreserving ginibreCoordinatesFinMatrix
      (ginibreIncidenceLebesgueMeasure n)
      (realGinibreLebesgueMeasure (n + 1)) :=
    ⟨measurable_ginibreCoordinatesFinMatrix,
      ginibreIncidenceLebesgueMeasure_map n⟩
  exact (hmp.integrable_comp_emb
    (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.measurableEmbedding).2
      hLeb

/-- Eliminating the auxiliary bottom row after the second fixed-fiber
calculation gives the signed two-root slice. -/
theorem integral_ginibreSignedTwoRootNuisance_eq_slice
    (m : ℕ) (x : ℝ) :
    (∫ v : GinibreIncidenceNuisance m,
      ((show RSqMat m from v.1.1) - v.2 • (1 : RSqMat m)).det *
        ginibreTruncatedExternalShiftWeight m x
          (Matrix.charpoly (Matrix.of (show RSqMat m from v.1.1))) v.2 *
        realGinibreDensityReal m (show RSqMat m from v.1.1) *
        (∏ i : Fin m, gaussianPDFReal 0 1 (v.1.2 i)) *
        gaussianPDFReal 0 1 v.2) =
      ginibreSignedTwoRootSlice m x := by
  let Z : (Fin m → ℝ) → ℝ := fun z =>
    ∏ i : Fin m, gaussianPDFReal 0 1 (z i)
  let G : (RSqMat m × ℝ) → ℝ := fun p =>
    (p.1 - p.2 • (1 : RSqMat m)).det *
      ginibreTruncatedExternalShiftWeight m x
        (Matrix.charpoly (Matrix.of p.1)) p.2 *
      realGinibreDensityReal m p.1 * gaussianPDFReal 0 1 p.2
  have hmp := measurePreserving_ginibreNuisanceReorder m
  calc
    (∫ v : GinibreIncidenceNuisance m,
      ((show RSqMat m from v.1.1) - v.2 • (1 : RSqMat m)).det *
        ginibreTruncatedExternalShiftWeight m x
          (Matrix.charpoly (Matrix.of (show RSqMat m from v.1.1))) v.2 *
        realGinibreDensityReal m (show RSqMat m from v.1.1) *
        (∏ i : Fin m, gaussianPDFReal 0 1 (v.1.2 i)) *
        gaussianPDFReal 0 1 v.2) =
        ∫ p : (Fin m → ℝ) × (RSqMat m × ℝ), Z p.1 * G p.2 := by
      have h := hmp.integral_comp
        (ginibreNuisanceReorder m).measurableEmbedding
        (fun p : (Fin m → ℝ) × (RSqMat m × ℝ) => Z p.1 * G p.2)
      calc
        (∫ v : GinibreIncidenceNuisance m,
          ((show RSqMat m from v.1.1) - v.2 • (1 : RSqMat m)).det *
            ginibreTruncatedExternalShiftWeight m x
              (Matrix.charpoly (Matrix.of
                (show RSqMat m from v.1.1))) v.2 *
            realGinibreDensityReal m (show RSqMat m from v.1.1) *
            (∏ i : Fin m, gaussianPDFReal 0 1 (v.1.2 i)) *
            gaussianPDFReal 0 1 v.2) =
            ∫ v : GinibreIncidenceNuisance m,
              Z v.1.2 * G (v.1.1, v.2) := by
          apply integral_congr_ae
          filter_upwards with v
          dsimp [Z, G]
          ac_rfl
        _ = ∫ p : (Fin m → ℝ) × (RSqMat m × ℝ), Z p.1 * G p.2 := h
    _ = (∫ z : Fin m → ℝ, Z z) *
          ∫ p : RSqMat m × ℝ, G p := by
      exact integral_prod_mul Z G
    _ = ∫ p : RSqMat m × ℝ, G p := by
      rw [show (∫ z : Fin m → ℝ, Z z) = 1 by
        simpa [Z] using integral_standardGaussianVectorDensity_eq_one m]
      simp
    _ = ginibreSignedTwoRootSlice m x := by
      unfold ginibreSignedTwoRootSlice
      rw [integral_realGinibre_prod_gaussian_eq_jointDensity]
      apply integral_congr_ae
      filter_upwards with p
      dsimp [G]
      rw [ginibreTruncatedExternalShiftWeight_charpoly]
      by_cases hpx : p.2 < x
      · simp only [if_pos hpx]
        ring_nf
      · simp only [if_neg hpx]
        simp

/-- Conditional second incidence transfer at a fixed external parameter.
The sole hypothesis is the natural integrability of the shifted determinant
under the `(m+1)`-dimensional real-Ginibre law. -/
theorem integral_realGinibre_det_mul_alternatingBelow_eq_factor_mul_slice
    (m : ℕ) (x : ℝ)
    (hx : Integrable (fun A : RSqMat (m + 1) =>
      (A - x • (1 : RSqMat (m + 1))).det)
      (realGinibreMeasure (m + 1))) :
    (∫ A : RSqMat (m + 1),
      (A - x • (1 : RSqMat (m + 1))).det *
        ginibreAlternatingCount (realEigenvalueBelowCount (A, x))
      ∂realGinibreMeasure (m + 1)) =
      ginibreCorollary31Factor (m + 1) *
        ginibreSignedTwoRootSlice m x := by
  let g : RSqMat (m + 1) → ℝ := fun A =>
    (A - x • (1 : RSqMat (m + 1))).det
  let d : GinibreIncidenceCoordinates m → ℝ := fun p =>
    realGinibreDensityReal (m + 1) (ginibreCoordinatesFinMatrix p)
  let h : GinibreIncidenceCoordinates m → ℝ := fun p =>
    d p * g (ginibreCoordinatesFinMatrix p)
  let H : Polynomial ℝ → ℝ → ℝ :=
    ginibreTruncatedExternalShiftWeight m x
  let Ψ : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock q)))
        (ginibreIncidenceEigenvalue q) *
      d (ginibreIncidenceChart q)
  have hh : Integrable h (ginibreIncidenceLebesgueMeasure m) := by
    have hcoord :=
      integrable_incidenceCoordinateDensity_of_integrable_realGinibre m hx
    simpa [h, d, g] using hcoord
  have htrunc := integral_ginibreAlternatingBelow_eq_signedIncidenceBelow
    m (ginibreIncidenceLebesgueMeasure m) x h hh
  let below : Set (GinibreIncidenceCoordinates m) :=
    {q | ginibreIncidenceEigenvalue q < x}
  let f : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      h (ginibreIncidenceChart q)
  have hbelow : MeasurableSet below :=
    measurableSet_lt measurable_ginibreIncidenceEigenvalue measurable_const
  have hΨpoint (q : GinibreIncidenceCoordinates m) :
      Ψ q = below.indicator f q := by
    dsimp [Ψ, H]
    rw [ginibreTruncatedExternalShiftWeight_incidence]
    dsimp [below]
    by_cases hqx : ginibreIncidenceEigenvalue q < x
    · have hmem : q ∈ {q : GinibreIncidenceCoordinates m |
          ginibreIncidenceEigenvalue q < x} := hqx
      rw [Set.indicator_of_mem hmem, if_pos hqx]
      dsimp [below, f, h, g, d]
      ring
    · have hnot : q ∉ {q : GinibreIncidenceCoordinates m |
          ginibreIncidenceEigenvalue q < x} := hqx
      rw [Set.indicator_of_notMem hnot, if_neg hqx]
      simp
  have hΨ : Integrable Ψ (ginibreIncidenceLebesgueMeasure m) := by
    have hfOn := integrableOn_ginibreSignedIncidenceBelow
      m (ginibreIncidenceLebesgueMeasure m) x h hh
    have hf : Integrable (below.indicator f)
        (ginibreIncidenceLebesgueMeasure m) := by
      exact hfOn.integrable_indicator hbelow
    exact hf.congr (ae_of_all _ fun q => (hΨpoint q).symm)
  have hbase :
      (∫ A : RSqMat (m + 1),
        (A - x • (1 : RSqMat (m + 1))).det *
          ginibreAlternatingCount (realEigenvalueBelowCount (A, x))
        ∂realGinibreMeasure (m + 1)) =
        ∫ q : GinibreIncidenceCoordinates m, Ψ q
          ∂ginibreIncidenceLebesgueMeasure m := by
    calc
      (∫ A : RSqMat (m + 1),
        (A - x • (1 : RSqMat (m + 1))).det *
          ginibreAlternatingCount (realEigenvalueBelowCount (A, x))
        ∂realGinibreMeasure (m + 1)) =
          ∫ p : GinibreIncidenceCoordinates m,
            d p *
              (g (ginibreCoordinatesFinMatrix p) *
                ginibreAlternatingCount
                  (realEigenvalueBelowCount
                    (ginibreCoordinatesFinMatrix p, x)))
            ∂ginibreIncidenceLebesgueMeasure m := by
        simpa [d, g] using integral_realGinibre_eq_incidenceCoordinateDensity
          m (fun A =>
            (A - x • (1 : RSqMat (m + 1))).det *
              ginibreAlternatingCount (realEigenvalueBelowCount (A, x)))
      _ = ∫ p : GinibreIncidenceCoordinates m,
            ginibreAlternatingCount
                (realEigenvalueBelowCount
                  (ginibreCoordinatesFinMatrix p, x)) * h p
            ∂ginibreIncidenceLebesgueMeasure m := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [h]
        ring
      _ = ∫ q in below, f q
            ∂ginibreIncidenceLebesgueMeasure m := by
        simpa [below, f] using htrunc
      _ = ∫ q : GinibreIncidenceCoordinates m, Ψ q
            ∂ginibreIncidenceLebesgueMeasure m := by
        rw [← integral_indicator hbelow]
        apply integral_congr_ae
        filter_upwards with q
        exact (hΨpoint q).symm
  have hΨvol : Integrable Ψ (volume : Measure (GinibreIncidenceCoordinates m)) := by
    rw [← ginibreIncidenceLebesgueMeasure_eq_signedVolume]
    exact hΨ
  let J : ℝ := ∫ v : GinibreIncidenceNuisance m,
    ((show RSqMat m from v.1.1) - v.2 • (1 : RSqMat m)).det *
      H (Matrix.charpoly (Matrix.of (show RSqMat m from v.1.1))) v.2 *
      realGinibreDensityReal m (show RSqMat m from v.1.1) *
      (∏ i : Fin m, gaussianPDFReal 0 1 (v.1.2 i)) *
      gaussianPDFReal 0 1 v.2
  let W : (Fin m → ℝ) → ℝ := fun y =>
    (1 + ∑ i : Fin m, y i ^ 2) ^ (-(((m : ℝ) + 1) / 2))
  calc
    (∫ A : RSqMat (m + 1),
      (A - x • (1 : RSqMat (m + 1))).det *
        ginibreAlternatingCount (realEigenvalueBelowCount (A, x))
      ∂realGinibreMeasure (m + 1)) =
        ∫ q : GinibreIncidenceCoordinates m, Ψ q
          ∂ginibreIncidenceLebesgueMeasure m := hbase
    _ = ∫ q : GinibreIncidenceCoordinates m, Ψ q := by
      rw [ginibreIncidenceLebesgueMeasure_eq_signedVolume]
    _ = ∫ y : Fin m → ℝ,
          ∫ u : GinibreIncidenceNuisance m, Ψ (u, y) := by
      exact integral_prod_symm Ψ hΨvol
    _ = ∫ y : Fin m → ℝ,
          W y * (gaussianPDFReal 0 1 0) ^ m * J := by
      apply integral_congr_ae
      filter_upwards with y
      obtain ⟨Q, hQ, hcol⟩ := exists_orthogonal_lastColumn_affine m y
      have hfiber := integral_ginibreSignedFixedFiber_of_orthogonal
        m y Q hQ hcol H
      simpa [Ψ, d, H, W, J] using hfiber
    _ = (∫ y : Fin m → ℝ, W y) *
          ((gaussianPDFReal 0 1 0) ^ m * J) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ginibreCorollary31Factor (m + 1) * J := by
      have hnorm := gaussianZeroPow_mul_integral_ginibreProjectiveWeight m
      change (∫ y : Fin m → ℝ, W y) *
          ((gaussianPDFReal 0 1 0) ^ m * J) = _
      have hW : (∫ y : Fin m → ℝ, W y) =
          ∫ y : Fin m → ℝ,
            (1 + ∑ i : Fin m, y i ^ 2) ^
              (-(((m : ℝ) + 1) / 2)) := rfl
      rw [hW]
      rw [show ginibreCorollary31Factor (m + 1) =
          (gaussianPDFReal 0 1 0) ^ m *
            (∫ y : Fin m → ℝ,
              (1 + ∑ i : Fin m, y i ^ 2) ^
                (-(((m : ℝ) + 1) / 2))) by exact hnorm.symm]
      ring
    _ = ginibreCorollary31Factor (m + 1) *
          ginibreSignedTwoRootSlice m x := by
      rw [show J = ginibreSignedTwoRootSlice m x by
        simpa [J, H] using
          integral_ginibreSignedTwoRootNuisance_eq_slice m x]

end

end NumStability
