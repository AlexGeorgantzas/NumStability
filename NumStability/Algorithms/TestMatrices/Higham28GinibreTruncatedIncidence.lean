/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRankTransfer

/-! # Higham Chapter 28: truncated signed incidence

This file applies the signed eigenline-incidence formula only to marked real
roots below a fixed external spectral threshold.  It is the inner incidence
step in the two-root real-Ginibre calculation.
-/

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Frobenius

noncomputable section

private local instance ginibreTruncatedMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi
private local instance ginibreTruncatedMeasureSpaceRSqMat (n : ℕ) :
    MeasureSpace (RSqMat n) := {
  toMeasurableSpace := MeasurableSpace.pi
  volume := realGinibreLebesgueMeasure n }
private local instance ginibreTruncatedStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod
private local instance ginibreTruncatedStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

/-- The image of a truncated regular rank sheet is measurable. -/
theorem measurableSet_ginibreIncidenceRankPieceBelow_image
    (m : ℕ) (k : Fin (m + 2)) (x : ℝ) :
    MeasurableSet (ginibreIncidenceChart ''
      ginibreIncidenceRankPieceBelow m k x) :=
  (measurableSet_ginibreIncidenceRankPieceBelow m k x).image_of_measurable_injOn
    measurable_ginibreIncidenceChart
    ((injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left)

/-- Truncated rank sheets partition the regular incidence set below the
external threshold. -/
theorem iUnion_ginibreIncidenceRankPieceBelow (m : ℕ) (x : ℝ) :
    (⋃ k : Fin (m + 2), ginibreIncidenceRankPieceBelow m k x) =
      ginibreIncidenceRegularSet m ∩
        {q | ginibreIncidenceEigenvalue q < x} := by
  ext q
  constructor
  · intro hq
    rcases Set.mem_iUnion.1 hq with ⟨k, hk⟩
    exact ⟨hk.1.1, hk.2⟩
  · rintro ⟨hreg, hlt⟩
    rw [← iUnion_ginibreIncidenceRankPiece] at hreg
    rcases Set.mem_iUnion.1 hreg with ⟨k, hk⟩
    exact Set.mem_iUnion.2 ⟨k, ⟨hk, hlt⟩⟩

/-- Truncated rank sheets remain pairwise disjoint. -/
theorem pairwiseDisjoint_ginibreIncidenceRankPieceBelow (m : ℕ) (x : ℝ) :
    Pairwise (fun i j : Fin (m + 2) =>
      Disjoint (ginibreIncidenceRankPieceBelow m i x)
        (ginibreIncidenceRankPieceBelow m j x)) := by
  intro i j hij
  exact (pairwiseDisjoint_ginibreIncidenceRankPiece m hij).mono
    inter_subset_left inter_subset_left

/-- A signed truncated incidence transfer.  The alternating number of real
roots below `x` becomes the signed deflated determinant, integrated over
incidence points whose marked root lies below `x`. -/
theorem integral_ginibreAlternatingBelow_eq_signedIncidenceBelow
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (x : ℝ)
    (h : GinibreIncidenceCoordinates m → ℝ) (hh : Integrable h μ) :
    (∫ p,
      ginibreAlternatingCount
          (realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x)) *
        h p ∂μ) =
      ∫ q in {q | ginibreIncidenceEigenvalue q < x},
        (ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
          h (ginibreIncidenceChart q) ∂μ := by
  classical
  let image : Fin (m + 2) → Set (GinibreIncidenceCoordinates m) := fun k =>
    ginibreIncidenceChart '' ginibreIncidenceRankPieceBelow m k x
  let c : Fin (m + 2) → ℝ := fun k => (-1 : ℝ) ^ k.val
  let f : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      h (ginibreIncidenceChart q)
  have himageMeas (k : Fin (m + 2)) : MeasurableSet (image k) := by
    exact measurableSet_ginibreIncidenceRankPieceBelow_image m k x
  have himageInt (k : Fin (m + 2)) :
      Integrable ((image k).indicator (fun p => c k * h p)) μ :=
    (hh.const_mul (c k)).indicator (himageMeas k)
  have hsourceInt (k : Fin (m + 2)) : IntegrableOn f
      (ginibreIncidenceRankPieceBelow m k x) μ := by
    have htarget : IntegrableOn (fun p => c k * h p) (image k) μ :=
      (hh.const_mul (c k)).integrableOn
    have hsource :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        μ (measurableSet_ginibreIncidenceRankPieceBelow m k x)
        (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
        ((injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left)
        (fun p => c k * h p)).1 htarget
    refine hsource.congr_fun ?_
      (measurableSet_ginibreIncidenceRankPieceBelow m k x)
    intro q hq
    simp only [smul_eq_mul]
    change |(ginibreIncidenceDerivativeLinearMap q).det| *
        (c k * h (ginibreIncidenceChart q)) = f q
    have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1.1
    dsimp [c, f]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.1.2]
    calc
      |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            h (ginibreIncidenceChart q)) =
        ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
          |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
          h (ginibreIncidenceChart q) := by ring
      _ = _ := by rw [hsign]
  have hb : ∀ᵐ p ∂μ, p ∉ ginibreAffineBoundaryEigenpairSet m :=
    measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreAffineBoundaryEigenpairSet_eq_zero m μ)
  have hc : ∀ᵐ p ∂μ,
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ :=
    measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreIncidence_criticalImage_eq_zero m μ)
  have hbelowMeas : MeasurableSet
      {q : GinibreIncidenceCoordinates m | ginibreIncidenceEigenvalue q < x} :=
    measurableSet_lt measurable_ginibreIncidenceEigenvalue measurable_const
  calc
    (∫ p,
      ginibreAlternatingCount
          (realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x)) *
        h p ∂μ) =
        ∫ p, ∑ k : Fin (m + 2),
          (image k).indicator (fun p => c k * h p) p ∂μ := by
      apply integral_congr_ae
      filter_upwards [hb, hc] with p hbp hcp
      have hcollapse :=
        sum_ginibreIncidenceRankPieceBelow_image_sign_eq_alternatingCount
          p hbp hcp x
      dsimp [image, c]
      rw [← hcollapse, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hmem : p ∈ ginibreIncidenceChart ''
          ginibreIncidenceRankPieceBelow m k x
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
          ∫ q in ginibreIncidenceRankPieceBelow m k x,
            |(ginibreIncidenceDerivativeLinearMap q).det| *
              (c k * h (ginibreIncidenceChart q)) ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (integral_ginibreIncidence_rankPieceBelow_eq_image
        m μ k x (fun p => c k * h p)).symm
    _ = ∑ k : Fin (m + 2),
          ∫ q in ginibreIncidenceRankPieceBelow m k x, f q ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply setIntegral_congr_fun
        (measurableSet_ginibreIncidenceRankPieceBelow m k x)
      intro q hq
      have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1.1
      change |(ginibreIncidenceDerivativeLinearMap q).det| *
          (c k * h (ginibreIncidenceChart q)) = f q
      dsimp [c, f]
      rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.1.2]
      calc
        |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
            ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
              h (ginibreIncidenceChart q)) =
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            |(ginibreIncidenceDeflatedBlock q -
              ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
            h (ginibreIncidenceChart q) := by ring
        _ = _ := by rw [hsign]
    _ = ∫ q in ginibreIncidenceRegularSet m ∩
          {q | ginibreIncidenceEigenvalue q < x}, f q ∂μ := by
      rw [← iUnion_ginibreIncidenceRankPieceBelow]
      symm
      rw [integral_iUnion
        (fun k => measurableSet_ginibreIncidenceRankPieceBelow m k x)
        (pairwiseDisjoint_ginibreIncidenceRankPieceBelow m x)]
      · rw [tsum_fintype]
      · exact integrableOn_iUnion_of_summable_integral_norm
          hsourceInt ((hasSum_fintype (fun k : Fin (m + 2) =>
            ∫ q in ginibreIncidenceRankPieceBelow m k x, ‖f q‖ ∂μ) _).summable)
    _ = ∫ q in {q | ginibreIncidenceEigenvalue q < x}, f q ∂μ := by
      rw [← integral_indicator hbelowMeas,
        ← integral_indicator
          ((measurableSet_ginibreIncidenceRegularSet m).inter hbelowMeas)]
      apply integral_congr_ae
      filter_upwards with q
      by_cases hreg : q ∈ ginibreIncidenceRegularSet m
      · by_cases hlt : ginibreIncidenceEigenvalue q < x
        · simp [hreg, hlt]
        · simp [hreg, hlt]
      · have htan : (ginibreIncidenceTangentMatrix q).det = 0 := by
          simpa [ginibreIncidenceRegularSet] using hreg
        have hdet : (ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det = 0 := by
          have hneg : ginibreIncidenceDeflatedBlock q -
              ginibreIncidenceEigenvalue q • (1 : RSqMat m) =
              -(ginibreIncidenceTangentMatrix q) := by
            unfold ginibreIncidenceTangentMatrix
            abel
          rw [hneg, Matrix.det_neg, htan, mul_zero]
        by_cases hlt : ginibreIncidenceEigenvalue q < x
        · simp [hreg, hlt, f, hdet]
        · simp [hreg, hlt]
    _ = _ := rfl

/-- Integrability companion to the truncated signed-incidence identity. -/
theorem integrableOn_ginibreSignedIncidenceBelow
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (x : ℝ)
    (h : GinibreIncidenceCoordinates m → ℝ) (hh : Integrable h μ) :
    IntegrableOn (fun q : GinibreIncidenceCoordinates m =>
      (ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
        h (ginibreIncidenceChart q))
      {q | ginibreIncidenceEigenvalue q < x} μ := by
  classical
  let f : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      h (ginibreIncidenceChart q)
  have hsourceInt (k : Fin (m + 2)) : IntegrableOn f
      (ginibreIncidenceRankPieceBelow m k x) μ := by
    let c : ℝ := (-1 : ℝ) ^ k.val
    let image : Set (GinibreIncidenceCoordinates m) :=
      ginibreIncidenceChart '' ginibreIncidenceRankPieceBelow m k x
    have htarget : IntegrableOn (fun p => c * h p) image μ :=
      (hh.const_mul c).integrableOn
    have hsource :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        μ (measurableSet_ginibreIncidenceRankPieceBelow m k x)
        (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
        ((injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left)
        (fun p => c * h p)).1 htarget
    refine hsource.congr_fun ?_
      (measurableSet_ginibreIncidenceRankPieceBelow m k x)
    intro q hq
    simp only [smul_eq_mul]
    change |(ginibreIncidenceDerivativeLinearMap q).det| *
        (c * h (ginibreIncidenceChart q)) = f q
    have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1.1
    dsimp [c, f]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.1.2]
    calc
      |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            h (ginibreIncidenceChart q)) =
        ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
          |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
          h (ginibreIncidenceChart q) := by ring
      _ = _ := by rw [hsign]
  have hregBelow : IntegrableOn f
      (ginibreIncidenceRegularSet m ∩
        {q | ginibreIncidenceEigenvalue q < x}) μ := by
    rw [← iUnion_ginibreIncidenceRankPieceBelow]
    exact integrableOn_iUnion_of_summable_integral_norm
      hsourceInt ((hasSum_fintype (fun k : Fin (m + 2) =>
        ∫ q in ginibreIncidenceRankPieceBelow m k x, ‖f q‖ ∂μ) _).summable)
  have hcomp : IntegrableOn f (ginibreIncidenceRegularSet m)ᶜ μ := by
    have hz : IntegrableOn
        (fun _q : GinibreIncidenceCoordinates m => (0 : ℝ))
        (ginibreIncidenceRegularSet m)ᶜ μ :=
      (integrable_zero (GinibreIncidenceCoordinates m) ℝ μ).integrableOn
    refine hz.congr_fun ?_
      (measurableSet_ginibreIncidenceRegularSet m).compl
    intro q hq
    have htan : (ginibreIncidenceTangentMatrix q).det = 0 := by
      simpa [ginibreIncidenceRegularSet] using hq
    have hdet : (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det = 0 := by
      have hneg : ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m) =
          -(ginibreIncidenceTangentMatrix q) := by
        unfold ginibreIncidenceTangentMatrix
        abel
      rw [hneg, Matrix.det_neg, htan, mul_zero]
    simp [f, hdet]
  have hall := hregBelow.union hcomp
  apply hall.mono_set
  intro q hq
  by_cases hreg : q ∈ ginibreIncidenceRegularSet m
  · exact Or.inl ⟨hreg, hq⟩
  · exact Or.inr hreg

end

end NumStability
