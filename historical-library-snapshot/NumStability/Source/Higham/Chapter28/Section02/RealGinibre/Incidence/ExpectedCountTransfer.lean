import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.Polynomials.RealRootCounting
import NumStability.Source.Higham.Chapter04.Problem04
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreGaussianBridge
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreMeasure
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.LebesgueMomentDensities
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.EigenvalueCounts
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.GinibreMultiplicity
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantIntegral, NumStability.Algorithms.TestMatrices.Higham28GinibreGaussianBridge, NumStability.Algorithms.TestMatrices.Higham28GinibreIncidence, NumStability.Algorithms.TestMatrices.Higham28GinibreIntegral, NumStability.Algorithms.TestMatrices.Higham28GinibreMultiplicity under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section

namespace NumStability

open scoped BigOperators

open MeasureTheory MeasureTheory.Measure Set

open scoped ENNReal Function

local instance instMeasurableSpaceGinibreRawMatrix_1 (n : ℕ) : MeasurableSpace (GinibreRawMatrix n) := MeasurableSpace.pi

variable {M Y : Type*}
  [AddCommGroup M] [Module ℝ M]
  [AddCommGroup Y] [Module ℝ Y]

theorem measurable_ginibreIncidenceChart {n : ℕ} :
    Measurable (@ginibreIncidenceChart n) :=
  continuous_ginibreIncidenceChart.measurable

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

theorem measurable_ginibreIncidenceEigenvalue {n : ℕ} :
    Measurable (@ginibreIncidenceEigenvalue n) :=
  continuous_ginibreIncidenceEigenvalue.measurable

theorem measurable_ginibreIncidenceRootRank (n : ℕ) :
    Measurable (@ginibreIncidenceRootRank n) := by
  apply (measurable_realEigenvalueBelowCount (n + 1)).comp
  exact (measurable_ginibreCoordinatesFinMatrix.comp
    measurable_ginibreIncidenceChart).prodMk
      measurable_ginibreIncidenceEigenvalue

theorem measurableSet_ginibreIncidenceRegularSet (n : ℕ) :
    MeasurableSet (ginibreIncidenceRegularSet n) := by
  exact (measurableSet_eq_fun
    continuous_ginibreIncidenceTangentDet.measurable measurable_const).compl

theorem measurableSet_ginibreIncidenceRankPiece (n : ℕ) (k : Fin (n + 2)) :
    MeasurableSet (ginibreIncidenceRankPiece n k) := by
  exact (measurableSet_ginibreIncidenceRegularSet n).inter
    (measurableSet_eq_fun (measurable_ginibreIncidenceRootRank n) measurable_const)

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

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory Set

theorem ginibreRegularFiberMultiplicity_eq_realEigenvalueCount
    {n : ℕ} (p : GinibreIncidenceCoordinates n)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet n)
    (hcritical : p ∉
      ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ) :
    ginibreRegularFiberMultiplicity n p =
      realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p) := by
  classical
  let P := Matrix.charpoly (Matrix.of (ginibreCoordinatesFinMatrix p))
  have hP : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  let r : ℝ → Fin (n + 2) := fun l =>
    ⟨realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, l), by
      have hle := realEigenvalueBelowCount_le
        (ginibreCoordinatesFinMatrix p, l)
      omega⟩
  let R : Finset ℝ := P.roots.toFinset
  let K : Finset (Fin (n + 2)) := Finset.univ.filter fun k =>
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
  have hpre (l : ℝ) (hl : l ∈ P.roots) :
      ∃ q : GinibreIncidenceCoordinates n,
        q ∈ ginibreIncidenceRegularSet n ∧
        ginibreIncidenceChart q = p ∧
        ginibreIncidenceEigenvalue q = l := by
    apply exists_regular_incidence_preimage_of_root p l hboundary hcritical
    rw [← ginibreCoordinatesFinMatrix_charpoly]
    exact (Polynomial.mem_roots hP).1 hl
  have hKR : K = R.image r := by
    ext k
    constructor
    · intro hk
      rcases (Finset.mem_filter.1 hk).2 with ⟨q, hq, hchart⟩
      let l := ginibreIncidenceEigenvalue q
      have hlroot : P.IsRoot l := by
        simpa [P, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
      have hlR : l ∈ R := by
        simp only [R, Multiset.mem_toFinset]
        exact (Polynomial.mem_roots hP).2 hlroot
      apply Finset.mem_image.2
      refine ⟨l, hlR, ?_⟩
      apply Fin.ext
      simpa [r, l, ginibreIncidenceRootRank, hchart] using hq.2
    · intro hk
      rcases Finset.mem_image.1 hk with ⟨l, hlR, rfl⟩
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      have hl : l ∈ P.roots := by
        simpa [R] using hlR
      obtain ⟨q, hreg, hchart, hlam⟩ := hpre l hl
      refine ⟨q, ?_, hchart⟩
      refine ⟨hreg, ?_⟩
      simpa [r, ginibreIncidenceRootRank, hchart, hlam]
  have hrinj : Set.InjOn r (R : Set ℝ) := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have haP : a ∈ P.roots := by simpa [R] using ha
      have hstrict := card_filter_lt_card_filter_of_mem P.roots haP hlt
      have : (r a).val < (r b).val := by
        simpa [r, realEigenvalueBelowCount, P] using hstrict
      rw [hab] at this
      exact (lt_irrefl _ this)
    · have hbP : b ∈ P.roots := by simpa [R] using hb
      have hstrict := card_filter_lt_card_filter_of_mem P.roots hbP hgt
      have : (r b).val < (r a).val := by
        simpa [r, realEigenvalueBelowCount, P] using hstrict
      rw [hab] at this
      exact (lt_irrefl _ this)
  have hnodup : P.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro l
    by_cases hl : l ∈ P.roots
    · obtain ⟨q, hreg, hchart, hlam⟩ := hpre l hl
      have hcount :=
        (mem_ginibreIncidenceRegularSet_iff_root_count_eq_one q).1 hreg
      have hchar : P = (ginibreIncidenceMatrix q).charpoly := by
        change (Matrix.of (ginibreCoordinatesFinMatrix p)).charpoly =
          (ginibreIncidenceMatrix q).charpoly
        rw [ginibreCoordinatesFinMatrix_charpoly]
        rw [← hchart, ginibreCoordinatesMatrix_chart]
      rw [hchar]
      simpa [hlam] using hcount.le
    · rw [Multiset.count_eq_zero.2 hl]
      omega
  have hcardImage : (R.image r).card = R.card :=
    Finset.card_image_iff.mpr hrinj
  calc
    ginibreRegularFiberMultiplicity n p = K.card := by
      simp [ginibreRegularFiberMultiplicity, K, Finset.sum_boole]
    _ = (R.image r).card := by rw [hKR]
    _ = R.card := hcardImage
    _ = P.roots.card := by
      simpa [R] using Multiset.toFinset_card_of_nodup hnodup
    _ = realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p) := rfl

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory MeasureTheory.Measure Set

open scoped ENNReal BigOperators

local instance instStandardBorelSpaceGinibreIncidenceNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod

local instance instStandardBorelSpaceGinibreIncidenceCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

theorem measurableSet_ginibreIncidenceRankImage (n : ℕ) (k : Fin (n + 2)) :
    MeasurableSet (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k) :=
  (measurableSet_ginibreIncidenceRankPiece n k).image_of_measurable_injOn
    measurable_ginibreIncidenceChart (injOn_ginibreIncidenceChart_rankPiece n k)

theorem ae_ginibreRegularFiberMultiplicity_eq_realEigenvalueCount
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] :
    ∀ᵐ p ∂μ, ginibreRegularFiberMultiplicity n p =
      realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p) := by
  have hb : ∀ᵐ p ∂μ, p ∉ ginibreAffineBoundaryEigenpairSet n :=
    (measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreAffineBoundaryEigenpairSet_eq_zero n μ))
  have hc : ∀ᵐ p ∂μ,
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ :=
    (measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreIncidence_criticalImage_eq_zero n μ))
  filter_upwards [hb, hc] with p hbp hcp
  exact ginibreRegularFiberMultiplicity_eq_realEigenvalueCount p hbp hcp

theorem sum_lintegral_ginibreRankImages_eq_fiberMultiplicity
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    (g : GinibreIncidenceCoordinates n → ℝ≥0∞) (hg : Measurable g) :
    ∑ k : Fin (n + 2),
        ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece n k,
          g p ∂μ =
      ∫⁻ p, (ginibreRegularFiberMultiplicity n p : ℝ≥0∞) * g p ∂μ := by
  symm
  calc
    (∫⁻ p, (ginibreRegularFiberMultiplicity n p : ℝ≥0∞) * g p ∂μ) =
        ∫⁻ p, ∑ k : Fin (n + 2),
          (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k).indicator g p ∂μ := by
      apply lintegral_congr
      intro p
      classical
      unfold ginibreRegularFiberMultiplicity
      rw [Nat.cast_sum]
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      calc
        (∑ k : Fin (n + 2),
              if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
                then (1 : ℝ≥0∞) else 0) * g p =
            ∑ k : Fin (n + 2),
              (if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
                then (1 : ℝ≥0∞) else 0) * g p := by
          exact Finset.sum_mul Finset.univ _ _
        _ = ∑ k : Fin (n + 2),
            (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k).indicator g p := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hmem :
              p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
          · simp [hmem]
          · simp [hmem]
    _ = ∑ k : Fin (n + 2), ∫⁻ p,
        (ginibreIncidenceChart '' ginibreIncidenceRankPiece n k).indicator g p ∂μ := by
      rw [MeasureTheory.lintegral_finset_sum Finset.univ]
      intro k hk
      exact hg.indicator (measurableSet_ginibreIncidenceRankImage n k)
    _ = ∑ k : Fin (n + 2),
        ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece n k,
          g p ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact lintegral_indicator
        (measurableSet_ginibreIncidenceRankImage n k) g

theorem lintegral_ginibreIncidence_regular_eq_rootCount
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure]
    (g : GinibreIncidenceCoordinates n → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q in ginibreIncidenceRegularSet n,
        ENNReal.ofReal |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫⁻ p, (realEigenvalueCount (n + 1)
        (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) * g p ∂μ := by
  rw [lintegral_ginibreIncidence_regular_eq_sum_rank_images n μ g]
  rw [sum_lintegral_ginibreRankImages_eq_fiberMultiplicity n μ g hg]
  apply lintegral_congr_ae
  filter_upwards [ae_ginibreRegularFiberMultiplicity_eq_realEigenvalueCount n μ]
    with p hp
  rw [hp]

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal BigOperators

/-- The Gaussian-weighted real-root count in matrix coordinates is exactly
the unrestricted incidence integral of the absolute deflated characteristic
determinant.  This is the fully specialized Kac--Rice/coarea reduction; only
its scalar analytic evaluation remains. -/
theorem lintegral_ginibreIncidence_gaussian_eq_rootCount
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] :
    ∫⁻ q,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))) ∂μ =
      ∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p)) ∂μ := by
  let g : GinibreIncidenceCoordinates n → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (realGinibreDensityReal (n + 1)
      (ginibreCoordinatesFinMatrix p))
  have hg : Measurable g :=
    (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal.comp
      measurable_ginibreCoordinatesFinMatrix
  rw [← lintegral_ginibreIncidence_regular_eq_rootCount n μ g hg]
  rw [← lintegral_indicator (measurableSet_ginibreIncidenceRegularSet n)]
  apply lintegral_congr
  intro q
  by_cases hq : q ∈ ginibreIncidenceRegularSet n
  · rw [Set.indicator_of_mem hq]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det]
  · rw [Set.indicator_of_notMem hq]
    have hdet : (ginibreIncidenceTangentMatrix q).det = 0 := by
      simpa [ginibreIncidenceRegularSet] using hq
    have hderiv : (ginibreIncidenceDerivativeLinearMap q).det = 0 := by
      rw [ginibreIncidenceDerivativeLinearMap_det, hdet]
    have habs : |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| = 0 := by
      rw [← abs_ginibreIncidenceDerivativeLinearMap_det, hderiv]
      simp
    rw [habs]
    simp

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal BigOperators

private local instance ginibreGaussianBridgeMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreGaussianBridgeStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod

private local instance ginibreGaussianBridgeStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

private instance matrixVolume_isAddHaarMeasure (n : ℕ) :
    (volume : Measure (GinibreRawMatrix n)).IsAddHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsAddLeftInvariant := inferInstance
  toIsOpenPosMeasure := inferInstance

local instance ginibreIncidenceLebesgueMeasure_isAddHaarMeasure (n : ℕ) :
    (ginibreIncidenceLebesgueMeasure n).IsAddHaarMeasure := by
  unfold ginibreIncidenceLebesgueMeasure
  exact ContinuousLinearEquiv.isAddHaarMeasure_map
    (ginibreCoordinatesContinuousLinearEquiv n).symm
      (volume : Measure (GinibreRawMatrix (n + 1)))

/-- The affine block assembly map sends incidence Lebesgue measure to the
standard nested product Lebesgue measure on matrices, with no scalar
renormalization. -/
theorem ginibreIncidenceLebesgueMeasure_map (n : ℕ) :
    Measure.map ginibreCoordinatesFinMatrix
        (ginibreIncidenceLebesgueMeasure n) =
      realGinibreLebesgueMeasure (n + 1) := by
  unfold ginibreIncidenceLebesgueMeasure
  rw [Measure.map_map]
  · have hfun : ginibreCoordinatesFinMatrix ∘
        (ginibreCoordinatesContinuousLinearEquiv n).symm = id := by
      funext A
      exact (ginibreCoordinatesLinearEquiv n).apply_symm_apply A
    rw [hfun, Measure.map_id]
    symm
    simp [realGinibreLebesgueMeasure, volume_pi]
  · exact measurable_ginibreCoordinatesFinMatrix
  · exact (ginibreCoordinatesContinuousLinearEquiv n).symm.continuous.measurable

/-- The Gaussian density-weighted root-count `lintegral` in affine block
coordinates is the nonnegative embedding of the real-Ginibre expectation. -/
theorem lintegral_ginibreCoordinate_rootCount_density_eq_expected
    (n : ℕ) :
    (∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
  let F : GinibreRawMatrix (n + 1) → ℝ≥0∞ := fun A =>
    (realEigenvalueCount (n + 1) A : ℝ≥0∞) *
      ENNReal.ofReal (realGinibreDensityReal (n + 1) A)
  have hmp : MeasurePreserving ginibreCoordinatesFinMatrix
      (ginibreIncidenceLebesgueMeasure n)
      (realGinibreLebesgueMeasure (n + 1)) :=
    ⟨measurable_ginibreCoordinatesFinMatrix,
      ginibreIncidenceLebesgueMeasure_map n⟩
  calc
    (∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p))
      ∂ginibreIncidenceLebesgueMeasure n) =
        ∫⁻ A, F A ∂realGinibreLebesgueMeasure (n + 1) := by
      exact hmp.lintegral_comp_emb
        (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.measurableEmbedding F
    _ = ∫⁻ A, (realEigenvalueCount (n + 1) A : ℝ≥0∞)
        ∂realGinibreMeasure (n + 1) := by
      rw [realGinibreMeasure_eq_withDensity,
        lintegral_withDensity_eq_lintegral_mul]
      · apply lintegral_congr
        intro A
        simp [F, mul_comm]
      · exact (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal
      · exact (measurable_of_countable _).comp
          (measurable_realEigenvalueCount (n + 1))
    _ = ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
      unfold expectedRealEigenvalueCount
      symm
      simpa using (ofReal_integral_eq_lintegral_ofReal
        (integrable_realEigenvalueCount (n + 1))
        (ae_of_all _ fun A => Nat.cast_nonneg _))

/-- With the correctly normalized affine Lebesgue measure, the unrestricted
Gaussian incidence determinant integral is exactly the real-Ginibre expected
real-eigenvalue count. -/
theorem lintegral_ginibreIncidence_gaussian_eq_expected (n : ℕ) :
    (∫⁻ q,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
  rw [lintegral_ginibreIncidence_gaussian_eq_rootCount n
    (ginibreIncidenceLebesgueMeasure n)]
  exact lintegral_ginibreCoordinate_rootCount_density_eq_expected n

end NumStability

end
