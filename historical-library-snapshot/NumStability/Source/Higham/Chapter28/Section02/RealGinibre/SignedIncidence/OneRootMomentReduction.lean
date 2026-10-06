import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational
import NumStability.Analysis.TestMatrices.RealGinibre.ProjectiveWeightIntegral
import NumStability.Source.Higham.Chapter04.Problem04
import NumStability.Source.Higham.Chapter06.Asides.EuclideanNormDifferentiability
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreCorollary31Factor
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreAtlas
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreJointDensity
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.AlternatingRankSheets
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedRankTransfer
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GinibreCorollary31Factor, NumStability.Algorithms.TestMatrices.Higham28GinibreOrthogonalFiber, NumStability.Algorithms.TestMatrices.Higham28GinibreSignedIncidence under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

/-- Integral form of the exact Corollary 3.1 normalization. -/
theorem gaussianZeroPow_mul_integral_ginibreProjectiveWeight (n : ℕ) :
    (gaussianPDFReal 0 1 0) ^ n *
        (∫ y : Fin n → ℝ,
          (1 + ∑ i, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      ginibreCorollary31Factor (n + 1) := by
  rw [integral_ginibreProjectiveWeight,
    gaussianZeroPow_mul_projectiveConstant]

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter Matrix

open scoped ENNReal BigOperators RealInnerProductSpace Matrix.Norms.Frobenius

private local instance ginibreOrthogonalFiberMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreOrthogonalFiberMeasureSpaceRSqMat (n : ℕ) :
    MeasureSpace (RSqMat n) := {
  toMeasurableSpace := MeasurableSpace.pi
  volume := realGinibreLebesgueMeasure n }

private local instance ginibreOrthogonalFiberMeasureSpaceNuisanceCore (n : ℕ) :
    MeasureSpace (RSqMat n × (Fin n → ℝ)) := {
  toMeasurableSpace := Prod.instMeasurableSpace
  volume := (volume : Measure (RSqMat n)).prod
    (volume : Measure (Fin n → ℝ)) }

private local instance ginibreOrthogonalFiberMeasureSpaceNuisance (n : ℕ) :
    MeasureSpace (GinibreIncidenceNuisance n) := {
  toMeasurableSpace := Prod.instMeasurableSpace
  volume := (volume : Measure (RSqMat n × (Fin n → ℝ))).prod volume }

private local instance ginibreOrthogonalFiberMeasureSpaceCoordinates (n : ℕ) :
    MeasureSpace (GinibreIncidenceCoordinates n) := {
  toMeasurableSpace := Prod.instMeasurableSpace
  volume := (volume : Measure (GinibreIncidenceNuisance n)).prod volume }

private local instance ginibreOrthogonalFiberStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod

private local instance ginibreOrthogonalFiberStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

private instance ginibreOrthogonalFiberMatrixMeasurableAdd (n : ℕ) :
    MeasurableAdd (RSqMat n) := {
  measurable_const_add := by
    intro C
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    have hi : Measurable (fun A : RSqMat n => A i) := measurable_pi_apply i
    have hij : Measurable (fun A : RSqMat n => A i j) :=
      (measurable_pi_apply j).comp hi
    exact measurable_const.add hij
  measurable_add_const := by
    intro C
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    have hi : Measurable (fun A : RSqMat n => A i) := measurable_pi_apply i
    have hij : Measurable (fun A : RSqMat n => A i j) :=
      (measurable_pi_apply j).comp hi
    exact hij.add measurable_const }

private instance ginibreOrthogonalFiberMatrixVolumeIsAddHaar (n : ℕ) :
    (volume : Measure (RSqMat n)).IsAddHaarMeasure := {
  toIsFiniteMeasureOnCompacts := by
    change IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin n => volume)))
    infer_instance
  toIsAddLeftInvariant := by
    change (Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin n => volume))).IsAddLeftInvariant
    infer_instance
  toIsOpenPosMeasure := by
    change (Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin n => volume))).IsOpenPosMeasure
    infer_instance }

private local instance ginibreOrthogonalFiberMatrixVolumeSigmaFinite (n : ℕ) :
    SigmaFinite (volume : Measure (RSqMat n)) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

private instance ginibreOrthogonalFiberNuisanceCoreMeasurableAdd (n : ℕ) :
    MeasurableAdd (RSqMat n × (Fin n → ℝ)) := {
  measurable_const_add := by
    intro c
    exact ((measurable_const_add c.1).comp measurable_fst).prodMk
      ((measurable_const_add c.2).comp measurable_snd)
  measurable_add_const := by
    intro c
    exact ((measurable_add_const c.1).comp measurable_fst).prodMk
      ((measurable_add_const c.2).comp measurable_snd) }

private instance ginibreOrthogonalFiberNuisanceCoreVolumeIsAddHaar (n : ℕ) :
    (volume : Measure (RSqMat n × (Fin n → ℝ))).IsAddHaarMeasure := by
  change ((volume : Measure (RSqMat n)).prod
    (volume : Measure (Fin n → ℝ))).IsAddHaarMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

private local instance ginibreOrthogonalFiberNuisanceCoreVolumeSigmaFinite (n : ℕ) :
    SigmaFinite (volume : Measure (RSqMat n × (Fin n → ℝ))) := by
  change SigmaFinite ((volume : Measure (RSqMat n)).prod
    (volume : Measure (Fin n → ℝ)))
  infer_instance

private instance ginibreOrthogonalFiberNuisanceVolumeIsAddHaar (n : ℕ) :
    (volume : Measure (GinibreIncidenceNuisance n)).IsAddHaarMeasure := by
  change ((volume : Measure (RSqMat n × (Fin n → ℝ))).prod
    (volume : Measure ℝ)).IsAddHaarMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

variable {M Y : Type*}
  [AddCommGroup M] [Module ℝ M]
  [AddCommGroup Y] [Module ℝ Y]

/-- The finite coordinate permutation
`(((C,z),b),y) ↦ ((b,z),(y,C))` preserves product Lebesgue measure. -/
theorem volume_preserving_ginibreCoordinateReorder (n : ℕ) :
    MeasurePreserving
      (fun q : GinibreIncidenceCoordinates n =>
        ((q.1.2, q.1.1.2), (q.2, q.1.1.1))) := by
  let A := Fin n → Fin n → ℝ
  let B := Fin n → ℝ
  let C := ℝ
  let D := Fin n → ℝ
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((A × B) × C) × D ≃ᵐ
        (A × B) × (C × D)) := volume_preserving_prodAssoc
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (A × B) × (C × D) ≃ᵐ
        A × (B × (C × D))) := volume_preserving_prodAssoc
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodComm : A × (B × (C × D)) ≃ᵐ
        (B × (C × D)) × A) := Measure.measurePreserving_swap
  have h4 : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (B × (C × D)) × A ≃ᵐ
        B × ((C × D) × A)) := volume_preserving_prodAssoc
  have h5 : MeasurePreserving
      (fun p : B × ((C × D) × A) =>
        (p.1, (p.2.1.1, (p.2.1.2, p.2.2)))) :=
    by
      have hp := (MeasurePreserving.id (volume : Measure B)).prod
        (volume_preserving_prodAssoc : MeasurePreserving
          (MeasurableEquiv.prodAssoc : (C × D) × A ≃ᵐ C × (D × A)))
      simpa [Prod.map] using hp
  have h6 : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : B × (C × (D × A)) ≃ᵐ
        (B × C) × (D × A)) := volume_preserving_prodAssoc.symm
  have h7 : MeasurePreserving
      (fun p : (B × C) × (D × A) => ((p.1.2, p.1.1), p.2)) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure B))
      (ν := (volume : Measure C))).prod
        (MeasurePreserving.id (volume : Measure (D × A)))
  have h := h7.comp (h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1)))))
  simpa [A, B, C, D, Function.comp_def] using h

/-- Affine block assembly is a coordinate permutation, hence preserves the
canonical product Lebesgue measure exactly. -/
theorem volume_preserving_ginibreCoordinatesFinMatrix (n : ℕ) :
    MeasurePreserving (@ginibreCoordinatesFinMatrix n) := by
  let Row := Fin (n + 1) → ℝ
  let LeftRow := Fin n → ℝ
  let rowSplit : Row ≃ᵐ ℝ × LeftRow :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  let outerSplit : (Fin (n + 1) → Row) ≃ᵐ Row × (Fin n → Row) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Row) (Fin.last n)
  have hrow : MeasurePreserving rowSplit.symm :=
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hpair : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ LeftRow (Fin n)).symm :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ LeftRow (Fin n)).symm
  have hpi : MeasurePreserving
      (fun f : Fin n → ℝ × LeftRow => fun i => rowSplit.symm (f i)) := by
    simpa [rowSplit] using
      (volume_preserving_pi (fun _ : Fin n => hrow))
  have htop : MeasurePreserving
      (fun p : (Fin n → ℝ) × (Fin n → LeftRow) =>
        fun i => rowSplit.symm (p.1 i, p.2 i)) := by
    have h := hpi.comp hpair
    simpa [Function.comp_def] using h
  have hblocks : MeasurePreserving
      (fun p : (ℝ × LeftRow) × ((Fin n → ℝ) × (Fin n → LeftRow)) =>
        (rowSplit.symm p.1, fun i => rowSplit.symm (p.2.1 i, p.2.2 i))) := by
    have h := hrow.prod htop
    simpa [Prod.map] using h
  have houter : MeasurePreserving outerSplit.symm :=
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => Row) (Fin.last n)).symm
  have hjoin : MeasurePreserving
      (fun p : (ℝ × LeftRow) × ((Fin n → ℝ) × (Fin n → LeftRow)) =>
        outerSplit.symm
          (rowSplit.symm p.1, fun i => rowSplit.symm (p.2.1 i, p.2.2 i))) :=
    houter.comp hblocks
  have h := hjoin.comp (volume_preserving_ginibreCoordinateReorder n)
  have hrow_last (p : ℝ × LeftRow) :
      rowSplit.symm p (Fin.last n) = p.1 := by
    have hp := congrArg Prod.fst (rowSplit.apply_symm_apply p)
    exact hp
  have hrow_castSucc (p : ℝ × LeftRow) (j : Fin n) :
      rowSplit.symm p j.castSucc = p.2 j := by
    have hp := congrArg (fun r : ℝ × LeftRow => r.2 j)
      (rowSplit.apply_symm_apply p)
    change rowSplit.symm p ((Fin.last n).succAbove j) = p.2 j at hp
    simpa using hp
  have hfun : (fun q : GinibreIncidenceCoordinates n =>
      outerSplit.symm
        (rowSplit.symm (q.1.2, q.1.1.2),
          fun i => rowSplit.symm (q.2 i, q.1.1.1 i))) =
      @ginibreCoordinatesFinMatrix n := by
    funext q i j
    by_cases hi : i = Fin.last n
    · subst i
      by_cases hj : j = Fin.last n
      · subst j
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_last (q.1.2, q.1.1.2)
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_castSucc (q.1.2, q.1.1.2) j
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      by_cases hj : j = Fin.last n
      · subst j
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_last (q.2 i, q.1.1.1 i)
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        simp [outerSplit, rowSplit, ginibreCoordinatesFinMatrix,
          ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
          Matrix.reindex, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv]
        exact hrow_castSucc (q.2 i, q.1.1.1 i) j
  rw [← hfun]
  simpa [Function.comp_def] using h

/-- The normalized affine incidence measure is literally the canonical
product Lebesgue measure; there is no residual Haar scalar. -/
theorem ginibreIncidenceLebesgueMeasure_eq_volume (n : ℕ) :
    ginibreIncidenceLebesgueMeasure n =
      (volume : Measure (GinibreIncidenceCoordinates n)) := by
  let e : GinibreIncidenceCoordinates n ≃ᵐ GinibreRawMatrix (n + 1) :=
    (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e := by
    simpa [e, ginibreCoordinatesContinuousLinearEquiv,
      ginibreCoordinatesLinearEquiv] using
        (volume_preserving_ginibreCoordinatesFinMatrix n)
  have hesymm := MeasurePreserving.symm e he
  unfold ginibreIncidenceLebesgueMeasure
  exact hesymm.map_eq

/-- Fixed-direction signed transfer with an arbitrary characteristic-polynomial
weight.  It deliberately stops at the nuisance-coordinate integral; later
applications can apply Fubini under the integrability hypothesis natural to
their particular weight. -/
theorem integral_ginibreSignedFixedFiber_of_orthogonal (n : ℕ)
    (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y)
    (H : Polynomial ℝ → ℝ → ℝ) :
    (∫ u : GinibreIncidenceNuisance n,
      (ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det *
        H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock (u, y))))
          (ginibreIncidenceEigenvalue (u, y)) *
        realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))) =
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2)) *
        (gaussianPDFReal 0 1 0) ^ n *
          ∫ v : GinibreIncidenceNuisance n,
            ((show RSqMat n from v.1.1) -
                v.2 • (1 : RSqMat n)).det *
              H (Matrix.charpoly (Matrix.of
                (show RSqMat n from v.1.1))) v.2 *
              realGinibreDensityReal n (show RSqMat n from v.1.1) *
              (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
              gaussianPDFReal 0 1 v.2 := by
  let F := ginibreOrthogonalBlockToNuisanceLinearMap n Q
  let g : GinibreIncidenceNuisance n → ℝ := fun u =>
    (ginibreIncidenceDeflatedBlock (u, y) -
        ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det *
      H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock (u, y))))
        (ginibreIncidenceEigenvalue (u, y)) *
      realGinibreDensityReal (n + 1)
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))
  let w : ℝ :=
    (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have hw : 0 < w := by
    dsimp [w]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hdet : |LinearMap.det F| = w :=
    abs_det_ginibreOrthogonalBlockToNuisanceLinearMap_eq_projectiveWeight
      n y Q hQ hcol
  have hF : LinearMap.det F ≠ 0 := by
    intro hzero
    have habs : |LinearMap.det F| = 0 := by rw [hzero, abs_zero]
    exact (ne_of_gt hw) (hdet.symm.trans habs)
  have hcov := integral_linearMap_eq_abs_det_mul
    (volume : Measure (GinibreIncidenceNuisance n)) F hF g
  rw [hdet] at hcov
  calc
    (∫ u : GinibreIncidenceNuisance n,
      (ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det *
        H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock (u, y))))
          (ginibreIncidenceEigenvalue (u, y)) *
        realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))) =
        w * ∫ v : GinibreIncidenceNuisance n, g (F v) := hcov
    _ = w * ∫ v : GinibreIncidenceNuisance n,
          (gaussianPDFReal 0 1 0) ^ n *
            (((show RSqMat n from v.1.1) -
                v.2 • (1 : RSqMat n)).det *
              H (Matrix.charpoly (Matrix.of
                (show RSqMat n from v.1.1))) v.2 *
              realGinibreDensityReal n (show RSqMat n from v.1.1) *
              (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
              gaussianPDFReal 0 1 v.2) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with v
      exact ginibreSignedFixedFiber_integrand_eq n y Q hQ hcol H v
    _ = w * (gaussianPDFReal 0 1 0) ^ n *
          ∫ v : GinibreIncidenceNuisance n,
            ((show RSqMat n from v.1.1) -
                v.2 • (1 : RSqMat n)).det *
              H (Matrix.charpoly (Matrix.of
                (show RSqMat n from v.1.1))) v.2 *
              realGinibreDensityReal n (show RSqMat n from v.1.1) *
              (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
              gaussianPDFReal 0 1 v.2 := by
      rw [integral_const_mul]
      ring

/-- Integrating the block variables leaves exactly the absolute
characteristic-moment `lintegral`; the auxiliary bottom row has mass one. -/
theorem lintegral_ginibreOrthogonalBlockDensity (n : ℕ) :
    (∫⁻ v : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2)) =
      realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  let Z : (Fin n → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (∏ i : Fin n, gaussianPDFReal 0 1 (z i))
  let H : RSqMat n → ℝ → ℝ≥0∞ := fun C l =>
    ENNReal.ofReal
      (|(C - l • (1 : RSqMat n)).det| *
        realGinibreDensityReal n C * gaussianPDFReal 0 1 l)
  have hZ : Measurable Z := by
    unfold Z
    fun_prop
  have hH (C : RSqMat n) : Measurable (H C) := by
    unfold H
    apply Measurable.ennreal_ofReal
    have hdet := (measurable_abs_det_ginibreShiftReal n).comp
      ((show Measurable (fun _ : ℝ => C) from measurable_const).prodMk measurable_id)
    exact (hdet.mul (show Measurable (fun _ : ℝ =>
      realGinibreDensityReal n C) from measurable_const)).mul
        (measurable_gaussianPDFReal 0 1)
  have hpoint (C : RSqMat n) (z : Fin n → ℝ) (l : ℝ) :
      ENNReal.ofReal
        (|(C - l • (1 : RSqMat n)).det| *
          realGinibreDensityReal n C *
          (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
          gaussianPDFReal 0 1 l) = Z z * H C l := by
    rw [show |(C - l • (1 : RSqMat n)).det| *
          realGinibreDensityReal n C *
          (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
          gaussianPDFReal 0 1 l =
        (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
          (|(C - l • (1 : RSqMat n)).det| *
            realGinibreDensityReal n C * gaussianPDFReal 0 1 l) by ring]
    rw [ENNReal.ofReal_mul
      (Finset.prod_nonneg fun i hi => gaussianPDFReal_nonneg 0 1 (z i))]
  have hfull : Measurable (fun v : GinibreIncidenceNuisance n =>
      ENNReal.ofReal
        (|((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2)) := by
    apply Measurable.ennreal_ofReal
    have hCcoord : Measurable (fun v : GinibreIncidenceNuisance n =>
        (show RSqMat n from v.1.1)) :=
      measurable_fst.comp measurable_fst
    have hlcoord : Measurable (fun v : GinibreIncidenceNuisance n => v.2) :=
      measurable_snd
    have hdet := (measurable_abs_det_ginibreShiftReal n).comp
      (hCcoord.prodMk hlcoord)
    have hC := (measurable_realGinibreDensityReal n).comp hCcoord
    have hz : Measurable (fun v : GinibreIncidenceNuisance n =>
        ∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) := by fun_prop
    have hl := (measurable_gaussianPDFReal 0 1).comp hlcoord
    exact ((hdet.mul hC).mul hz).mul hl
  calc
    (∫⁻ v : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2)) =
        ∫⁻ p : RSqMat n × (Fin n → ℝ), ∫⁻ l : ℝ,
          ENNReal.ofReal
            (|(p.1 - l • (1 : RSqMat n)).det| *
              realGinibreDensityReal n p.1 *
              (∏ i : Fin n, gaussianPDFReal 0 1 (p.2 i)) *
              gaussianPDFReal 0 1 l) := by
      rw [Measure.volume_eq_prod]
      exact lintegral_prod _ hfull.aemeasurable
    _ = ∫⁻ C : RSqMat n, ∫⁻ z : Fin n → ℝ, ∫⁻ l : ℝ,
          ENNReal.ofReal
            (|(C - l • (1 : RSqMat n)).det| *
              realGinibreDensityReal n C *
              (∏ i : Fin n, gaussianPDFReal 0 1 (z i)) *
              gaussianPDFReal 0 1 l) := by
      rw [Measure.volume_eq_prod]
      have hinner : Measurable (fun p : RSqMat n × (Fin n → ℝ) =>
          ∫⁻ l : ℝ,
            ENNReal.ofReal
              (|(p.1 - l • (1 : RSqMat n)).det| *
                realGinibreDensityReal n p.1 *
                (∏ i : Fin n, gaussianPDFReal 0 1 (p.2 i)) *
                gaussianPDFReal 0 1 l)) :=
        hfull.lintegral_prod_right'
      exact lintegral_prod _ hinner.aemeasurable
    _ = ∫⁻ C : RSqMat n, ∫⁻ z : Fin n → ℝ, ∫⁻ l : ℝ,
          Z z * H C l := by
      apply lintegral_congr
      intro C
      apply lintegral_congr
      intro z
      apply lintegral_congr
      intro l
      exact hpoint C z l
    _ = ∫⁻ C : RSqMat n,
          (∫⁻ z : Fin n → ℝ, Z z) * (∫⁻ l : ℝ, H C l) := by
      apply lintegral_congr
      intro C
      exact lintegral_lintegral_mul hZ.aemeasurable (hH C).aemeasurable
    _ = ∫⁻ C : RSqMat n, ∫⁻ l : ℝ, H C l := by
      rw [show (∫⁻ z : Fin n → ℝ, Z z) = 1 by
        exact lintegral_standardGaussianVectorDensity n]
      simp
    _ = realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity]
      have hjoint : Measurable (fun p : RSqMat n × ℝ =>
          ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
            ENNReal.ofReal
              (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)) :=
        ((measurable_abs_det_ginibreShift n).mul
          (((measurable_realGinibreDensityReal n).comp measurable_fst).mul
            ((measurable_gaussianPDFReal 0 1).comp measurable_snd)).ennreal_ofReal)
      rw [lintegral_prod _ hjoint.aemeasurable]
      apply lintegral_congr
      intro C
      apply lintegral_congr
      intro l
      unfold H
      rw [show |(C - l • (1 : RSqMat n)).det| *
          realGinibreDensityReal n C * gaussianPDFReal 0 1 l =
        |(C - l • (1 : RSqMat n)).det| *
          (realGinibreDensityReal n C * gaussianPDFReal 0 1 l) by ring]
      rw [ENNReal.ofReal_mul (abs_nonneg _)]

/-- The fixed affine-direction incidence integral after choosing an
orthogonal representative of that direction.  The representative disappears
from the right-hand side: its only contribution is the projective Jacobian. -/
theorem lintegral_ginibreFixedFiber_of_orthogonal (n : ℕ)
    (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y) :
    (∫⁻ u : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
      ENNReal.ofReal
          ((1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) *
        ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  let F := ginibreOrthogonalBlockToNuisanceLinearMap n Q
  let g : GinibreIncidenceNuisance n → ℝ≥0∞ := fun u =>
    ENNReal.ofReal
      (|(ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
        realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))
  let w : ℝ :=
    (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have hw : 0 < w := by
    dsimp [w]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hdet : |LinearMap.det F| = w := by
    exact abs_det_ginibreOrthogonalBlockToNuisanceLinearMap_eq_projectiveWeight
      n y Q hQ hcol
  have hF : LinearMap.det F ≠ 0 := by
    intro hzero
    have habs : |LinearMap.det F| = 0 := by rw [hzero, abs_zero]
    exact (ne_of_gt hw) (hdet.symm.trans habs)
  have hcov := lintegral_linearMap_eq_abs_det_mul
    (volume : Measure (GinibreIncidenceNuisance n)) F hF g
  rw [hdet] at hcov
  calc
    (∫⁻ u : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
        ENNReal.ofReal w * ∫⁻ v : GinibreIncidenceNuisance n, g (F v) := by
      exact hcov
    _ = ENNReal.ofReal w *
        ∫⁻ v : GinibreIncidenceNuisance n,
          ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            ENNReal.ofReal
              (|((show RSqMat n from v.1.1) -
                    v.2 • (1 : RSqMat n)).det| *
                realGinibreDensityReal n (show RSqMat n from v.1.1) *
                (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
                gaussianPDFReal 0 1 v.2) := by
      congr 1
      apply lintegral_congr
      intro v
      have hpoint := congrArg ENNReal.ofReal
        (ginibreFixedFiber_integrand_eq n y Q hQ hcol v)
      rw [ENNReal.ofReal_mul
        (pow_nonneg (gaussianPDFReal_nonneg 0 1 0) n)] at hpoint
      exact hpoint
    _ = ENNReal.ofReal w * ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_ginibreOrthogonalBlockDensity]
      ring

/-- Premise-free fixed-direction formula.  The orthogonal representative is
chosen pointwise, so no measurable-selection hypothesis is needed. -/
theorem lintegral_ginibreFixedFiber (n : ℕ) (y : Fin n → ℝ) :
    (∫⁻ u : GinibreIncidenceNuisance n,
      ENNReal.ofReal
        (|(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
      ENNReal.ofReal
          ((1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) *
        ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  obtain ⟨Q, hQ, hcol⟩ := exists_orthogonal_lastColumn_affine n y
  exact lintegral_ginibreFixedFiber_of_orthogonal n y Q hQ hcol

/-- Integrability of the affine projective weight, extracted from its already
evaluated (strictly positive) ordinary integral. -/
theorem integrable_ginibreProjectiveWeight (n : ℕ) :
    Integrable (fun y : Fin n → ℝ =>
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) := by
  by_contra h
  have hzero : (∫ y : Fin n → ℝ,
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) = 0 :=
    integral_undef h
  rw [integral_ginibreProjectiveWeight] at hzero
  have hpos : 0 <
      Real.pi ^ (((n : ℝ) + 1) / 2) /
        Real.Gamma (((n : ℝ) + 1) / 2) := by
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.Gamma_pos_of_pos (by positivity))
  linarith

/-- The full affine incidence integral is the Corollary 3.1 normalization
times the absolute characteristic-moment `lintegral`. -/
theorem lintegral_ginibreIncidence_gaussian_eq_corollary31Factor_mul_momentLIntegral
    (n : ℕ) :
    (∫⁻ q : GinibreIncidenceCoordinates n,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (ginibreCorollary31Factor (n + 1)) *
        realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  let W : (Fin n → ℝ) → ℝ := fun y =>
    (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have hW : Measurable W := by
    unfold W
    fun_prop
  have hweight_eq :
      (fun q : GinibreIncidenceCoordinates n =>
        |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det|) =
      (fun q => |(ginibreIncidenceTangentMatrix q).det|) := by
    funext q
    have hneg : ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n) =
        -(ginibreIncidenceTangentMatrix q) := by
      unfold ginibreIncidenceTangentMatrix
      abel
    rw [hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
  have hdet : Measurable (fun q : GinibreIncidenceCoordinates n =>
      ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det|) := by
    apply Measurable.ennreal_ofReal
    rw [hweight_eq]
    exact continuous_ginibreIncidenceTangentDet.abs.measurable
  have hdensity : Measurable (fun q : GinibreIncidenceCoordinates n =>
      ENNReal.ofReal (realGinibreDensityReal (n + 1)
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))) :=
    ((measurable_realGinibreDensityReal (n + 1)).comp
      (measurable_ginibreCoordinatesFinMatrix.comp
        measurable_ginibreIncidenceChart)).ennreal_ofReal
  have hfull : Measurable (fun q : GinibreIncidenceCoordinates n =>
      ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))) :=
    hdet.mul hdensity
  rw [ginibreIncidenceLebesgueMeasure_eq_volume]
  calc
    (∫⁻ q : GinibreIncidenceCoordinates n,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))) =
      ∫⁻ y : Fin n → ℝ, ∫⁻ u : GinibreIncidenceNuisance n,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock (u, y) -
          ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y)))) := by
      exact lintegral_prod_symm' _ hfull
    _ = ∫⁻ y : Fin n → ℝ,
        ENNReal.ofReal (W y) *
          ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      apply lintegral_congr
      intro y
      calc
        (∫⁻ u : GinibreIncidenceNuisance n,
          ENNReal.ofReal |(ginibreIncidenceDeflatedBlock (u, y) -
            ginibreIncidenceEigenvalue (u, y) • (1 : RSqMat n)).det| *
            ENNReal.ofReal (realGinibreDensityReal (n + 1)
              (ginibreCoordinatesFinMatrix (ginibreIncidenceChart (u, y))))) =
            ∫⁻ u : GinibreIncidenceNuisance n,
              ENNReal.ofReal
                (|(ginibreIncidenceDeflatedBlock (u, y) -
                    ginibreIncidenceEigenvalue (u, y) •
                      (1 : RSqMat n)).det| *
                  realGinibreDensityReal (n + 1)
                    (ginibreCoordinatesFinMatrix
                      (ginibreIncidenceChart (u, y)))) := by
          apply lintegral_congr
          intro u
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
        _ = ENNReal.ofReal (W y) *
              ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
                realGinibreAbsoluteCharacteristicMomentLIntegral n := by
          exact lintegral_ginibreFixedFiber n y
    _ = (∫⁻ y : Fin n → ℝ, ENNReal.ofReal (W y)) *
          (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            realGinibreAbsoluteCharacteristicMomentLIntegral n) := by
      simp_rw [mul_assoc]
      exact lintegral_mul_const'' _ hW.ennreal_ofReal.aemeasurable
    _ = ENNReal.ofReal (∫ y : Fin n → ℝ, W y) *
          (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            realGinibreAbsoluteCharacteristicMomentLIntegral n) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_ginibreProjectiveWeight n)
        (ae_of_all _ fun y => Real.rpow_nonneg (by positivity) _)]
    _ = ENNReal.ofReal (ginibreCorollary31Factor (n + 1)) *
          realGinibreAbsoluteCharacteristicMomentLIntegral n := by
      rw [show ENNReal.ofReal (∫ y : Fin n → ℝ, W y) *
            (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
              realGinibreAbsoluteCharacteristicMomentLIntegral n) =
          (ENNReal.ofReal ((gaussianPDFReal 0 1 0) ^ n) *
            ENNReal.ofReal (∫ y : Fin n → ℝ, W y)) *
              realGinibreAbsoluteCharacteristicMomentLIntegral n by ac_rfl]
      rw [← ENNReal.ofReal_mul
        (pow_nonneg (gaussianPDFReal_nonneg 0 1 0) n)]
      rw [show (∫ y : Fin n → ℝ, W y) =
          ∫ y : Fin n → ℝ,
            (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2)) by rfl]
      rw [gaussianZeroPow_mul_integral_ginibreProjectiveWeight]

/-- `ENNReal` form of the exact Corollary 3.1 bridge. -/
theorem ofReal_expectedRealEigenvalueCount_succ_eq_corollary31Factor_mul_momentLIntegral
    (n : ℕ) :
    ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) =
      ENNReal.ofReal (ginibreCorollary31Factor (n + 1)) *
        realGinibreAbsoluteCharacteristicMomentLIntegral n := by
  calc
    ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) =
        ∫⁻ q : GinibreIncidenceCoordinates n,
          ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
            ENNReal.ofReal (realGinibreDensityReal (n + 1)
              (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))
          ∂ginibreIncidenceLebesgueMeasure n :=
      (lintegral_ginibreIncidence_gaussian_eq_expected n).symm
    _ = _ :=
      lintegral_ginibreIncidence_gaussian_eq_corollary31Factor_mul_momentLIntegral n

/-- The unconditional real-valued Corollary 3.1 identity. -/
theorem expectedRealEigenvalueCount_succ_eq_corollary31Factor_mul_moment
    (n : ℕ) :
    expectedRealEigenvalueCount (n + 1) =
      ginibreCorollary31Factor (n + 1) *
        realGinibreAbsoluteCharacteristicMoment n := by
  have hexpected : 0 ≤ expectedRealEigenvalueCount (n + 1) := by
    unfold expectedRealEigenvalueCount
    exact integral_nonneg fun A => Nat.cast_nonneg _
  have hfactor : 0 ≤ ginibreCorollary31Factor (n + 1) := by
    unfold ginibreCorollary31Factor
    exact div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (le_of_lt (Real.Gamma_pos_of_pos (by positivity))))
  have h := congrArg ENNReal.toReal
    (ofReal_expectedRealEigenvalueCount_succ_eq_corollary31Factor_mul_momentLIntegral n)
  rw [ENNReal.toReal_ofReal hexpected, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hfactor,
    ← realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral] at h
  exact h

end NumStability

end

noncomputable section

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory Set Filter

open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Frobenius

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

/-- The one-root signed moment left after the first incidence transfer. -/
def ginibreSignedOneRootMoment (n : ℕ) : ℝ :=
  ∫ p : RSqMat n × ℝ,
    (p.1 - p.2 • (1 : RSqMat n)).det *
      ginibreAlternatingCount (realEigenvalueBelowCount p)
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

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

/-- The signed two-root slice at a fixed external spectral parameter `x`. -/
def ginibreSignedTwoRootSlice (m : ℕ) (x : ℝ) : ℝ :=
  ∫ p : RSqMat m × ℝ,
    if p.2 < x then
      (p.2 - x) *
        (p.1 - p.2 • (1 : RSqMat m)).det *
        (p.1 - x • (1 : RSqMat m)).det
    else 0
    ∂(realGinibreMeasure m).prod (gaussianReal 0 1)

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

end NumStability

end
