import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations
import NumStability.Source.Higham.Chapter28.Section03.Theorem01.StewartHaar.GaussianQRHaar
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GaussianQRHaar under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set

open scoped BigOperators ENNReal RealInnerProductSpace

private theorem span_range_ne_top_of_linearIndependent_of_card_lt
    {n k : ℕ} {v : Fin k → (Fin n → ℝ)}
    (hv : LinearIndependent ℝ v) (hk : k < n) :
    Submodule.span ℝ (Set.range v) ≠ ⊤ := by
  intro htop
  have hfin := finrank_span_eq_card hv
  rw [htop] at hfin
  simp at hfin
  omega

private theorem measurableSet_linearIndependent_fin_cons (n k : ℕ) :
    MeasurableSet
      {p : (Fin n → ℝ) × (Fin k → Fin n → ℝ) |
        LinearIndependent ℝ (Fin.cons p.1 p.2)} := by
  apply isOpen_setOf_linearIndependent.measurableSet.preimage
  apply measurable_pi_lambda
  intro i
  refine Fin.cases measurable_fst (fun j => ?_) i
  exact (measurable_pi_apply j).comp measurable_snd

theorem ae_linearIndependent_standardGaussianColumns_aux (n : ℕ) :
    ∀ k : ℕ, k ≤ n →
      ∀ᵐ v : Fin k → (Fin n → ℝ)
        ∂Measure.pi (fun _ : Fin k => standardGaussianVectorMeasure n),
        LinearIndependent ℝ v := by
  intro k hk
  induction k with
  | zero =>
      exact ae_of_all _ fun v => by
        exact linearIndependent_empty_type
  | succ k ih =>
      let μ : Measure (Fin n → ℝ) := standardGaussianVectorMeasure n
      let ν : Measure (Fin k → Fin n → ℝ) :=
        Measure.pi (fun _ : Fin k => μ)
      have hklt : k < n := Nat.lt_of_succ_le hk
      have htail : ∀ᵐ v : Fin k → (Fin n → ℝ) ∂ν,
          LinearIndependent ℝ v := by
        simpa [ν, μ] using ih (Nat.le_of_succ_le hk)
      have hnested : ∀ᵐ v : Fin k → (Fin n → ℝ) ∂ν,
          ∀ᵐ x : Fin n → ℝ ∂μ,
            LinearIndependent ℝ (Fin.cons x v) := by
        filter_upwards [htail] with v hv
        have hspan : Submodule.span ℝ (Set.range v) ≠ ⊤ :=
          span_range_ne_top_of_linearIndependent_of_card_lt hv hklt
        have hx : ∀ᵐ x : Fin n → ℝ ∂μ,
            x ∉ Submodule.span ℝ (Set.range v) := by
          exact compl_mem_ae_iff.2 (by
            simpa [μ] using
              standardGaussianVectorMeasure_submodule_eq_zero n
                (Submodule.span ℝ (Set.range v)) hspan)
        filter_upwards [hx] with x hx
        exact (linearIndependent_fin_cons).2 ⟨hv, hx⟩
      have hmeas := measurableSet_linearIndependent_fin_cons n k
      have houter : ∀ᵐ x : Fin n → ℝ ∂μ,
          ∀ᵐ v : Fin k → (Fin n → ℝ) ∂ν,
            LinearIndependent ℝ (Fin.cons x v) :=
        (Measure.ae_ae_comm hmeas).2 hnested
      have hpair : ∀ᵐ p : (Fin n → ℝ) × (Fin k → Fin n → ℝ)
          ∂μ.prod ν, LinearIndependent ℝ (Fin.cons p.1 p.2) :=
        (Measure.ae_prod_iff_ae_ae hmeas).2 houter
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => (Fin n → ℝ)) (0 : Fin (k + 1))
      have hmp : MeasurePreserving e
          (Measure.pi (fun _ : Fin (k + 1) => μ)) (μ.prod ν) := by
        simpa [e, ν] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (k + 1) => μ) (0 : Fin (k + 1)))
      have hpull := hmp.quasiMeasurePreserving.ae hpair
      simpa [μ, e, MeasurableEquiv.piFinSuccAbove,
        Fin.insertNthEquiv, Fin.cons_self_tail] using hpull

theorem ae_linearIndependent_standardGaussianColumns (n : ℕ) :
    ∀ᵐ v : Fin n → (Fin n → ℝ)
      ∂Measure.pi (fun _ : Fin n => standardGaussianVectorMeasure n),
      LinearIndependent ℝ v :=
  ae_linearIndependent_standardGaussianColumns_aux n n le_rfl

private theorem det_gsColumnsToMatrix_ne_zero_of_linearIndependent
    {n : ℕ} {v : Fin n → (Fin n → ℝ)}
    (hv : LinearIndependent ℝ v) :
    (Matrix.of (gsColumnsToMatrix v)).det ≠ 0 := by
  have hcols : LinearIndependent ℝ (Matrix.of (gsColumnsToMatrix v)).col := by
    simpa [Matrix.col, gsColumnsToMatrix] using hv
  have hinj : Function.Injective (Matrix.of (gsColumnsToMatrix v)).mulVec :=
    Matrix.mulVec_injective_iff.mpr hcols
  have hunit : IsUnit (Matrix.of (gsColumnsToMatrix v)) :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

theorem gaussianColumnMatrixMeasure_det_ne_zero_ae (n : ℕ) :
    ∀ᵐ A : RSqMat n ∂gaussianColumnMatrixMeasure n,
      (Matrix.of A).det ≠ 0 := by
  have hmeas : MeasurableSet {A : RSqMat n | (Matrix.of A).det ≠ 0} := by
    apply IsOpen.measurableSet
    have hdet : Continuous (fun A : RSqMat n => (Matrix.of A).det) := by
      have hmat : Continuous
          (fun A : RSqMat n => (fun i j => A i j : Matrix (Fin n) (Fin n) ℝ)) := by
        fun_prop
      simpa only [] using hmat.matrix_det
    exact (isClosed_singleton.preimage hdet).isOpen_compl
  unfold gaussianColumnMatrixMeasure
  apply (ae_map_iff (measurable_gsColumnsToMatrix n).aemeasurable hmeas).2
  filter_upwards [ae_linearIndependent_standardGaussianColumns n] with v hv
  exact det_gsColumnsToMatrix_ne_zero_of_linearIndependent hv

private theorem measurable_modifiedGramSchmidtVectors_apply (n : ℕ) :
    ∀ (t : ℕ) (j i : Fin n),
      Measurable (fun A : RSqMat n => modifiedGramSchmidtVectors A t j i) := by
  intro t
  induction t with
  | zero =>
      intro j i
      simp only [modifiedGramSchmidtVectors, gsColumn]
      fun_prop
  | succ t ih =>
      intro j i
      by_cases ht : t < n
      · rw [show (fun A : RSqMat n => modifiedGramSchmidtVectors A (t + 1) j i) =
            (fun A => modifiedGramSchmidtStep
              (modifiedGramSchmidtVectors A t) (Fin.mk t ht) j i) by
            funext A
            simp [modifiedGramSchmidtVectors, ht]]
        by_cases hkj : (Fin.mk t ht : Fin n) < j
        · simp only [modifiedGramSchmidtStep, hkj, dite_true,
            gsProjectAway, gsNormalize, gsColumnNorm2, vecNorm2, vecNorm2Sq,
            gsDot]
          have hnorm : Measurable (fun A : RSqMat n =>
              Real.sqrt (∑ r : Fin n,
                modifiedGramSchmidtVectors A t (Fin.mk t ht) r ^ 2)) := by
            apply Measurable.sqrt
            apply Finset.measurable_sum
            intro r hr
            exact (ih (Fin.mk t ht) r).pow_const 2
          have hq (r : Fin n) : Measurable (fun A : RSqMat n =>
              modifiedGramSchmidtVectors A t (Fin.mk t ht) r /
                Real.sqrt (∑ s : Fin n,
                  modifiedGramSchmidtVectors A t (Fin.mk t ht) s ^ 2)) :=
            (ih (Fin.mk t ht) r).div hnorm
          have hdot : Measurable (fun A : RSqMat n =>
              ∑ r : Fin n,
                (modifiedGramSchmidtVectors A t (Fin.mk t ht) r /
                  Real.sqrt (∑ s : Fin n,
                    modifiedGramSchmidtVectors A t (Fin.mk t ht) s ^ 2)) *
                  modifiedGramSchmidtVectors A t j r) := by
            apply Finset.measurable_sum
            intro r hr
            exact (hq r).mul (ih j r)
          exact (ih j i).sub (hdot.mul (hq i))
        · simp only [modifiedGramSchmidtStep, hkj, dite_false]
          exact ih j i
      · rw [show (fun A : RSqMat n => modifiedGramSchmidtVectors A (t + 1) j i) =
            (fun A => modifiedGramSchmidtVectors A t j i) by
            funext A
            simp [modifiedGramSchmidtVectors, ht]]
        exact ih j i

theorem measurable_modifiedGramSchmidtQ (n : ℕ) :
    Measurable (fun A : RSqMat n => modifiedGramSchmidtQ A) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  unfold modifiedGramSchmidtQ gsNormalize gsColumnNorm2 vecNorm2 vecNorm2Sq
  have hnorm : Measurable (fun A : RSqMat n =>
      Real.sqrt (∑ r : Fin n,
        modifiedGramSchmidtVectors A j.val j r ^ 2)) := by
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro r hr
    exact (measurable_modifiedGramSchmidtVectors_apply n j.val j r).pow_const 2
  apply Measurable.div
  · exact measurable_modifiedGramSchmidtVectors_apply n j.val j i
  · exact hnorm

theorem measurable_gaussianQRQMatrix (n : ℕ) :
    Measurable (gaussianQRQMatrix n) := by
  unfold gaussianQRQMatrix
  apply Measurable.ite
  · exact (measurable_matrixDet n) (measurableSet_singleton (0 : ℝ))
  · exact measurable_const
  · exact measurable_modifiedGramSchmidtQ n

theorem measurable_gaussianQRQ (n : ℕ) : Measurable (gaussianQRQ n) := by
  apply Measurable.subtype_mk
  exact measurable_gaussianQRQMatrix n

theorem gaussianQRQ_orthogonalLeftMul_ae (n : ℕ)
    (U : RealOrthogonalGroup n) :
    ∀ᵐ A : RSqMat n ∂gaussianColumnMatrixMeasure n,
      gaussianQRQ n (orthogonalLeftMulMatrix n U A) =
        U * gaussianQRQ n A := by
  filter_upwards [gaussianColumnMatrixMeasure_det_ne_zero_ae n] with A hdet
  exact gaussianQRQ_orthogonalLeftMul_of_det_ne_zero U A hdet

instance gaussianQRQLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianQRQLaw n) := by
  unfold gaussianQRQLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianQRQ n).aemeasurable

instance gaussianQRQLaw_isMulLeftInvariant (n : ℕ) :
    (gaussianQRQLaw n).IsMulLeftInvariant where
  map_mul_left_eq_self U := by
    unfold gaussianQRQLaw
    calc
      Measure.map (fun Q : RealOrthogonalGroup n => U * Q)
          (Measure.map (gaussianQRQ n) (gaussianColumnMatrixMeasure n)) =
          Measure.map ((fun Q : RealOrthogonalGroup n => U * Q) ∘ gaussianQRQ n)
            (gaussianColumnMatrixMeasure n) :=
        Measure.map_map (continuous_const.mul continuous_id).measurable
          (measurable_gaussianQRQ n)
      Measure.map ((fun Q : RealOrthogonalGroup n => U * Q) ∘ gaussianQRQ n)
          (gaussianColumnMatrixMeasure n) =
          Measure.map
            (gaussianQRQ n ∘ orthogonalLeftMulMatrix n U)
            (gaussianColumnMatrixMeasure n) := by
        apply Measure.map_congr
        filter_upwards [gaussianQRQ_orthogonalLeftMul_ae n U] with A hA
        exact hA.symm
      _ = Measure.map (gaussianQRQ n)
          ((gaussianColumnMatrixMeasure n).map
            (orthogonalLeftMulMatrix n U)) := by
        rw [Measure.map_map (measurable_gaussianQRQ n)
          (measurable_orthogonalLeftMulMatrix n U)]
      _ = Measure.map (gaussianQRQ n)
          (gaussianColumnMatrixMeasure n) := by
        rw [gaussianColumnMatrixMeasure_map_orthogonalLeftMul]

instance gaussianQRQLaw_isHaarMeasure (n : ℕ) :
    (gaussianQRQLaw n).IsHaarMeasure := by
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior
    (gaussianQRQLaw n) Set.univ isCompact_univ
    (by simp) (by simp) (by simp)

/-- The positive-diagonal QR factor of an iid standard-Gaussian square matrix
is exactly normalized Haar measure on the real orthogonal group. -/
theorem gaussianQRQLaw_eq_normalizedOrthogonalHaar (n : ℕ) :
    gaussianQRQLaw n = normalizedOrthogonalHaar n :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure
    (gaussianQRQLaw n) (normalizedOrthogonalHaar n)

theorem gaussianColumnMatrixMeasureOfScale_det_ne_zero_ae
    (n : ℕ) (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ᵐ A : RSqMat n ∂gaussianColumnMatrixMeasureOfScale n σ,
      (Matrix.of A).det ≠ 0 := by
  rw [gaussianColumnMatrixMeasureOfScale_eq_map_scale]
  have hmeas : MeasurableSet {A : RSqMat n | (Matrix.of A).det ≠ 0} := by
    exact (isClosed_singleton.preimage (continuous_matrixDet n)).isOpen_compl.measurableSet
  apply (ae_map_iff
    (measurable_gaussianScaleMatrix n σ).aemeasurable hmeas).2
  filter_upwards [gaussianColumnMatrixMeasure_det_ne_zero_ae n] with A hdet
  change (σ • Matrix.of A).det ≠ 0
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hσ) hdet

instance gaussianQRQLawOfScale_isProbabilityMeasure (n : ℕ) (σ : ℝ) :
    IsProbabilityMeasure (gaussianQRQLawOfScale n σ) := by
  unfold gaussianQRQLawOfScale
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianQRQ n).aemeasurable

theorem gaussianQRQLawOfScale_eq_normalizedOrthogonalHaar
    (n : ℕ) (σ : ℝ) (hσ : σ ≠ 0) :
    gaussianQRQLawOfScale n σ = normalizedOrthogonalHaar n := by
  let μ := gaussianQRQLawOfScale n σ
  letI : IsProbabilityMeasure μ :=
    gaussianQRQLawOfScale_isProbabilityMeasure n σ
  haveI : μ.IsMulLeftInvariant := by
    refine ⟨?_⟩
    intro U
    unfold μ gaussianQRQLawOfScale
    calc
      Measure.map (fun Q : RealOrthogonalGroup n => U * Q)
          (Measure.map (gaussianQRQ n)
            (gaussianColumnMatrixMeasureOfScale n σ)) =
          Measure.map ((fun Q : RealOrthogonalGroup n => U * Q) ∘ gaussianQRQ n)
            (gaussianColumnMatrixMeasureOfScale n σ) :=
        Measure.map_map (continuous_const.mul continuous_id).measurable
          (measurable_gaussianQRQ n)
      _ = Measure.map
            (gaussianQRQ n ∘ orthogonalLeftMulMatrix n U)
            (gaussianColumnMatrixMeasureOfScale n σ) := by
        apply Measure.map_congr
        filter_upwards
            [gaussianColumnMatrixMeasureOfScale_det_ne_zero_ae n σ hσ]
            with A hdet
        exact (gaussianQRQ_orthogonalLeftMul_of_det_ne_zero U A hdet).symm
      _ = Measure.map (gaussianQRQ n)
          ((gaussianColumnMatrixMeasureOfScale n σ).map
            (orthogonalLeftMulMatrix n U)) := by
        rw [Measure.map_map (measurable_gaussianQRQ n)
          (measurable_orthogonalLeftMulMatrix n U)]
      _ = Measure.map (gaussianQRQ n)
          (gaussianColumnMatrixMeasureOfScale n σ) := by
        rw [gaussianColumnMatrixMeasureOfScale_map_orthogonalLeftMul]
  letI : μ.IsHaarMeasure := by
    exact Measure.isHaarMeasure_of_isCompact_nonempty_interior μ
      Set.univ isCompact_univ (by simp) (by simp) (by simp)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ
    (normalizedOrthogonalHaar n)

end NumStability
