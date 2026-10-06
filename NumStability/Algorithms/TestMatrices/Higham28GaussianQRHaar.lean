import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalHaar
import NumStability.Algorithms.QR.GramSchmidt
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Higham Chapter 28: Gaussian QR produces Haar orthogonal matrices

This file formalizes the independent Gaussian-QR generator stated on printed
p. 517.  For a square matrix whose entries are iid `N(0, σ²)`, with `σ ≠ 0`,
the `Q` factor from the exact modified Gram--Schmidt QR factorization with
positive diagonal `R` has normalized Haar law on the real orthogonal group.

The proof derives almost-sure nonsingularity from absolute continuity, proves
left-orthogonal invariance of the matrix law and equivariance/measurability of
the computed QR map, and identifies its pushforward by Haar uniqueness.  The
orthogonal-valued map is totalized by the identity on the singular null set.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace

theorem standardGaussianVectorMeasure_eq_withDensity_volume (n : ℕ) :
    standardGaussianVectorMeasure n =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i : Fin n, gaussianPDFReal 0 1 (x i))) := by
  have h := MeasureTheory.Measure.pi_withDensity_ofReal
    (fun _ : Fin n => volume)
    (fun _ : Fin n => gaussianPDFReal 0 1)
    (fun _ => integrable_gaussianPDFReal 0 1)
    (fun _ => gaussianPDFReal_nonneg 0 1)
  simpa [standardGaussianVectorMeasure, gaussianReal_of_var_ne_zero,
    gaussianPDF, volume_pi] using h

theorem standardGaussianVectorMeasure_absolutelyContinuous_volume (n : ℕ) :
    standardGaussianVectorMeasure n ≪ (volume : Measure (Fin n → ℝ)) := by
  rw [standardGaussianVectorMeasure_eq_withDensity_volume]
  exact withDensity_absolutelyContinuous _ _

theorem standardGaussianVectorMeasure_submodule_eq_zero (n : ℕ)
    (s : Submodule ℝ (Fin n → ℝ)) (hs : s ≠ ⊤) :
    standardGaussianVectorMeasure n s = 0 := by
  exact standardGaussianVectorMeasure_absolutelyContinuous_volume n
    (Measure.addHaar_submodule (volume : Measure (Fin n → ℝ)) s hs)

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

/-- The iid standard-Gaussian square-matrix law, grouped by columns. -/
noncomputable def gaussianColumnMatrixMeasure (n : ℕ) : Measure (RSqMat n) :=
  (Measure.pi (fun _ : Fin n => standardGaussianVectorMeasure n)).map
    gsColumnsToMatrix

theorem measurable_gsColumnsToMatrix (n : ℕ) :
    Measurable (@gsColumnsToMatrix n n) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply i).comp (measurable_pi_apply j)

instance gaussianColumnMatrixMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianColumnMatrixMeasure n) := by
  unfold gaussianColumnMatrixMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_gsColumnsToMatrix n).aemeasurable

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

def orthogonalLeftActionColumns (n : ℕ) (U : RealOrthogonalGroup n)
    (v : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j => Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) (v j)

theorem measurable_orthogonalLeftActionColumns (n : ℕ)
    (U : RealOrthogonalGroup n) :
    Measurable (orthogonalLeftActionColumns n U) := by
  unfold orthogonalLeftActionColumns Matrix.mulVec dotProduct
  fun_prop

theorem standardGaussianColumnsMeasure_map_orthogonalLeftAction (n : ℕ)
    (U : RealOrthogonalGroup n) :
    (Measure.pi (fun _ : Fin n => standardGaussianVectorMeasure n)).map
        (orthogonalLeftActionColumns n U) =
      Measure.pi (fun _ : Fin n => standardGaussianVectorMeasure n) := by
  have hcol : ∀ j : Fin n,
      MeasurePreserving
        (fun x : Fin n → ℝ =>
          Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) x)
        (standardGaussianVectorMeasure n)
        (standardGaussianVectorMeasure n) := by
    intro j
    exact ⟨by fun_prop,
      standardGaussianVectorMeasure_map_orthogonalGroup n U⟩
  have hpi := measurePreserving_pi
    (fun _ : Fin n => standardGaussianVectorMeasure n)
    (fun _ : Fin n => standardGaussianVectorMeasure n) hcol
  exact hpi.map_eq

def orthogonalLeftMulMatrix (n : ℕ) (U : RealOrthogonalGroup n)
    (A : RSqMat n) : RSqMat n :=
  fun i j => ∑ k : Fin n, (U : Matrix (Fin n) (Fin n) ℝ) i k * A k j

theorem measurable_orthogonalLeftMulMatrix (n : ℕ)
    (U : RealOrthogonalGroup n) :
    Measurable (orthogonalLeftMulMatrix n U) := by
  unfold orthogonalLeftMulMatrix
  fun_prop

theorem orthogonalLeftMulMatrix_gsColumnsToMatrix (n : ℕ)
    (U : RealOrthogonalGroup n) (v : Fin n → Fin n → ℝ) :
    orthogonalLeftMulMatrix n U (gsColumnsToMatrix v) =
      gsColumnsToMatrix (orthogonalLeftActionColumns n U v) := by
  rfl

theorem gaussianColumnMatrixMeasure_map_orthogonalLeftMul (n : ℕ)
    (U : RealOrthogonalGroup n) :
    (gaussianColumnMatrixMeasure n).map (orthogonalLeftMulMatrix n U) =
      gaussianColumnMatrixMeasure n := by
  unfold gaussianColumnMatrixMeasure
  rw [Measure.map_map (measurable_orthogonalLeftMulMatrix n U)
    (measurable_gsColumnsToMatrix n)]
  have hfun : orthogonalLeftMulMatrix n U ∘ gsColumnsToMatrix =
      gsColumnsToMatrix ∘ orthogonalLeftActionColumns n U := by
    funext v
    exact orthogonalLeftMulMatrix_gsColumnsToMatrix n U v
  rw [hfun]
  let μ := Measure.pi (fun _ : Fin n => standardGaussianVectorMeasure n)
  calc
    Measure.map (gsColumnsToMatrix ∘ orthogonalLeftActionColumns n U) μ =
        Measure.map gsColumnsToMatrix
          (Measure.map (orthogonalLeftActionColumns n U) μ) :=
      (Measure.map_map (μ := μ)
        (measurable_gsColumnsToMatrix n)
        (measurable_orthogonalLeftActionColumns n U)).symm
    _ = Measure.map gsColumnsToMatrix μ := by
      rw [standardGaussianColumnsMeasure_map_orthogonalLeftAction]

theorem gsDot_orthogonalGroup_mulVec (n : ℕ)
    (U : RealOrthogonalGroup n) (x y : Fin n → ℝ) :
    gsDot (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) x)
        (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) y) =
      gsDot x y := by
  let M : Matrix (Fin n) (Fin n) ℝ := U
  have hM : M.transpose * M = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property
  change dotProduct (M.mulVec x) (M.mulVec y) = dotProduct x y
  calc
    dotProduct (M.mulVec x) (M.mulVec y) =
        dotProduct (Matrix.vecMul x M.transpose) (M.mulVec y) := by
      rw [Matrix.vecMul_transpose]
    _ = dotProduct x (M.transpose.mulVec (M.mulVec y)) :=
      (Matrix.dotProduct_mulVec x M.transpose (M.mulVec y)).symm
    _ = dotProduct x ((M.transpose * M).mulVec y) := by
      rw [Matrix.mulVec_mulVec]
    _ = dotProduct x y := by simp [hM]

theorem gsColumnNorm2_orthogonalGroup_mulVec (n : ℕ)
    (U : RealOrthogonalGroup n) (x : Fin n → ℝ) :
    gsColumnNorm2
        (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) x) =
      gsColumnNorm2 x := by
  unfold gsColumnNorm2 vecNorm2 vecNorm2Sq
  congr 1
  simpa [gsDot, pow_two] using gsDot_orthogonalGroup_mulVec n U x x

theorem orthogonalGroup_mulVec_gsNormalize (n : ℕ)
    (U : RealOrthogonalGroup n) (x : Fin n → ℝ) (r : ℝ) :
    Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) (gsNormalize x r) =
      gsNormalize
        (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) x) r := by
  ext i
  unfold Matrix.mulVec dotProduct gsNormalize
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem orthogonalGroup_mulVec_gsProjectAway (n : ℕ)
    (U : RealOrthogonalGroup n) (x q : Fin n → ℝ) :
    Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) (gsProjectAway x q) =
      gsProjectAway
        (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) x)
        (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) q) := by
  unfold gsProjectAway
  rw [gsDot_orthogonalGroup_mulVec n U q x]
  ext i
  unfold Matrix.mulVec dotProduct
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem modifiedGramSchmidtStep_orthogonalLeftAction (n : ℕ)
    (U : RealOrthogonalGroup n) (V : Fin n → Fin n → ℝ) (k : Fin n) :
    modifiedGramSchmidtStep (orthogonalLeftActionColumns n U V) k =
      orthogonalLeftActionColumns n U (modifiedGramSchmidtStep V k) := by
  funext j
  by_cases hkj : k < j
  · simp only [modifiedGramSchmidtStep, hkj, dite_true,
      orthogonalLeftActionColumns]
    rw [gsColumnNorm2_orthogonalGroup_mulVec,
      ← orthogonalGroup_mulVec_gsNormalize,
      ← orthogonalGroup_mulVec_gsProjectAway]
  · simp [modifiedGramSchmidtStep, orthogonalLeftActionColumns, hkj]

theorem modifiedGramSchmidtVectors_orthogonalLeftMul (n : ℕ)
    (U : RealOrthogonalGroup n) (A : RSqMat n) (t : ℕ) :
    modifiedGramSchmidtVectors (orthogonalLeftMulMatrix n U A) t =
      orthogonalLeftActionColumns n U (modifiedGramSchmidtVectors A t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      by_cases ht : t < n
      · simp only [modifiedGramSchmidtVectors, ht, dite_true]
        rw [ih, modifiedGramSchmidtStep_orthogonalLeftAction]
      · simp only [modifiedGramSchmidtVectors, ht, dite_false, ih]

theorem modifiedGramSchmidtQ_orthogonalLeftMul (n : ℕ)
    (U : RealOrthogonalGroup n) (A : RSqMat n) :
    modifiedGramSchmidtQ (orthogonalLeftMulMatrix n U A) =
      orthogonalLeftMulMatrix n U (modifiedGramSchmidtQ A) := by
  ext i j
  unfold modifiedGramSchmidtQ
  have hv := congrFun
    (modifiedGramSchmidtVectors_orthogonalLeftMul n U A j.val) j
  rw [hv]
  change gsNormalize
      (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ)
        (modifiedGramSchmidtVectors A j.val j))
      (gsColumnNorm2
        (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ)
          (modifiedGramSchmidtVectors A j.val j))) i = _
  rw [gsColumnNorm2_orthogonalGroup_mulVec]
  change gsNormalize
      (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ)
        (modifiedGramSchmidtVectors A j.val j))
      (gsColumnNorm2 (modifiedGramSchmidtVectors A j.val j)) i =
    Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ)
      (gsNormalize (modifiedGramSchmidtVectors A j.val j)
        (gsColumnNorm2 (modifiedGramSchmidtVectors A j.val j))) i
  have hnorm := orthogonalGroup_mulVec_gsNormalize n U
    (modifiedGramSchmidtVectors A j.val j)
    (gsColumnNorm2 (modifiedGramSchmidtVectors A j.val j))
  exact congrFun hnorm i |>.symm

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

theorem continuous_matrixDet (n : ℕ) :
    Continuous (fun A : RSqMat n => (Matrix.of A).det) := by
  have hmat : Continuous
      (fun A : RSqMat n => (fun i j => A i j : Matrix (Fin n) (Fin n) ℝ)) := by
    fun_prop
  simpa only [] using hmat.matrix_det

theorem measurable_matrixDet (n : ℕ) :
    Measurable (fun A : RSqMat n => (Matrix.of A).det) :=
  (continuous_matrixDet n).measurable

theorem rectMatMulVec_injective_of_det_ne_zero {n : ℕ} (A : RSqMat n)
    (hdet : (Matrix.of A).det ≠ 0) :
    Function.Injective (rectMatMulVec A) := by
  have hunitDet : IsUnit (Matrix.of A).det := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit (Matrix.of A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunitDet
  have hinj : Function.Injective (Matrix.of A).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa [rectMatMulVec, Matrix.mulVec, dotProduct, Matrix.of] using hinj

theorem modifiedGramSchmidtQ_mem_orthogonalGroup_of_det_ne_zero {n : ℕ}
    (A : RSqMat n) (hdet : (Matrix.of A).det ≠ 0) :
    Matrix.of (modifiedGramSchmidtQ A) ∈
      Matrix.orthogonalGroup (Fin n) ℝ := by
  have hinj := rectMatMulVec_injective_of_det_ne_zero A hdet
  have hdiag : ∀ k : Fin n,
      gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k) ≠ 0 :=
    modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective A hinj
  have hcols := modifiedGramSchmidtQ_orthonormal_columns A hdiag
  rw [Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ]
  ext i j
  simpa [GramSchmidtOrthonormalColumns, rectangularGram, matMulRect,
    finiteTranspose, idMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply] using hcols i j

noncomputable def gaussianQRQMatrix (n : ℕ) (A : RSqMat n) : RSqMat n :=
  if (Matrix.of A).det = 0 then (1 : Matrix (Fin n) (Fin n) ℝ)
  else modifiedGramSchmidtQ A

theorem measurable_gaussianQRQMatrix (n : ℕ) :
    Measurable (gaussianQRQMatrix n) := by
  unfold gaussianQRQMatrix
  apply Measurable.ite
  · exact (measurable_matrixDet n) (measurableSet_singleton (0 : ℝ))
  · exact measurable_const
  · exact measurable_modifiedGramSchmidtQ n

theorem gaussianQRQMatrix_mem_orthogonalGroup (n : ℕ) (A : RSqMat n) :
    Matrix.of (gaussianQRQMatrix n A) ∈
      Matrix.orthogonalGroup (Fin n) ℝ := by
  by_cases hdet : (Matrix.of A).det = 0
  · rw [gaussianQRQMatrix, if_pos hdet]
    rw [Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ]
    change (1 : Matrix (Fin n) (Fin n) ℝ).transpose * 1 = 1
    simp
  · rw [gaussianQRQMatrix, if_neg hdet]
    exact modifiedGramSchmidtQ_mem_orthogonalGroup_of_det_ne_zero A hdet

noncomputable def gaussianQRQ (n : ℕ) (A : RSqMat n) :
    RealOrthogonalGroup n :=
  ⟨Matrix.of (gaussianQRQMatrix n A),
    gaussianQRQMatrix_mem_orthogonalGroup n A⟩

theorem measurable_gaussianQRQ (n : ℕ) : Measurable (gaussianQRQ n) := by
  apply Measurable.subtype_mk
  exact measurable_gaussianQRQMatrix n

/-- Nonsingularity supplies the exact square MGS factorization, its
upper-triangular `R`, and the positive diagonal convention that makes the QR
factor unique. -/
theorem modifiedGramSchmidt_positiveDiagonalQR_of_det_ne_zero {n : ℕ}
    (A : RSqMat n) (hdet : (Matrix.of A).det ≠ 0) :
    A = matMulRect n n n (modifiedGramSchmidtQ A)
          (modifiedGramSchmidtR A) ∧
      IsUpperTrapezoidal n n (modifiedGramSchmidtR A) ∧
      ∀ k : Fin n, 0 < modifiedGramSchmidtR A k k := by
  have hinj := rectMatMulVec_injective_of_det_ne_zero A hdet
  have hdiag : ∀ k : Fin n,
      gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k) ≠ 0 :=
    modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective A hinj
  refine ⟨modifiedGramSchmidt_exact_factorization A hdiag,
    modifiedGramSchmidtR_upper_trapezoidal A, ?_⟩
  intro k
  rw [modifiedGramSchmidtR_diag]
  have hnonneg : 0 ≤
      gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k) := by
    simpa [gsColumnNorm2] using
      vecNorm2_nonneg (modifiedGramSchmidtVectors A k.val k)
  exact lt_of_le_of_ne hnonneg (Ne.symm (hdiag k))

theorem det_orthogonalLeftMulMatrix_ne_zero {n : ℕ}
    (U : RealOrthogonalGroup n) (A : RSqMat n)
    (hdet : (Matrix.of A).det ≠ 0) :
    (Matrix.of (orthogonalLeftMulMatrix n U A)).det ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := U
  have hMTM : M.transpose * M = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property
  have hMdet : M.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hMTM
  change (M * Matrix.of A).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hMdet hdet

theorem gaussianQRQ_orthogonalLeftMul_of_det_ne_zero {n : ℕ}
    (U : RealOrthogonalGroup n) (A : RSqMat n)
    (hdet : (Matrix.of A).det ≠ 0) :
    gaussianQRQ n (orthogonalLeftMulMatrix n U A) =
      U * gaussianQRQ n A := by
  have hdetUA := det_orthogonalLeftMulMatrix_ne_zero U A hdet
  apply Subtype.ext
  change Matrix.of
      (gaussianQRQMatrix n (orthogonalLeftMulMatrix n U A)) =
    (U : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.of (gaussianQRQMatrix n A)
  rw [gaussianQRQMatrix, if_neg hdetUA, gaussianQRQMatrix, if_neg hdet]
  simpa [orthogonalLeftMulMatrix, Matrix.mul_apply] using congrArg Matrix.of
    (modifiedGramSchmidtQ_orthogonalLeftMul n U A)

theorem gaussianQRQ_orthogonalLeftMul_ae (n : ℕ)
    (U : RealOrthogonalGroup n) :
    ∀ᵐ A : RSqMat n ∂gaussianColumnMatrixMeasure n,
      gaussianQRQ n (orthogonalLeftMulMatrix n U A) =
        U * gaussianQRQ n A := by
  filter_upwards [gaussianColumnMatrixMeasure_det_ne_zero_ae n] with A hdet
  exact gaussianQRQ_orthogonalLeftMul_of_det_ne_zero U A hdet

/-- Distribution of the positive-diagonal QR `Q` factor of an iid standard
Gaussian square matrix. -/
noncomputable def gaussianQRQLaw (n : ℕ) :
    Measure (RealOrthogonalGroup n) :=
  (gaussianColumnMatrixMeasure n).map (gaussianQRQ n)

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

/-! ## Arbitrary nonzero Gaussian scale -/

def gaussianScaleVector (n : ℕ) (σ : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => σ * x i

def gaussianScaleMatrix (n : ℕ) (σ : ℝ) (A : RSqMat n) : RSqMat n :=
  fun i j => σ * A i j

def gaussianScaleVariance (σ : ℝ) : NNReal :=
  ⟨σ ^ 2, sq_nonneg σ⟩

theorem measurable_gaussianScaleVector (n : ℕ) (σ : ℝ) :
    Measurable (gaussianScaleVector n σ) := by
  unfold gaussianScaleVector
  fun_prop

theorem measurable_gaussianScaleMatrix (n : ℕ) (σ : ℝ) :
    Measurable (gaussianScaleMatrix n σ) := by
  unfold gaussianScaleMatrix
  fun_prop

theorem standardGaussianVectorMeasure_map_scale (n : ℕ) (σ : ℝ) :
    (standardGaussianVectorMeasure n).map (gaussianScaleVector n σ) =
      Measure.pi (fun _ : Fin n =>
        gaussianReal 0 (gaussianScaleVariance σ)) := by
  have hcoord : ∀ i : Fin n,
      MeasurePreserving (fun x : ℝ => σ * x)
        (gaussianReal 0 1)
        (gaussianReal 0 (gaussianScaleVariance σ)) := by
    intro i
    refine ⟨by fun_prop, ?_⟩
    simpa [gaussianScaleVariance] using
      (gaussianReal_map_const_mul (μ := 0) (v := (1 : NNReal)) σ)
  simpa [standardGaussianVectorMeasure, gaussianScaleVector] using
    (measurePreserving_pi
      (fun _ : Fin n => gaussianReal 0 1)
      (fun _ : Fin n =>
        gaussianReal 0 (gaussianScaleVariance σ))
      hcoord).map_eq

/-- An iid `N(0, σ²)` square-matrix law, grouped by columns. -/
noncomputable def gaussianColumnMatrixMeasureOfScale (n : ℕ) (σ : ℝ) :
    Measure (RSqMat n) :=
  (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n =>
      gaussianReal 0 (gaussianScaleVariance σ)))).map
        gsColumnsToMatrix

instance gaussianColumnMatrixMeasureOfScale_isProbabilityMeasure
    (n : ℕ) (σ : ℝ) :
    IsProbabilityMeasure (gaussianColumnMatrixMeasureOfScale n σ) := by
  unfold gaussianColumnMatrixMeasureOfScale
  exact Measure.isProbabilityMeasure_map
    (measurable_gsColumnsToMatrix n).aemeasurable

theorem gaussianColumnMatrixMeasureOfScale_eq_map_scale
    (n : ℕ) (σ : ℝ) :
    gaussianColumnMatrixMeasureOfScale n σ =
      (gaussianColumnMatrixMeasure n).map (gaussianScaleMatrix n σ) := by
  have hcol : ∀ j : Fin n,
      MeasurePreserving (gaussianScaleVector n σ)
        (standardGaussianVectorMeasure n)
        (Measure.pi (fun _ : Fin n =>
          gaussianReal 0 (gaussianScaleVariance σ))) := by
    intro j
    exact ⟨measurable_gaussianScaleVector n σ,
      standardGaussianVectorMeasure_map_scale n σ⟩
  have hcols := (measurePreserving_pi
    (fun _ : Fin n => standardGaussianVectorMeasure n)
    (fun _ : Fin n => Measure.pi (fun _ : Fin n =>
      gaussianReal 0 (gaussianScaleVariance σ))) hcol).map_eq
  have hscaleColumns : Measurable
      (fun v : Fin n → Fin n → ℝ =>
        fun j => gaussianScaleVector n σ (v j)) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_gaussianScaleVector n σ).comp (measurable_pi_apply j)
  unfold gaussianColumnMatrixMeasureOfScale gaussianColumnMatrixMeasure
  rw [Measure.map_map (measurable_gaussianScaleMatrix n σ)
    (measurable_gsColumnsToMatrix n)]
  rw [show gaussianScaleMatrix n σ ∘ gsColumnsToMatrix =
      gsColumnsToMatrix ∘ (fun v : Fin n → Fin n → ℝ =>
        fun j => gaussianScaleVector n σ (v j)) by rfl]
  rw [← hcols]
  exact Measure.map_map (measurable_gsColumnsToMatrix n) hscaleColumns

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

theorem gaussianColumnMatrixMeasureOfScale_map_orthogonalLeftMul
    (n : ℕ) (σ : ℝ) (U : RealOrthogonalGroup n) :
    (gaussianColumnMatrixMeasureOfScale n σ).map
        (orthogonalLeftMulMatrix n U) =
      gaussianColumnMatrixMeasureOfScale n σ := by
  rw [gaussianColumnMatrixMeasureOfScale_eq_map_scale]
  rw [Measure.map_map (measurable_orthogonalLeftMulMatrix n U)
    (measurable_gaussianScaleMatrix n σ)]
  rw [show orthogonalLeftMulMatrix n U ∘ gaussianScaleMatrix n σ =
      gaussianScaleMatrix n σ ∘ orthogonalLeftMulMatrix n U by
    funext A
    ext i j
    unfold orthogonalLeftMulMatrix gaussianScaleMatrix
    change (∑ k : Fin n,
      (U : Matrix (Fin n) (Fin n) ℝ) i k * (σ * A k j)) =
      σ * ∑ k : Fin n, (U : Matrix (Fin n) (Fin n) ℝ) i k * A k j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  rw [← Measure.map_map (measurable_gaussianScaleMatrix n σ)
    (measurable_orthogonalLeftMulMatrix n U)]
  rw [gaussianColumnMatrixMeasure_map_orthogonalLeftMul]

/-- Distribution of the positive-diagonal QR `Q` factor under the iid
`N(0, σ²)` matrix law. -/
noncomputable def gaussianQRQLawOfScale (n : ℕ) (σ : ℝ) :
    Measure (RealOrthogonalGroup n) :=
  (gaussianColumnMatrixMeasureOfScale n σ).map (gaussianQRQ n)

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
