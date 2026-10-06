import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Haar.HomogeneousSpaceUniqueness
import NumStability.Analysis.TestMatrices.Gaussian.GaussianOrthogonal
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalHaar
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreMeasure

/-!
# Chapter28 Section03 Theorem01 StewartHaar GaussianQRHaar

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GaussianQRHaar` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
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

/-- Distribution of the positive-diagonal QR `Q` factor of an iid standard
Gaussian square matrix. -/
noncomputable def gaussianQRQLaw (n : ℕ) :
    Measure (RealOrthogonalGroup n) :=
  (gaussianColumnMatrixMeasure n).map (gaussianQRQ n)

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

end NumStability
