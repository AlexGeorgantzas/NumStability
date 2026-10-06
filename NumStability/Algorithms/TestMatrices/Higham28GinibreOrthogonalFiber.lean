import NumStability.Algorithms.TestMatrices.Higham28GinibreGaussianBridge
import NumStability.Algorithms.TestMatrices.Higham28GinibreCorollary31Factor
import NumStability.Algorithms.TestMatrices.Higham28GaussianDirection
import NumStability.Algorithms.TestMatrices.Higham28GinibreTraceDensity
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal BigOperators RealInnerProductSpace Matrix.Norms.Frobenius

noncomputable section

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

/-- The leading principal block of a `(n+1)`-square matrix. -/
def ginibreLeadingBlock (n : ℕ) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Q.submatrix Fin.castSucc Fin.castSucc

lemma adjugate_eq_det_smul_transpose_of_isOrthogonal (n : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsOrthogonal n Q) :
    Q.adjugate = Q.det • Q.transpose := by
  have hleft : Q.transpose * Q = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, matTranspose] using hQ.left_inv i j
  calc
    Q.adjugate = 1 * Q.adjugate := by simp
    _ = (Q.transpose * Q) * Q.adjugate := by rw [hleft]
    _ = Q.transpose * (Q * Q.adjugate) := by rw [Matrix.mul_assoc]
    _ = Q.transpose * (Q.det • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
      rw [Matrix.mul_adjugate]
    _ = Q.det • Q.transpose := by simp

lemma abs_det_eq_one_of_isOrthogonal (n : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsOrthogonal n Q) :
    |Q.det| = 1 := by
  have hleft : Q.transpose * Q = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, matTranspose] using hQ.left_inv i j
  have hdet := congrArg Matrix.det hleft
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have habs_sq : |Q.det| * |Q.det| = 1 := by
    rw [← abs_mul, hdet, abs_one]
  nlinarith [abs_nonneg Q.det]

theorem abs_det_ginibreLeadingBlock_eq_abs_lastEntry (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : IsOrthogonal (n + 1) Q) :
    |(ginibreLeadingBlock n Q).det| = |Q (Fin.last n) (Fin.last n)| := by
  have hadj := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      A (Fin.last n) (Fin.last n))
    (adjugate_eq_det_smul_transpose_of_isOrthogonal (n + 1) Q hQ)
  simp only [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last,
    Matrix.smul_apply, smul_eq_mul] at hadj
  have habs := congrArg abs hadj
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow] at habs
  rw [show ginibreLeadingBlock n Q =
      Q.submatrix Fin.castSucc Fin.castSucc from rfl]
  simpa [abs_det_eq_one_of_isOrthogonal (n + 1) Q hQ] using habs

section BlockDeterminant

variable {M Y : Type*}
  [AddCommGroup M] [Module ℝ M]
  [AddCommGroup Y] [Module ℝ Y]

/-- A general block-lower-triangular endomorphism. -/
def LinearMap.lowerBlockDiagonal (D : M →ₗ[ℝ] M) (C : M →ₗ[ℝ] Y)
    (T : Y →ₗ[ℝ] Y) : (M × Y) →ₗ[ℝ] (M × Y) :=
  (D.comp (LinearMap.fst ℝ M Y)).prod
    (C.comp (LinearMap.fst ℝ M Y) + T.comp (LinearMap.snd ℝ M Y))

@[simp] theorem LinearMap.lowerBlockDiagonal_apply
    (D : M →ₗ[ℝ] M) (C : M →ₗ[ℝ] Y) (T : Y →ₗ[ℝ] Y) (p : M × Y) :
    LinearMap.lowerBlockDiagonal D C T p = (D p.1, C p.1 + T p.2) := rfl

theorem LinearMap.det_lowerBlockDiagonal
    [Module.Free ℝ M] [Module.Finite ℝ M]
    [Module.Free ℝ Y] [Module.Finite ℝ Y]
    (D : M →ₗ[ℝ] M) (C : M →ₗ[ℝ] Y) (T : Y →ₗ[ℝ] Y) :
    (LinearMap.lowerBlockDiagonal D C T).det = D.det * T.det := by
  classical
  let bM := Module.Free.chooseBasis ℝ M
  let bY := Module.Free.chooseBasis ℝ Y
  rw [← LinearMap.det_toMatrix (bM.prod bY)]
  rw [show LinearMap.toMatrix (bM.prod bY) (bM.prod bY)
      (LinearMap.lowerBlockDiagonal D C T) =
        Matrix.fromBlocks (LinearMap.toMatrix bM bM D) 0
          (LinearMap.toMatrix bM bY C) (LinearMap.toMatrix bY bY T) by
    ext (i | i) (j | j) <;>
      simp [LinearMap.lowerBlockDiagonal, LinearMap.toMatrix_apply]]
  rw [Matrix.det_fromBlocks_zero₁₂]
  exact congrArg₂ (· * ·) (LinearMap.det_toMatrix bM D)
    (LinearMap.det_toMatrix bY T)

end BlockDeterminant

/-- Regroup nuisance coordinates as the bottom row followed by the top-left block. -/
def ginibreNuisanceBottomTopLinearEquiv (n : ℕ) :
    GinibreIncidenceNuisance n ≃ₗ[ℝ]
      ((Fin (n + 1) → ℝ) × RSqMat n) where
  toFun u := (Fin.lastCases u.2 u.1.2, u.1.1)
  invFun p := ((p.2, fun j => p.1 j.castSucc), p.1 (Fin.last n))
  left_inv u := by
    rcases u with ⟨⟨B, w⟩, b⟩
    simp
  right_inv p := by
    rcases p with ⟨x, B⟩
    apply Prod.ext
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    · rfl
  map_add' p q := by
    apply Prod.ext
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    · rfl

/-- Regroup nuisance coordinates columnwise, retaining the scalar last. -/
def ginibreNuisanceColumnsLinearEquiv (n : ℕ) :
    GinibreIncidenceNuisance n ≃ₗ[ℝ]
      ((Fin n → Fin (n + 1) → ℝ) × ℝ) where
  toFun u := (fun j => Fin.lastCases (u.1.2 j) (fun i => u.1.1 i j), u.2)
  invFun p := (((fun i j => p.1 j i.castSucc),
    fun j => p.1 j (Fin.last n)), p.2)
  left_inv u := by
    rcases u with ⟨⟨B, w⟩, b⟩
    simp
  right_inv p := by
    rcases p with ⟨x, b⟩
    apply Prod.ext
    · funext j i
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
    · rfl
  map_add' p q := by
    apply Prod.ext
    · funext j i
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · funext j i
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
    · rfl

/-- Apply an `(n+1)`-square matrix independently to `n` vector columns. -/
def ginibreColumnwiseLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin n → Fin (n + 1) → ℝ) →ₗ[ℝ]
      (Fin n → Fin (n + 1) → ℝ) :=
  LinearMap.pi fun j => (Matrix.toLin' Q).comp (LinearMap.proj j)

theorem det_ginibreColumnwiseLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (ginibreColumnwiseLinearMap n Q).det = Q.det ^ n := by
  rw [ginibreColumnwiseLinearMap, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

/-- Left multiplication by `Q` on the first `n` block columns, with the
distinguished eigenvalue coordinate unchanged. -/
def ginibreLeftMixLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    GinibreIncidenceNuisance n →ₗ[ℝ] GinibreIncidenceNuisance n :=
  (ginibreNuisanceColumnsLinearEquiv n).symm.toLinearMap.comp <|
    (LinearMap.prodMap (ginibreColumnwiseLinearMap n Q) LinearMap.id).comp <|
      (ginibreNuisanceColumnsLinearEquiv n).toLinearMap

theorem det_ginibreLeftMixLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (ginibreLeftMixLinearMap n Q).det = Q.det ^ n := by
  change LinearMap.det
      ((ginibreNuisanceColumnsLinearEquiv n).symm.toLinearMap.comp
        ((LinearMap.prodMap (ginibreColumnwiseLinearMap n Q) LinearMap.id).comp
          (ginibreNuisanceColumnsLinearEquiv n).toLinearMap)) = _
  have hconj := LinearMap.det_conj
    (LinearMap.prodMap (ginibreColumnwiseLinearMap n Q) LinearMap.id)
    (ginibreNuisanceColumnsLinearEquiv n).symm
  rw [show LinearMap.det
      ((ginibreNuisanceColumnsLinearEquiv n).symm.toLinearMap.comp
        ((LinearMap.prodMap (ginibreColumnwiseLinearMap n Q) LinearMap.id).comp
          (ginibreNuisanceColumnsLinearEquiv n).toLinearMap)) =
      LinearMap.det
        (LinearMap.prodMap (ginibreColumnwiseLinearMap n Q) LinearMap.id) by
    simpa [LinearMap.comp_assoc] using hconj]
  rw [LinearMap.det_prodMap, det_ginibreColumnwiseLinearMap]
  simp

/-- Right multiplication by `Qᵀ`, after the last block column has been
restricted to a multiple of the last column of `Q`. -/
def ginibreBottomRowLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  Matrix.toLin' (Q * Matrix.diagonal
    (Fin.lastCases (Q (Fin.last n) (Fin.last n)) (fun _ => 1)))

@[simp] theorem ginibreBottomRowLinearMap_apply (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    ginibreBottomRowLinearMap n Q x j =
      ∑ k : Fin (n + 1), Q j k *
        (Fin.lastCases (Q (Fin.last n) (Fin.last n)) (fun _ => 1) k * x k) := by
  rw [ginibreBottomRowLinearMap, Matrix.toLin'_mul]
  change Matrix.mulVec Q
      (Matrix.mulVec (Matrix.diagonal
        (Fin.lastCases (Q (Fin.last n) (Fin.last n)) (fun _ => 1))) x) j = _
  change (∑ k : Fin (n + 1), Q j k *
      Matrix.mulVec (Matrix.diagonal
        (Fin.lastCases (Q (Fin.last n) (Fin.last n)) (fun _ => 1))) x k) = _
  simp_rw [Matrix.mulVec_diagonal]

def ginibreTopRowsLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    RSqMat n →ₗ[ℝ] RSqMat n :=
  LinearMap.pi fun i =>
    (Matrix.toLin' (ginibreLeadingBlock n Q)).comp (LinearMap.proj i)

@[simp] theorem ginibreTopRowsLinearMap_apply (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    ginibreTopRowsLinearMap n Q A i j =
      ∑ k : Fin n, Q j.castSucc k.castSucc * A i k := rfl

def ginibreRightCrossLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] RSqMat n where
  toFun x i j := x (Fin.last n) * Q i.castSucc (Fin.last n) *
    Q j.castSucc (Fin.last n)
  map_add' x z := by
    ext i j
    simp
    ring
  map_smul' c x := by
    ext i j
    simp
    ring

def ginibreRightProjectCoreLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ((Fin (n + 1) → ℝ) × RSqMat n) →ₗ[ℝ]
      ((Fin (n + 1) → ℝ) × RSqMat n) :=
  LinearMap.lowerBlockDiagonal
    (M := Fin (n + 1) → ℝ) (Y := Fin n → Fin n → ℝ)
    (ginibreBottomRowLinearMap n Q)
    (ginibreRightCrossLinearMap n Q) (ginibreTopRowsLinearMap n Q)

@[simp] theorem ginibreRightProjectCoreLinearMap_fst (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p : (Fin (n + 1) → ℝ) × (Fin n → Fin n → ℝ)) :
    (ginibreRightProjectCoreLinearMap n Q p).1 =
      ginibreBottomRowLinearMap n Q p.1 := rfl

@[simp] theorem ginibreRightProjectCoreLinearMap_snd (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (p : (Fin (n + 1) → ℝ) × (Fin n → Fin n → ℝ)) :
    (ginibreRightProjectCoreLinearMap n Q p).2 =
      ginibreRightCrossLinearMap n Q p.1 + ginibreTopRowsLinearMap n Q p.2 := rfl

def ginibreRightProjectLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    GinibreIncidenceNuisance n →ₗ[ℝ] GinibreIncidenceNuisance n :=
  (ginibreNuisanceBottomTopLinearEquiv n).symm.toLinearMap.comp <|
    (ginibreRightProjectCoreLinearMap n Q).comp <|
      (ginibreNuisanceBottomTopLinearEquiv n).toLinearMap

theorem det_ginibreBottomRowLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (ginibreBottomRowLinearMap n Q).det =
      Q.det * Q (Fin.last n) (Fin.last n) := by
  rw [ginibreBottomRowLinearMap, LinearMap.det_toLin', Matrix.det_mul,
    Matrix.det_diagonal]
  have hprod : (∏ i : Fin (n + 1),
      Fin.lastCases (Q (Fin.last n) (Fin.last n)) (fun _ => 1) i) =
      Q (Fin.last n) (Fin.last n) := by
    rw [Fin.prod_univ_castSucc]
    simp
  rw [hprod]

theorem det_ginibreTopRowsLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    LinearMap.det (show (Fin n → Fin n → ℝ) →ₗ[ℝ]
        (Fin n → Fin n → ℝ) from ginibreTopRowsLinearMap n Q) =
      (ginibreLeadingBlock n Q).det ^ n := by
  change LinearMap.det (LinearMap.pi fun i : Fin n =>
    (Matrix.toLin' (ginibreLeadingBlock n Q)).comp (LinearMap.proj i)) = _
  rw [LinearMap.det_pi]
  simp [LinearMap.det_toLin']

theorem det_ginibreRightProjectLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (ginibreRightProjectLinearMap n Q).det =
      (Q.det * Q (Fin.last n) (Fin.last n)) *
        (ginibreLeadingBlock n Q).det ^ n := by
  change LinearMap.det
      ((ginibreNuisanceBottomTopLinearEquiv n).symm.toLinearMap.comp
        ((ginibreRightProjectCoreLinearMap n Q).comp
          (ginibreNuisanceBottomTopLinearEquiv n).toLinearMap)) = _
  have hconj := LinearMap.det_conj (ginibreRightProjectCoreLinearMap n Q)
    (ginibreNuisanceBottomTopLinearEquiv n).symm
  rw [show LinearMap.det
      ((ginibreNuisanceBottomTopLinearEquiv n).symm.toLinearMap.comp
        ((ginibreRightProjectCoreLinearMap n Q).comp
          (ginibreNuisanceBottomTopLinearEquiv n).toLinearMap)) =
      LinearMap.det (ginibreRightProjectCoreLinearMap n Q) by
    simpa [LinearMap.comp_assoc] using hconj]
  have hcore : LinearMap.det (ginibreRightProjectCoreLinearMap n Q) =
      LinearMap.det (ginibreBottomRowLinearMap n Q) *
        LinearMap.det (show (Fin n → Fin n → ℝ) →ₗ[ℝ]
          (Fin n → Fin n → ℝ) from ginibreTopRowsLinearMap n Q) := by
    change LinearMap.det
      (LinearMap.lowerBlockDiagonal
        (M := Fin (n + 1) → ℝ) (Y := Fin n → Fin n → ℝ)
        (ginibreBottomRowLinearMap n Q) (ginibreRightCrossLinearMap n Q)
          (ginibreTopRowsLinearMap n Q)) = _
    exact LinearMap.det_lowerBlockDiagonal _ _ _
  rw [hcore, det_ginibreBottomRowLinearMap,
    det_ginibreTopRowsLinearMap]

/-- The full fixed-eigenvector nuisance map from orthogonal block variables
to affine incidence nuisance variables. -/
def ginibreOrthogonalBlockToNuisanceLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    GinibreIncidenceNuisance n →ₗ[ℝ] GinibreIncidenceNuisance n :=
  (ginibreRightProjectLinearMap n Q).comp (ginibreLeftMixLinearMap n Q)

theorem abs_det_ginibreOrthogonalBlockToNuisanceLinearMap (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q) :
    |(ginibreOrthogonalBlockToNuisanceLinearMap n Q).det| =
      |Q (Fin.last n) (Fin.last n)| ^ (n + 1) := by
  rw [ginibreOrthogonalBlockToNuisanceLinearMap, LinearMap.det_comp,
    det_ginibreRightProjectLinearMap, det_ginibreLeftMixLinearMap]
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
    abs_det_eq_one_of_isOrthogonal (n + 1) Q hQ,
    abs_det_ginibreLeadingBlock_eq_abs_lastEntry n Q hQ]
  simp [pow_succ']

/-- The lower-block matrix whose last column is zero. -/
def ginibreOrthogonalBlockMatrix (n : ℕ)
    (v : GinibreIncidenceNuisance n) : GinibreRawMatrix (n + 1) :=
  ginibreCoordinatesFinMatrix (v, (0 : Fin n → ℝ))

theorem ginibreOrthogonalBlockToNuisanceLinearMap_eq_extract_conjugate
    (n : ℕ) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : GinibreIncidenceNuisance n) :
    ginibreOrthogonalBlockToNuisanceLinearMap n Q v =
      (ginibreFinMatrixCoordinates
        (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose)).1 := by
  have hcast (i : Fin n) : Fin.castAdd 1 i = i.castSucc := by
    apply Fin.ext
    rfl
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
    apply Fin.ext
    simp
  rcases v with ⟨⟨C, z⟩, l⟩
  apply Prod.ext
  · apply Prod.ext
    · ext i j
      simp [ginibreOrthogonalBlockToNuisanceLinearMap,
        ginibreRightProjectLinearMap,
        ginibreRightCrossLinearMap,
        ginibreLeftMixLinearMap,
        ginibreColumnwiseLinearMap, ginibreNuisanceBottomTopLinearEquiv,
        ginibreNuisanceColumnsLinearEquiv, ginibreFinMatrixCoordinates,
        ginibreOrthogonalBlockMatrix, ginibreCoordinatesFinMatrix,
        ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
        LinearMap.pi_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, hcast, hlast, Matrix.mul_apply,
        Fin.sum_univ_castSucc]
      change l * Q i.castSucc (Fin.last n) * Q j.castSucc (Fin.last n) +
          ∑ x : Fin n,
            Q j.castSucc x.castSucc *
              ((∑ x₁ : Fin n, Q i.castSucc x₁.castSucc * C x₁ x) +
                Q i.castSucc (Fin.last n) * z x) = _
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hsum :
          (∑ x : Fin n, Q j.castSucc x.castSucc *
              ∑ x₁ : Fin n, Q i.castSucc x₁.castSucc * C x₁ x) +
            (∑ x : Fin n,
              Q j.castSucc x.castSucc * (Q i.castSucc (Fin.last n) * z x)) =
          ∑ x : Fin n,
            (Q i.castSucc (Fin.last n) * z x * Q j.castSucc x.castSucc +
              (∑ x₁ : Fin n, Q i.castSucc x₁.castSucc * C x₁ x) *
                Q j.castSucc x.castSucc) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsum]
      have hfinal :
          (∑ x : Fin n,
            (Q i.castSucc (Fin.last n) * z x * Q j.castSucc x.castSucc +
              (∑ x₁ : Fin n, Q i.castSucc x₁.castSucc * C x₁ x) *
                Q j.castSucc x.castSucc)) =
          ∑ x : Fin n,
            ((∑ x₁ : Fin n, Q i.castSucc x₁.castSucc * C x₁ x) +
              Q i.castSucc (Fin.last n) * z x) * Q j.castSucc x.castSucc := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hfinal]
      ring
    · ext j
      simp [ginibreOrthogonalBlockToNuisanceLinearMap,
        ginibreRightProjectLinearMap,
        ginibreRightCrossLinearMap,
        ginibreLeftMixLinearMap,
        ginibreColumnwiseLinearMap, ginibreNuisanceBottomTopLinearEquiv,
        ginibreNuisanceColumnsLinearEquiv, ginibreFinMatrixCoordinates,
        ginibreOrthogonalBlockMatrix, ginibreCoordinatesFinMatrix,
        ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
        LinearMap.pi_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, hcast, hlast, Matrix.mul_apply,
        Fin.sum_univ_castSucc]
      change (∑ x : Fin n, Q j.castSucc x.castSucc *
            ((∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) +
              Q (Fin.last n) (Fin.last n) * z x)) +
          Q j.castSucc (Fin.last n) *
            (Q (Fin.last n) (Fin.last n) * l) = _
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hsum :
          (∑ x : Fin n, Q j.castSucc x.castSucc *
              ∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) +
            (∑ x : Fin n, Q j.castSucc x.castSucc *
              (Q (Fin.last n) (Fin.last n) * z x)) =
          ∑ x : Fin n,
            (Q (Fin.last n) (Fin.last n) * z x * Q j.castSucc x.castSucc +
              (∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) *
                Q j.castSucc x.castSucc) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsum]
      have hfinal :
          (∑ x : Fin n,
            (Q (Fin.last n) (Fin.last n) * z x * Q j.castSucc x.castSucc +
              (∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) *
                Q j.castSucc x.castSucc)) =
          ∑ x : Fin n,
            ((∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) +
              Q (Fin.last n) (Fin.last n) * z x) * Q j.castSucc x.castSucc := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hfinal]
      ring
  · simp [ginibreOrthogonalBlockToNuisanceLinearMap,
      ginibreRightProjectLinearMap,
      ginibreRightCrossLinearMap,
      ginibreLeftMixLinearMap,
      ginibreColumnwiseLinearMap, ginibreNuisanceBottomTopLinearEquiv,
      ginibreNuisanceColumnsLinearEquiv, ginibreFinMatrixCoordinates,
      ginibreOrthogonalBlockMatrix, ginibreCoordinatesFinMatrix,
      ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
      LinearMap.pi_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, hcast, hlast, Matrix.mul_apply,
      Fin.sum_univ_castSucc]
    change (∑ x : Fin n, Q (Fin.last n) x.castSucc *
          ((∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) +
            Q (Fin.last n) (Fin.last n) * z x)) +
        Q (Fin.last n) (Fin.last n) *
          (Q (Fin.last n) (Fin.last n) * l) = _
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hsum :
        (∑ x : Fin n, Q (Fin.last n) x.castSucc *
            ∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) +
          (∑ x : Fin n, Q (Fin.last n) x.castSucc *
            (Q (Fin.last n) (Fin.last n) * z x)) =
        ∑ x : Fin n,
          (Q (Fin.last n) (Fin.last n) * z x * Q (Fin.last n) x.castSucc +
            (∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) *
              Q (Fin.last n) x.castSucc) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hsum]
    have hfinal :
        (∑ x : Fin n,
          (Q (Fin.last n) (Fin.last n) * z x * Q (Fin.last n) x.castSucc +
            (∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) *
              Q (Fin.last n) x.castSucc)) =
        ∑ x : Fin n,
          ((∑ x₁ : Fin n, Q (Fin.last n) x₁.castSucc * C x₁ x) +
            Q (Fin.last n) (Fin.last n) * z x) * Q (Fin.last n) x.castSucc := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hfinal]
    ring

/-! ## The distinguished affine eigenvector -/

/-- The last coordinate basis vector in the ambient `(n+1)`-space. -/
def ginibreLastBasisVector (n : ℕ) : Fin (n + 1) → ℝ :=
  Pi.single (Fin.last n) 1

/-- The affine vector `(y,1)`, reindexed from `Fin n ⊕ Unit` to `Fin (n+1)`. -/
def ginibreAffineFinEigenvector (n : ℕ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun i => ginibreAffineEigenvector y ((ginibreBlockIndexEquiv n).symm i)

@[simp] theorem ginibreAffineFinEigenvector_castSucc (n : ℕ) (y : Fin n → ℝ)
    (i : Fin n) :
    ginibreAffineFinEigenvector n y i.castSucc = y i := by
  simp [ginibreAffineFinEigenvector, ginibreAffineEigenvector,
    ginibreBlockIndexEquiv, unitEquivFinOne]

@[simp] theorem ginibreAffineFinEigenvector_last (n : ℕ) (y : Fin n → ℝ) :
    ginibreAffineFinEigenvector n y (Fin.last n) = 1 := by
  simp [ginibreAffineFinEigenvector, ginibreAffineEigenvector,
    ginibreBlockIndexEquiv, unitEquivFinOne]

/-- The last coordinate axis as a point of the Euclidean unit sphere. -/
noncomputable def ginibreLastSpherePoint (n : ℕ) :
    OrthogonalSphere (n + 1) :=
  ⟨WithLp.toLp 2 (ginibreLastBasisVector n), by
    rw [Metric.mem_sphere, dist_zero_right]
    simp [ginibreLastBasisVector]⟩

/-- Reciprocal Euclidean norm of the affine vector `(y,1)`. -/
noncomputable def ginibreAffineDirectionScale (n : ℕ) (y : Fin n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (ginibreAffineFinEigenvector n y)‖⁻¹

theorem ginibreAffineFinEigenvector_ne_zero (n : ℕ) (y : Fin n → ℝ) :
    ginibreAffineFinEigenvector n y ≠ 0 := by
  intro h
  have hlast := congrFun h (Fin.last n)
  simp at hlast

theorem ginibreAffineDirectionScale_pos (n : ℕ) (y : Fin n → ℝ) :
    0 < ginibreAffineDirectionScale n y := by
  unfold ginibreAffineDirectionScale
  apply inv_pos.mpr
  rw [norm_pos_iff]
  intro h
  apply ginibreAffineFinEigenvector_ne_zero n y
  simpa using congrArg WithLp.ofLp h

theorem norm_ginibreAffineFinEigenvector (n : ℕ) (y : Fin n → ℝ) :
    ‖WithLp.toLp 2 (ginibreAffineFinEigenvector n y)‖ =
      Real.sqrt (1 + ∑ i : Fin n, y i ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [sq_abs]
  ring

theorem ginibreAffineDirectionScale_eq_inv_sqrt (n : ℕ) (y : Fin n → ℝ) :
    ginibreAffineDirectionScale n y =
      (Real.sqrt (1 + ∑ i : Fin n, y i ^ 2))⁻¹ := by
  rw [ginibreAffineDirectionScale, norm_ginibreAffineFinEigenvector]

/-- The natural Jacobian power of the normalized affine direction is the
standard projective weight. -/
theorem ginibreAffineDirectionScale_pow (n : ℕ) (y : Fin n → ℝ) :
    ginibreAffineDirectionScale n y ^ (n + 1) =
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2)) := by
  let s : ℝ := 1 + ∑ i : Fin n, y i ^ 2
  have hs : 0 < s := by
    dsimp [s]
    positivity
  rw [ginibreAffineDirectionScale_eq_inv_sqrt, Real.sqrt_eq_rpow]
  change ((s ^ (1 / 2 : ℝ))⁻¹) ^ (n + 1) =
    s ^ (-(((n : ℝ) + 1) / 2))
  calc
    ((s ^ (1 / 2 : ℝ))⁻¹) ^ (n + 1) =
        (s ^ (-(1 / 2 : ℝ))) ^ (n + 1) := by
          rw [Real.rpow_neg hs.le]
    _ = (s ^ (-(1 / 2 : ℝ))) ^ ((n + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = s ^ (-(1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_mul hs.le]
    _ = s ^ (-(((n : ℝ) + 1) / 2)) := by
      congr 1
      push_cast
      ring

/-- A Mathlib orthogonal-group element satisfies the repository's bundled
left-and-right orthogonality predicate. -/
theorem isOrthogonal_coe_orthogonalGroup (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    IsOrthogonal n (Q : Matrix (Fin n) (Fin n) ℝ) := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  have hQ := Q.property
  rw [Matrix.mem_orthogonalGroup_iff'] at hQ
  have hentry := congrFun (congrFun hQ i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hentry

/-- Every affine direction admits an orthogonal representative whose last
column is the normalized affine vector.  This is pointwise in `y`; no
measurable selection is needed for the later fixed-fiber identity. -/
theorem exists_orthogonal_lastColumn_affine (n : ℕ) (y : Fin n → ℝ) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      IsOrthogonal (n + 1) Q ∧
      (fun i => Q i (Fin.last n)) =
        ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y := by
  let x := ginibreAffineFinEigenvector n y
  let target : OrthogonalSphere (n + 1) := gaussianUnitDirection n x
  obtain ⟨Q, hQ⟩ := orthogonalGroup_action_pretransitive
    (n + 1) (ginibreLastSpherePoint n) target
  refine ⟨(Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    isOrthogonal_coe_orthogonalGroup (n + 1) Q, ?_⟩
  funext i
  have hi := congrArg
    (fun u : OrthogonalSphere (n + 1) => WithLp.ofLp (u :
      EuclideanSpace ℝ (Fin (n + 1))) i) hQ
  have hx : x ≠ 0 := ginibreAffineFinEigenvector_ne_zero n y
  change WithLp.ofLp (gaussianUnitDirectionValue n x) i =
    (Matrix.mulVec (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (ginibreLastBasisVector n)) i at hi
  simpa [gaussianUnitDirectionValue, hx, x, ginibreAffineDirectionScale,
    ginibreLastBasisVector] using hi.symm

theorem orthogonal_lastEntry_eq_affineScale (n : ℕ) (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y) :
    Q (Fin.last n) (Fin.last n) = ginibreAffineDirectionScale n y := by
  have hlast := congrFun hcol (Fin.last n)
  simpa using hlast

/-- Exact fixed-direction Jacobian, with no hypothesis on `y`. -/
theorem abs_det_ginibreOrthogonalBlockToNuisanceLinearMap_eq_projectiveWeight
    (n : ℕ) (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y) :
    |(ginibreOrthogonalBlockToNuisanceLinearMap n Q).det| =
      (1 + ∑ i : Fin n, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2)) := by
  rw [abs_det_ginibreOrthogonalBlockToNuisanceLinearMap n Q hQ,
    orthogonal_lastEntry_eq_affineScale n y Q hcol,
    abs_of_pos (ginibreAffineDirectionScale_pos n y),
    ginibreAffineDirectionScale_pow]

/-- In lower-block coordinates, the last basis vector is an eigenvector
with eigenvalue equal to the bottom-right scalar. -/
theorem ginibreOrthogonalBlockMatrix_mulVec_last (n : ℕ)
    (v : GinibreIncidenceNuisance n) :
    (Matrix.of (ginibreOrthogonalBlockMatrix n v)).mulVec
        (ginibreLastBasisVector n) =
      v.2 • ginibreLastBasisVector n := by
  rcases v with ⟨⟨C, z⟩, l⟩
  rw [show ginibreLastBasisVector n = Pi.single (Fin.last n) 1 from rfl,
    Matrix.mulVec_single_one]
  ext i
  by_cases hi : i = Fin.last n
  · subst i
    simp [ginibreOrthogonalBlockMatrix,
      ginibreCoordinatesFinMatrix, ginibreCoordinatesMatrix,
      ginibreBlockIndexEquiv, unitEquivFinOne]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    simp [ginibreOrthogonalBlockMatrix,
      ginibreCoordinatesFinMatrix, ginibreCoordinatesMatrix,
      ginibreBlockIndexEquiv, unitEquivFinOne]

/-- Orthogonal conjugation transports the distinguished block eigenvector
to the last column of the orthogonal matrix. -/
theorem ginibreOrthogonalConjugate_mulVec_lastColumn (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) :
    (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose).mulVec
        (fun i => Q i (Fin.last n)) =
      v.2 • (fun i => Q i (Fin.last n)) := by
  have hQtQ : Q.transpose * Q = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, matTranspose] using hQ.left_inv i j
  have hcol : (fun i => Q i (Fin.last n)) =
      Q.mulVec (ginibreLastBasisVector n) := by
    funext i
    simp [ginibreLastBasisVector]
  rw [hcol]
  simp only [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v))
      Q.transpose Q, hQtQ, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    ginibreOrthogonalBlockMatrix_mulVec_last]
  exact Matrix.mulVec_smul Q v.2 (ginibreLastBasisVector n)

/-- Reindexing the affine block coordinates preserves their distinguished
eigenpair equation. -/
theorem ginibreCoordinatesFinMatrix_mulVec_affine_iff (n : ℕ)
    (p : GinibreIncidenceCoordinates n) (y : Fin n → ℝ) (l : ℝ) :
    (Matrix.of (ginibreCoordinatesFinMatrix p)).mulVec
        (ginibreAffineFinEigenvector n y) =
          l • ginibreAffineFinEigenvector n y ↔
      (ginibreCoordinatesMatrix p).mulVec (ginibreAffineEigenvector y) =
        l • ginibreAffineEigenvector y := by
  let e := ginibreBlockIndexEquiv n
  constructor
  · intro h
    funext i
    have hi := congrFun h (e i)
    simpa [ginibreCoordinatesFinMatrix, ginibreAffineFinEigenvector,
      Matrix.reindex, Matrix.mulVec, dotProduct, e,
      ← Equiv.sum_comp e] using hi
  · intro h
    funext i
    have hi := congrFun h (e.symm i)
    have hsum :
        (∑ x : Fin (n + 1),
          ginibreCoordinatesMatrix p (e.symm i) (e.symm x) *
            ginibreAffineEigenvector y (e.symm x)) =
          ∑ x : Fin n ⊕ Unit,
            ginibreCoordinatesMatrix p (e.symm i) x *
              ginibreAffineEigenvector y x := by
      simpa using (Equiv.sum_comp e.symm
        (fun x : Fin n ⊕ Unit =>
          ginibreCoordinatesMatrix p (e.symm i) x *
            ginibreAffineEigenvector y x))
    change (∑ x : Fin (n + 1),
      ginibreCoordinatesMatrix p (e.symm i) (e.symm x) *
        ginibreAffineEigenvector y (e.symm x)) =
      l * ginibreAffineEigenvector y (e.symm i)
    rw [hsum]
    simpa [Matrix.mulVec, dotProduct] using hi

/-- If the last orthogonal column is a nonzero multiple of `(y,1)`, then
the conjugated block matrix has `(y,1)` as an eigenvector. -/
theorem ginibreOrthogonalConjugate_mulVec_affine (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) (y : Fin n → ℝ) (t : ℝ)
    (ht : t ≠ 0)
    (hcol : (fun i => Q i (Fin.last n)) =
      t • ginibreAffineFinEigenvector n y) :
    (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose).mulVec
        (ginibreAffineFinEigenvector n y) =
      v.2 • ginibreAffineFinEigenvector n y := by
  have h := ginibreOrthogonalConjugate_mulVec_lastColumn n Q hQ v
  rw [hcol] at h
  apply smul_right_injective (Fin (n + 1) → ℝ) ht
  calc
    t • (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose).mulVec
          (ginibreAffineFinEigenvector n y) =
        (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose).mulVec
          (t • ginibreAffineFinEigenvector n y) := by
            symm
            exact Matrix.mulVec_smul _ _ _
    _ = v.2 • (t • ginibreAffineFinEigenvector n y) := h
    _ = t • (v.2 • ginibreAffineFinEigenvector n y) := by
      simp only [smul_smul]
      rw [mul_comm]

/-- The affine incidence chart assembled from the transformed nuisance
coordinates is exactly the orthogonally conjugated lower-block matrix. -/
theorem ginibreCoordinatesFinMatrix_incidenceChart_orthogonalBlock (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) (y : Fin n → ℝ) (t : ℝ)
    (ht : t ≠ 0)
    (hcol : (fun i => Q i (Fin.last n)) =
      t • ginibreAffineFinEigenvector n y) :
    ginibreCoordinatesFinMatrix
        (ginibreIncidenceChart
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y)) =
      Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose := by
  let A : GinibreRawMatrix (n + 1) :=
    Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose
  let p : GinibreIncidenceCoordinates n := ginibreFinMatrixCoordinates A
  have hpA : ginibreCoordinatesFinMatrix p = A :=
    (ginibreCoordinatesLinearEquiv n).right_inv A
  have hp1 : p.1 = ginibreOrthogonalBlockToNuisanceLinearMap n Q v := by
    change (ginibreFinMatrixCoordinates A).1 = _
    exact (ginibreOrthogonalBlockToNuisanceLinearMap_eq_extract_conjugate
      n Q v).symm
  have heigA : (Matrix.of A).mulVec (ginibreAffineFinEigenvector n y) =
      v.2 • ginibreAffineFinEigenvector n y :=
    ginibreOrthogonalConjugate_mulVec_affine n Q hQ v y t ht hcol
  have heigFin :
      (Matrix.of (ginibreCoordinatesFinMatrix p)).mulVec
          (ginibreAffineFinEigenvector n y) =
        v.2 • ginibreAffineFinEigenvector n y := by
    rw [hpA]
    exact heigA
  have heigBlock :
      (ginibreCoordinatesMatrix p).mulVec (ginibreAffineEigenvector y) =
        v.2 • ginibreAffineEigenvector y :=
    (ginibreCoordinatesFinMatrix_mulVec_affine_iff n p y v.2).mp heigFin
  have hl : ginibreIncidenceEigenvalue (p.1, y) = v.2 := by
    have hlast := congrFun heigBlock (Sum.inr ())
    have hlast' :
        (∑ x : Fin n, p.1.1.2 x * y x) + p.1.2 = v.2 := by
      simpa [ginibreCoordinatesMatrix, ginibreAffineEigenvector,
        Matrix.mulVec, dotProduct] using hlast
    unfold ginibreIncidenceEigenvalue
    linarith
  have hchart : ginibreIncidenceChart (p.1, y) = p := by
    apply (ginibreIncidenceChart_fiber_iff_affine_eigenpair p y).mpr
    rw [hl]
    exact heigBlock
  rw [hp1] at hchart
  calc
    ginibreCoordinatesFinMatrix
        (ginibreIncidenceChart
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y)) =
        ginibreCoordinatesFinMatrix p := congrArg ginibreCoordinatesFinMatrix hchart
    _ = A := hpA

/-! ## Gaussian density under the fiber coordinates -/

theorem ginibreMatrixSq_orthogonal_conjugate (n : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsOrthogonal n Q)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ginibreMatrixSq n (Q * A * Q.transpose) = ginibreMatrixSq n A := by
  change frobNormSq (matMul n (matMul n Q A) (matTranspose Q)) = frobNormSq A
  rw [frobNormSq_orthogonal_right _ _ hQ.transpose,
    frobNormSq_orthogonal_left _ _ hQ]

/-- The standard Ginibre density is invariant under orthogonal conjugation. -/
theorem realGinibreDensityReal_orthogonal_conjugate (n : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsOrthogonal n Q)
    (A : RSqMat n) :
    realGinibreDensityReal n (Q * A * Q.transpose) =
      realGinibreDensityReal n A := by
  rw [realGinibreDensityReal_eq_exp, realGinibreDensityReal_eq_exp,
    ginibreMatrixSq_orthogonal_conjugate n Q hQ]

/-- The lower-block Gaussian density factors into the `n × n` Ginibre
density, `n` zero-coordinate densities, the bottom-row density, and the
scalar density. -/
theorem realGinibreDensityReal_orthogonalBlock (n : ℕ)
    (v : GinibreIncidenceNuisance n) :
    realGinibreDensityReal (n + 1)
        (Matrix.of (ginibreOrthogonalBlockMatrix n v)) =
      (gaussianPDFReal 0 1 0) ^ n *
        realGinibreDensityReal n (show RSqMat n from v.1.1) *
        (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
        gaussianPDFReal 0 1 v.2 := by
  rcases v with ⟨⟨C, z⟩, l⟩
  unfold realGinibreDensityReal
  rw [Fin.prod_univ_castSucc]
  simp_rw [Fin.prod_univ_castSucc]
  simp [ginibreOrthogonalBlockMatrix, ginibreCoordinatesFinMatrix,
    ginibreCoordinatesMatrix, ginibreBlockIndexEquiv, unitEquivFinOne,
    Finset.prod_mul_distrib]
  ring

/-! ## The deflated characteristic polynomial -/

/-- The lower-block matrix has the expected characteristic-polynomial
factorization. -/
theorem ginibreOrthogonalBlockMatrix_charpoly (n : ℕ)
    (v : GinibreIncidenceNuisance n) :
    (Matrix.of (ginibreOrthogonalBlockMatrix n v)).charpoly =
      (Matrix.of v.1.1).charpoly *
        (Polynomial.X - Polynomial.C v.2) := by
  rw [ginibreOrthogonalBlockMatrix,
    ginibreCoordinatesFinMatrix_charpoly]
  unfold ginibreCoordinatesMatrix
  change (Matrix.fromBlocks v.1.1
      (0 : Matrix (Fin n) Unit ℝ)
      (fun _ j => v.1.2 j) (fun _ _ => v.2)).charpoly = _
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  congr 1
  have hdiag : (fun _ _ : Unit => v.2) =
      Matrix.diagonal (fun _ : Unit => v.2) := by
    ext i j
    rcases i with ⟨⟩
    rcases j with ⟨⟩
    simp
  rw [hdiag, Matrix.charpoly_diagonal]
  simp

/-- Orthogonal conjugation preserves the block characteristic polynomial. -/
theorem ginibreOrthogonalConjugate_charpoly (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) :
    (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose).charpoly =
      (Matrix.of v.1.1).charpoly *
        (Polynomial.X - Polynomial.C v.2) := by
  have hQtQ : Q.transpose * Q =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, matTranspose] using hQ.left_inv i j
  have hcomm := Matrix.charpoly_mul_comm
    (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v)) Q.transpose
  calc
    (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose).charpoly =
        (Q.transpose *
          (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v))).charpoly := hcomm
    _ = (Matrix.of (ginibreOrthogonalBlockMatrix n v)).charpoly := by
      rw [← Matrix.mul_assoc, hQtQ, Matrix.one_mul]
    _ = _ := ginibreOrthogonalBlockMatrix_charpoly n v

/-- The eigenvalue reconstructed by the affine incidence chart is the
bottom-right scalar of the lower-block matrix. -/
theorem ginibreIncidenceEigenvalue_orthogonalBlock (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) (y : Fin n → ℝ) (t : ℝ)
    (ht : t ≠ 0)
    (hcol : (fun i => Q i (Fin.last n)) =
      t • ginibreAffineFinEigenvector n y) :
    ginibreIncidenceEigenvalue
        (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) = v.2 := by
  let q : GinibreIncidenceCoordinates n :=
    (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y)
  have hmatrix := ginibreCoordinatesFinMatrix_incidenceChart_orthogonalBlock
    n Q hQ v y t ht hcol
  have heigFin :
      (Matrix.of (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))).mulVec
          (ginibreAffineFinEigenvector n y) =
        v.2 • ginibreAffineFinEigenvector n y := by
    rw [hmatrix]
    exact ginibreOrthogonalConjugate_mulVec_affine n Q hQ v y t ht hcol
  have heigBlock :=
    (ginibreCoordinatesFinMatrix_mulVec_affine_iff n
      (ginibreIncidenceChart q) y v.2).mp heigFin
  rw [ginibreCoordinatesMatrix_chart] at heigBlock
  have hcanonical := ginibreIncidenceMatrix_has_eigenpair q
  have hlast := (congrFun hcanonical (Sum.inr ())).symm.trans
    (congrFun heigBlock (Sum.inr ()))
  simpa [ginibreAffineEigenvector] using hlast

/-- The affine deflated block and the original upper-left block have the
same characteristic polynomial. -/
theorem ginibreIncidenceDeflatedBlock_charpoly_orthogonalBlock (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) (y : Fin n → ℝ) (t : ℝ)
    (ht : t ≠ 0)
    (hcol : (fun i => Q i (Fin.last n)) =
      t • ginibreAffineFinEigenvector n y) :
    (Matrix.of (ginibreIncidenceDeflatedBlock
        (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y))).charpoly =
      (Matrix.of v.1.1).charpoly := by
  let q : GinibreIncidenceCoordinates n :=
    (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y)
  have hl : ginibreIncidenceEigenvalue q = v.2 :=
    ginibreIncidenceEigenvalue_orthogonalBlock n Q hQ v y t ht hcol
  have hmatrix := ginibreCoordinatesFinMatrix_incidenceChart_orthogonalBlock
    n Q hQ v y t ht hcol
  have hmatrix' : Matrix.of
      (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)) =
        Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) * Q.transpose := by
    ext i j
    exact congrFun (congrFun hmatrix i) j
  have hchar : (ginibreIncidenceMatrix q).charpoly =
      (Matrix.of v.1.1).charpoly *
        (Polynomial.X - Polynomial.C v.2) := by
    calc
      (ginibreIncidenceMatrix q).charpoly =
          (ginibreCoordinatesMatrix (ginibreIncidenceChart q)).charpoly := by
            rw [ginibreCoordinatesMatrix_chart]
      _ = (Matrix.of
          (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))).charpoly :=
            (ginibreCoordinatesFinMatrix_charpoly
              (ginibreIncidenceChart q)).symm
      _ = (Q * Matrix.of (ginibreOrthogonalBlockMatrix n v) *
          Q.transpose).charpoly := by rw [hmatrix']
      _ = _ := ginibreOrthogonalConjugate_charpoly n Q hQ v
  rw [ginibreIncidenceMatrix_charpoly_factor, hl] at hchar
  exact mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero v.2) hchar

/-- Absolute determinant of a scalar shift as the absolute characteristic
polynomial evaluation. -/
theorem abs_det_sub_smul_one_eq_abs_charpoly_eval (n : ℕ)
    (A : RSqMat n) (l : ℝ) :
    |(A - l • (1 : RSqMat n)).det| =
      |(Matrix.of A).charpoly.eval l| := by
  rw [Matrix.eval_charpoly]
  have hneg : A - l • (1 : RSqMat n) =
      -(Matrix.scalar (Fin n) l - Matrix.of A) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]

/-- Signed version of scalar-shift characteristic-polynomial evaluation. -/
theorem det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval (n : ℕ)
    (A : RSqMat n) (l : ℝ) :
    (A - l • (1 : RSqMat n)).det =
      (-1 : ℝ) ^ n * (Matrix.of A).charpoly.eval l := by
  rw [Matrix.eval_charpoly]
  have hneg : A - l • (1 : RSqMat n) =
      -(Matrix.scalar (Fin n) l - Matrix.of A) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hneg, Matrix.det_neg, Fintype.card_fin]

/-- Signed fixed-direction determinant reduction. -/
theorem det_ginibreIncidenceDeflatedBlock_orthogonalBlock (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) (y : Fin n → ℝ) (t : ℝ)
    (ht : t ≠ 0)
    (hcol : (fun i => Q i (Fin.last n)) =
      t • ginibreAffineFinEigenvector n y) :
    (ginibreIncidenceDeflatedBlock
        (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) -
      ginibreIncidenceEigenvalue
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) •
        (1 : RSqMat n)).det =
      ((show RSqMat n from v.1.1) -
        v.2 • (1 : RSqMat n)).det := by
  rw [ginibreIncidenceEigenvalue_orthogonalBlock n Q hQ v y t ht hcol,
    det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval,
    det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval,
    ginibreIncidenceDeflatedBlock_charpoly_orthogonalBlock n Q hQ v y t ht hcol]

/-- In fixed affine direction, the incidence determinant is exactly the
absolute characteristic determinant of the `n × n` Ginibre block. -/
theorem abs_det_ginibreIncidenceDeflatedBlock_orthogonalBlock (n : ℕ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (v : GinibreIncidenceNuisance n) (y : Fin n → ℝ) (t : ℝ)
    (ht : t ≠ 0)
    (hcol : (fun i => Q i (Fin.last n)) =
      t • ginibreAffineFinEigenvector n y) :
    |(ginibreIncidenceDeflatedBlock
        (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) -
      ginibreIncidenceEigenvalue
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) •
        (1 : RSqMat n)).det| =
      |((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| := by
  rw [ginibreIncidenceEigenvalue_orthogonalBlock n Q hQ v y t ht hcol,
    abs_det_sub_smul_one_eq_abs_charpoly_eval,
    abs_det_sub_smul_one_eq_abs_charpoly_eval,
    ginibreIncidenceDeflatedBlock_charpoly_orthogonalBlock n Q hQ v y t ht hcol]

/-- Complete pointwise fixed-direction reduction of the incidence integrand.
The bottom-row Gaussian factor remains explicit for the subsequent integral. -/
theorem ginibreFixedFiber_integrand_eq (n : ℕ) (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y)
    (v : GinibreIncidenceNuisance n) :
    |(ginibreIncidenceDeflatedBlock
        (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) -
      ginibreIncidenceEigenvalue
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) •
        (1 : RSqMat n)).det| *
      realGinibreDensityReal (n + 1)
        (ginibreCoordinatesFinMatrix
          (ginibreIncidenceChart
            (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y))) =
      (gaussianPDFReal 0 1 0) ^ n *
        (|((show RSqMat n from v.1.1) - v.2 • (1 : RSqMat n)).det| *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2) := by
  rw [abs_det_ginibreIncidenceDeflatedBlock_orthogonalBlock n Q hQ v y
      (ginibreAffineDirectionScale n y) (ginibreAffineDirectionScale_pos n y).ne'
      hcol,
    ginibreCoordinatesFinMatrix_incidenceChart_orthogonalBlock n Q hQ v y
      (ginibreAffineDirectionScale n y) (ginibreAffineDirectionScale_pos n y).ne'
      hcol,
    realGinibreDensityReal_orthogonal_conjugate (n + 1) Q hQ,
    realGinibreDensityReal_orthogonalBlock]
  ring

/-- Signed, characteristic-polynomial-weighted version of the fixed-direction
integrand reduction.  The auxiliary weight is allowed to depend on the
deflated characteristic polynomial and on the distinguished eigenvalue; both
are preserved by the orthogonal block parametrization. -/
theorem ginibreSignedFixedFiber_integrand_eq (n : ℕ) (y : Fin n → ℝ)
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : IsOrthogonal (n + 1) Q)
    (hcol : (fun i => Q i (Fin.last n)) =
      ginibreAffineDirectionScale n y • ginibreAffineFinEigenvector n y)
    (H : Polynomial ℝ → ℝ → ℝ) (v : GinibreIncidenceNuisance n) :
    (ginibreIncidenceDeflatedBlock
        (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) -
      ginibreIncidenceEigenvalue
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y) •
        (1 : RSqMat n)).det *
      H (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y))))
        (ginibreIncidenceEigenvalue
          (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y)) *
      realGinibreDensityReal (n + 1)
        (ginibreCoordinatesFinMatrix
          (ginibreIncidenceChart
            (ginibreOrthogonalBlockToNuisanceLinearMap n Q v, y))) =
      (gaussianPDFReal 0 1 0) ^ n *
        (((show RSqMat n from v.1.1) -
              v.2 • (1 : RSqMat n)).det *
          H (Matrix.charpoly (Matrix.of (show RSqMat n from v.1.1))) v.2 *
          realGinibreDensityReal n (show RSqMat n from v.1.1) *
          (∏ i : Fin n, gaussianPDFReal 0 1 (v.1.2 i)) *
          gaussianPDFReal 0 1 v.2) := by
  rw [det_ginibreIncidenceDeflatedBlock_orthogonalBlock n Q hQ v y
      (ginibreAffineDirectionScale n y) (ginibreAffineDirectionScale_pos n y).ne'
      hcol,
    ginibreIncidenceEigenvalue_orthogonalBlock n Q hQ v y
      (ginibreAffineDirectionScale n y) (ginibreAffineDirectionScale_pos n y).ne'
      hcol,
    ginibreIncidenceDeflatedBlock_charpoly_orthogonalBlock n Q hQ v y
      (ginibreAffineDirectionScale n y) (ginibreAffineDirectionScale_pos n y).ne'
      hcol,
    ginibreCoordinatesFinMatrix_incidenceChart_orthogonalBlock n Q hQ v y
      (ginibreAffineDirectionScale n y) (ginibreAffineDirectionScale_pos n y).ne'
      hcol,
    realGinibreDensityReal_orthogonal_conjugate (n + 1) Q hQ,
    realGinibreDensityReal_orthogonalBlock]
  ring

/-! ## Canonical product volume in affine coordinates -/

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

/-- Global linear change of variables for a finite-dimensional product
Lebesgue space, in the orientation used by the fixed-fiber calculation. -/
theorem lintegral_linearMap_eq_abs_det_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E →ₗ[ℝ] E) (hf : LinearMap.det f ≠ 0) (g : E → ℝ≥0∞) :
    (∫⁻ u, g u ∂μ) =
      ENNReal.ofReal |LinearMap.det f| *
        ∫⁻ v, g (f v) ∂μ := by
  have himage : f '' (Set.univ : Set E) = Set.univ := by
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr (f.equivOfDetNeZero hf).surjective
  have himage' : (f.toContinuousLinearMap : E → E) ''
      (Set.univ : Set E) = Set.univ := by
    simpa using himage
  have harea := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    μ MeasurableSet.univ
    (fun x hx => f.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    (f.equivOfDetNeZero hf).injective.injOn g
  rw [himage'] at harea
  calc
    (∫⁻ u, g u ∂μ) =
        ∫⁻ v, ENNReal.ofReal |LinearMap.det f| * g (f v)
          ∂μ := by simpa using harea
    _ = ENNReal.ofReal |LinearMap.det f| *
        ∫⁻ v, g (f v) ∂μ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Ordinary-integral form of the global linear change of variables.  Like
Mathlib's area formula, this equality is unconditional; in the
nonintegrable case both Bochner integrals use the standard zero convention. -/
theorem integral_linearMap_eq_abs_det_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E →ₗ[ℝ] E) (hf : LinearMap.det f ≠ 0) (g : E → ℝ) :
    (∫ u, g u ∂μ) =
      |LinearMap.det f| * ∫ v, g (f v) ∂μ := by
  have himage : f '' (Set.univ : Set E) = Set.univ := by
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr (f.equivOfDetNeZero hf).surjective
  have himage' : (f.toContinuousLinearMap : E → E) ''
      (Set.univ : Set E) = Set.univ := by
    simpa using himage
  have harea := integral_image_eq_integral_abs_det_fderiv_smul
    μ MeasurableSet.univ
    (fun x hx => f.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    (f.equivOfDetNeZero hf).injective.injOn g
  rw [himage'] at harea
  calc
    (∫ u, g u ∂μ) =
        ∫ v, |LinearMap.det f| • g (f v) ∂μ := by
      simpa using harea
    _ = |LinearMap.det f| * ∫ v, g (f v) ∂μ := by
      simp only [smul_eq_mul]
      rw [integral_const_mul]

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

theorem lintegral_standardGaussianVectorDensity (n : ℕ) :
    (∫⁻ z : Fin n → ℝ,
      ENNReal.ofReal (∏ i : Fin n, gaussianPDFReal 0 1 (z i))) = 1 := by
  have hint : Integrable
      (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDFReal 0 1 (z i)) := by
    exact Integrable.fintype_prod (fun _ : Fin n =>
      integrable_gaussianPDFReal 0 1)
  have hnonneg : ∀ z : Fin n → ℝ,
      0 ≤ ∏ i : Fin n, gaussianPDFReal 0 1 (z i) := by
    intro z
    exact Finset.prod_nonneg fun i hi => gaussianPDFReal_nonneg 0 1 (z i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnonneg)]
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one]

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

end
end NumStability
