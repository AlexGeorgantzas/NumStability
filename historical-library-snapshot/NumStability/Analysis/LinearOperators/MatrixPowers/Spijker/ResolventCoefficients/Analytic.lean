import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteDimensional
import NumStability.Analysis.FunctionalCalculus.Resolvent.Analyticity
import NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.DistanceToInstability
import NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.ResolventBound
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.SingularValues.Basic

/-!
# Analysis.LinearOperators.MatrixPowers.Spijker.ResolventCoefficients.Analytic

R07 canonical `reusable` leaf. Declaration-level review groups 13 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixEuclideanCoefficientCLM`, `NumStability.cstarMatrixEuclideanCoefficientCLM_apply`, `NumStability.cstarMatrixEuclideanCoefficientCLM_circleIntegral`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped Real Topology ComplexOrder

open Complex Metric Set MeasureTheory

noncomputable section

/-- The Euclidean scalar coefficient `⟪v, M u⟫`, linear in the matrix `M`. -/
def cstarMatrixEuclideanCoefficientLinear
    {n : ℕ} [Nonempty (Fin n)] (u v : EuclideanSpace ℂ (Fin n)) :
    CStarMatrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun M := inner ℂ v
    (complexMatrixEuclideanLin (fun i j => M i j) u)
  map_add' M N := by
    have haction :
        complexMatrixEuclideanLin (fun i j => (M + N) i j) u =
          complexMatrixEuclideanLin (fun i j => M i j) u +
            complexMatrixEuclideanLin (fun i j => N i j) u := by
      apply WithLp.ofLp_injective
      ext i
      simp [complexMatrixEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct, Finset.sum_add_distrib, add_mul]
    rw [haction, inner_add_right]
  map_smul' c M := by
    have haction :
        complexMatrixEuclideanLin (fun i j => (c • M) i j) u =
          c • complexMatrixEuclideanLin (fun i j => M i j) u := by
      apply WithLp.ofLp_injective
      ext i
      simp [complexMatrixEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct, Finset.mul_sum, mul_assoc]
    rw [haction, inner_smul_right]
    simp only [RingHom.id_apply, smul_eq_mul]

/-- Continuous version of `cstarMatrixEuclideanCoefficientLinear`. -/
def cstarMatrixEuclideanCoefficientCLM
    {n : ℕ} [Nonempty (Fin n)] (u v : EuclideanSpace ℂ (Fin n)) :
    CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  (cstarMatrixEuclideanCoefficientLinear u v).toContinuousLinearMap

@[simp]
lemma cstarMatrixEuclideanCoefficientCLM_apply
    {n : ℕ} [Nonempty (Fin n)] (u v : EuclideanSpace ℂ (Fin n))
    (M : CStarMatrix (Fin n) (Fin n) ℂ) :
    cstarMatrixEuclideanCoefficientCLM u v M =
      inner ℂ v (complexMatrixEuclideanLin (fun i j => M i j) u) := by
  change cstarMatrixEuclideanCoefficientLinear u v M = _
  rfl

/-- Scalar resolvent coefficient used in the sharp Kreiss proof. -/
def spijkerResolventCoefficient
    {n : ℕ} [Nonempty (Fin n)] (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) (z : ℂ) : ℂ :=
  cstarMatrixEuclideanCoefficientCLM u v (resolvent A z)

/-- The coefficient curve on the circle of radius `R`. -/
def spijkerResolventCoefficientCurve
    {n : ℕ} [Nonempty (Fin n)] (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) (R : ℝ) (θ : ℝ) : ℂ :=
  spijkerResolventCoefficient A u v (circleMap 0 R θ)

/-- A Euclidean matrix coefficient commutes with a circle integral. -/
lemma cstarMatrixEuclideanCoefficientCLM_circleIntegral
    {n : ℕ} [Nonempty (Fin n)]
    (u v : EuclideanSpace ℂ (Fin n))
    {f : ℂ → CStarMatrix (Fin n) (Fin n) ℂ} {R : ℝ}
    (hf : CircleIntegrable f 0 R) :
    cstarMatrixEuclideanCoefficientCLM u v
        (∮ z in C(0, R), f z) =
      ∮ z in C(0, R), cstarMatrixEuclideanCoefficientCLM u v (f z) := by
  rw [circleIntegral, circleIntegral]
  calc
    _ = ∫ θ : ℝ in 0..2 * Real.pi,
        cstarMatrixEuclideanCoefficientCLM u v
          (deriv (circleMap 0 R) θ • f (circleMap 0 R θ)) :=
      ((cstarMatrixEuclideanCoefficientCLM u v).intervalIntegral_comp_comm hf.out).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _hθ
      simp only [map_smul]

/-- The matrix Cauchy formula, after applying a Euclidean scalar
coefficient.  Keeping this identity separate makes the scalar
integration-by-parts step auditable. -/
lemma spijkerResolventCoefficient_pow_eq_circleIntegral
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) (k : ℕ) :
    cstarMatrixEuclideanCoefficientCLM u v (A ^ k) =
      (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C(0, R), z ^ k * spijkerResolventCoefficient A u v z := by
  have hsphere : sphere (0 : ℂ) R ⊆ resolventSet ℂ A := by
    intro z hz
    have hznorm : ‖z‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hz
    exact (hK z (by simpa [hznorm] using hR)).1
  have hfint : CircleIntegrable
      (fun z : ℂ => z ^ k • resolvent A z) 0 R :=
    ((continuous_pow k).continuousOn.smul
      ((resolvent_continuousOn A).mono hsphere)).circleIntegrable
        (zero_le_one.trans hR.le)
  have hp :=
    pow_eq_two_pi_I_inv_smul_circleIntegral_of_kreissResolventBound
      A hK hR k
  have hmap := congrArg (cstarMatrixEuclideanCoefficientCLM u v) hp
  rw [map_smul] at hmap
  calc
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
        cstarMatrixEuclideanCoefficientCLM u v
          (∮ z in C(0, R), z ^ k • resolvent A z) := hmap
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(0, R), cstarMatrixEuclideanCoefficientCLM u v
          (z ^ k • resolvent A z)) := by
      congr 1
      exact cstarMatrixEuclideanCoefficientCLM_circleIntegral u v hfint
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _hθ
      simp only [map_smul, smul_eq_mul, spijkerResolventCoefficient]

/-- Parameterized scalar Cauchy moment.  The extra factor of `z` comes from
the derivative of the circle parameterization. -/
lemma spijkerResolventCoefficient_pow_eq_intervalIntegral
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) (k : ℕ) :
    cstarMatrixEuclideanCoefficientCLM u v (A ^ k) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ θ : ℝ in 0..2 * Real.pi,
          circleMap 0 R θ ^ (k + 1) *
            spijkerResolventCoefficientCurve A u v R θ := by
  rw [spijkerResolventCoefficient_pow_eq_circleIntegral A u v hK hR k]
  rw [circleIntegral]
  have hintegrand :
      (∫ θ : ℝ in 0..2 * Real.pi,
          deriv (circleMap 0 R) θ *
            (circleMap 0 R θ ^ k *
              spijkerResolventCoefficient A u v (circleMap 0 R θ))) =
        I * (∫ θ : ℝ in 0..2 * Real.pi,
          circleMap 0 R θ ^ (k + 1) *
            spijkerResolventCoefficientCurve A u v R θ) := by
    calc
      _ = ∫ θ : ℝ in 0..2 * Real.pi,
          I * (circleMap 0 R θ ^ (k + 1) *
            spijkerResolventCoefficientCurve A u v R θ) := by
        apply intervalIntegral.integral_congr
        intro θ _hθ
        dsimp only
        rw [deriv_circleMap]
        simp only [spijkerResolventCoefficientCurve]
        rw [pow_succ]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  simp only [smul_eq_mul]
  have htwoPi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  calc
    _ = (2 * Real.pi * I : ℂ)⁻¹ *
        (I * (∫ θ : ℝ in 0..2 * Real.pi,
          circleMap 0 R θ ^ (k + 1) *
            spijkerResolventCoefficientCurve A u v R θ)) := by
      exact congrArg (fun x : ℂ => (2 * Real.pi * I : ℂ)⁻¹ * x) hintegrand
    _ = _ := by
      field_simp [htwoPi, I_ne_zero]
      push_cast
      ring

set_option backward.isDefEq.respectTransparency false in
/-- Along every exterior circle, a resolvent coefficient is differentiable
as a real-parameterized curve. -/
lemma spijkerResolventCoefficientCurve_differentiableAt
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) (θ : ℝ) :
    DifferentiableAt ℝ
      (spijkerResolventCoefficientCurve A u v R) θ := by
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hzmem : circleMap 0 R θ ∈ resolventSet ℂ A := by
    apply (hK (circleMap 0 R θ) ?_).1
    simpa [norm_circleMap_zero, abs_of_pos hRpos] using hR
  have hcoeff : DifferentiableAt ℂ
      (spijkerResolventCoefficient A u v) (circleMap 0 R θ) := by
    exact (cstarMatrixEuclideanCoefficientCLM u v).differentiableAt.comp
      (circleMap 0 R θ) (resolvent_differentiableAt A hzmem)
  exact hcoeff.restrictScalars ℝ |>.comp θ
    (differentiable_circleMap 0 R θ)

/-- Explicit real-parameter derivative of a resolvent coefficient along an
exterior circle.  This is the chain rule applied to `R'(z) = -R(z)^2`. -/
lemma spijkerResolventCoefficientCurve_hasDerivAt
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) (θ : ℝ) :
    HasDerivAt (spijkerResolventCoefficientCurve A u v R)
      (cstarMatrixEuclideanCoefficientCLM u v
        (-resolvent A (circleMap 0 R θ) ^ 2) * (circleMap 0 R θ * I)) θ := by
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hzmem : circleMap 0 R θ ∈ resolventSet ℂ A := by
    apply (hK (circleMap 0 R θ) ?_).1
    simpa [norm_circleMap_zero, abs_of_pos hRpos] using hR
  have hresCoeff : HasDerivAt (spijkerResolventCoefficient A u v)
      (cstarMatrixEuclideanCoefficientCLM u v
        (-resolvent A (circleMap 0 R θ) ^ 2)) (circleMap 0 R θ) := by
    have hcomp := (cstarMatrixEuclideanCoefficientCLM u v).hasFDerivAt.comp
      (circleMap 0 R θ) (resolvent_hasDerivAt A hzmem).hasFDerivAt
    convert hcomp.hasDerivAt using 1
    rw [ContinuousLinearMap.comp_apply]
    exact congrArg (cstarMatrixEuclideanCoefficientCLM u v)
      (ContinuousLinearMap.toSpanSingleton_apply_one ℂ
        (-resolvent A (circleMap 0 R θ) ^ 2)).symm
  exact hresCoeff.comp θ (hasDerivAt_circleMap 0 R θ)

/-- On every exterior circle controlled by a Kreiss resolvent bound, the
derivative of each scalar resolvent coefficient is continuous. -/
lemma spijkerResolventCoefficientCurve_deriv_continuous
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) :
    Continuous (fun θ : ℝ =>
      deriv (spijkerResolventCoefficientCurve A u v R) θ) := by
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hzmem : ∀ θ : ℝ, circleMap 0 R θ ∈ resolventSet ℂ A := by
    intro θ
    apply (hK (circleMap 0 R θ) ?_).1
    simpa [norm_circleMap_zero, abs_of_pos hRpos] using hR
  have hresCurve : Continuous (fun θ : ℝ => resolvent A (circleMap 0 R θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact ((resolvent_continuousOn A).continuousAt
      ((spectrum.isOpen_resolventSet A).mem_nhds (hzmem θ))).comp
        (continuous_circleMap 0 R).continuousAt
  have hformula : (fun θ : ℝ =>
      deriv (spijkerResolventCoefficientCurve A u v R) θ) =
      (fun θ : ℝ => cstarMatrixEuclideanCoefficientCLM u v
        (-resolvent A (circleMap 0 R θ) ^ 2) * (circleMap 0 R θ * I)) := by
    funext θ
    exact (spijkerResolventCoefficientCurve_hasDerivAt
      A u v hK hR θ).deriv
  rw [hformula]
  exact ((cstarMatrixEuclideanCoefficientCLM u v).continuous.comp
      (hresCurve.pow 2).neg).mul
    ((continuous_circleMap 0 R).mul continuous_const)

/-- The derivative integrability needed for integration by parts is internal:
it follows from resolvent analyticity on an exterior circle and is not part of
the Spijker arc-length interface. -/
lemma spijkerResolventCoefficientCurve_deriv_intervalIntegrable
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) :
    IntervalIntegrable
      (fun θ : ℝ => deriv (spijkerResolventCoefficientCurve A u v R) θ)
      volume 0 (2 * Real.pi) :=
  (spijkerResolventCoefficientCurve_deriv_continuous
    A u v hK hR).intervalIntegrable _ _

/-- A normalized antiderivative of the circle monomial used in integration
by parts. -/
lemma hasDerivAt_spijkerPowerAntiderivative
    (R : ℝ) (k : ℕ) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => ((((k + 1 : ℕ) : ℝ) : ℂ) * I)⁻¹ *
        circleMap 0 R t ^ (k + 1))
      (circleMap 0 R θ ^ (k + 1)) θ := by
  have hm : ((((k + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  have hraw := (hasDerivAt_circleMap 0 R θ).pow (k + 1)
  have hscaled := hraw.const_mul
    (((((k + 1 : ℕ) : ℝ) : ℂ) * I)⁻¹)
  convert hscaled using 1
  field_simp [hm, I_ne_zero]
  push_cast
  rw [pow_succ]
  ring

end

end NumStability
