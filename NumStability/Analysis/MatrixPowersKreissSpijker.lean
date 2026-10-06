/-
# The Spijker interface in the finite-dimensional Kreiss theorem

The sharp reverse Kreiss inequality

  `‖A^k‖₂ ≤ exp(1) * n * K`

does not follow from Cayley--Hamilton with uncontrolled characteristic-
polynomial coefficients.  Its standard proof uses Spijker's sharp arc-length
lemma for rational functions.  If `q` is a quotient of two polynomials of
degree at most `n`, with no pole on a circle, that lemma states

  `∫ |q'| ≤ 2π n sup |q|`.

For the Kreiss proof one takes

  `q(z) = ⟪v, (zI-A)⁻¹u⟫`.

This scalar function has rational order at most `n` by the adjugate formula.
The predicate `SpijkerArcLengthBound` below is exactly the sharp inequality in
this specialization.  Its `KreissResolventBound` and `1 < R` hypotheses imply
the source requirement that the circle be pole-free.  The continuity and
interval integrability of the derivative on
the exterior circles used by the Kreiss proof are established internally
below.  This file isolates the Spijker inequality as a reusable interface and
proves that it implies the full all-powers Kreiss endpoint.  The interface is
proved unconditionally by the planar projection and finite layer-cake
argument in `MatrixPowersSpijkerPlanarAnalysis`.
-/

import NumStability.Analysis.MatrixPowersKreiss
import NumStability.Analysis.MatrixPowersBaiDemmelGuDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

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

/--
The exact resolvent-coefficient specialization of **Spijker's sharp
arc-length lemma** (Spijker 1991; Wegert--Trefethen 1994).

The universal published theorem applies because each coefficient
`⟪v,(zI-A)⁻¹u⟫` is rational of order at most `n`.  The Kreiss resolvent bound
and `1 < R` record the source requirement that the rational function have no
pole on the circle; the corresponding explicit denominator fact is
`spijkerResolventCoefficient_certificate_denominator_ne_on_exteriorCircle`.
-/
def SpijkerArcLengthBound (n : ℕ) [Nonempty (Fin n)] : Prop :=
  ∀ (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) (K R C : ℝ),
    KreissResolventBound A K → 1 < R → 0 ≤ C →
    (∀ z ∈ Metric.sphere (0 : ℂ) R,
      ‖spijkerResolventCoefficient A u v z‖ ≤ C) →
    (∫ θ : ℝ in 0..2 * Real.pi,
        ‖deriv (spijkerResolventCoefficientCurve A u v R) θ‖) ≤
      2 * Real.pi * n * C

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

/-- Integration by parts converts the Cauchy moment into the arc length of
the scalar resolvent coefficient. -/
lemma norm_spijkerMoment_le_arcLength
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R D : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) (k : ℕ)
    (hderivInt : IntervalIntegrable
      (fun θ : ℝ => deriv
        (spijkerResolventCoefficientCurve A u v R) θ)
      volume 0 (2 * Real.pi))
    (hderivBound :
      (∫ θ : ℝ in 0..2 * Real.pi,
        ‖deriv (spijkerResolventCoefficientCurve A u v R) θ‖) ≤ D) :
    ‖∫ θ : ℝ in 0..2 * Real.pi,
        circleMap 0 R θ ^ (k + 1) *
          spijkerResolventCoefficientCurve A u v R θ‖ ≤
      R ^ (k + 1) / (k + 1) * D := by
  let U : ℝ → ℂ := fun θ =>
    ((((k + 1 : ℕ) : ℝ) : ℂ) * I)⁻¹ * circleMap 0 R θ ^ (k + 1)
  let q : ℝ → ℂ := spijkerResolventCoefficientCurve A u v R
  let p : ℝ → ℂ := fun θ => circleMap 0 R θ ^ (k + 1)
  have hUderiv : ∀ θ : ℝ, HasDerivAt U (p θ) θ := by
    intro θ
    exact hasDerivAt_spijkerPowerAntiderivative R k θ
  have hqderiv : ∀ θ : ℝ, HasDerivAt q (deriv q θ) θ := by
    intro θ
    exact (spijkerResolventCoefficientCurve_differentiableAt
      A u v hK hR θ).hasDerivAt
  have hpInt : IntervalIntegrable p volume 0 (2 * Real.pi) :=
    ((continuous_circleMap 0 R).pow (k + 1)).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := U) (v := q) (u' := p) (v' := fun θ => deriv q θ)
    (fun θ _hθ => hUderiv θ) (fun θ _hθ => hqderiv θ)
    hpInt hderivInt
  have hUend : U (2 * Real.pi) = U 0 := by
    dsimp only [U]
    congr 2
    exact (periodic_circleMap 0 R).eq
  have hqend : q (2 * Real.pi) = q 0 := by
    exact ((periodic_circleMap 0 R).comp
      (spijkerResolventCoefficient A u v)).eq
  rw [hUend, hqend, sub_self, zero_sub] at hibp
  have hmoment :
      (∫ θ : ℝ in 0..2 * Real.pi, p θ * q θ) =
        -(∫ θ : ℝ in 0..2 * Real.pi, U θ * deriv q θ) := by
    have hneg := congrArg Neg.neg hibp
    simpa using hneg.symm
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hUnorm : ∀ θ : ℝ, ‖U θ‖ = R ^ (k + 1) / (k + 1) := by
    intro θ
    dsimp only [U]
    simp [norm_inv, norm_circleMap_zero, abs_of_pos hRpos,
      Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    have hkNorm : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      calc
        _ = ‖((k + 1 : ℕ) : ℂ)‖ := by norm_num
        _ = (k + 1 : ℕ) := Complex.norm_natCast _
        _ = _ := by push_cast; ring
    rw [hkNorm]
    ring
  have hconst0 : 0 ≤ R ^ (k + 1) / (k + 1) := by positivity
  have hgInt : IntervalIntegrable
      (fun θ : ℝ => R ^ (k + 1) / (k + 1) * ‖deriv q θ‖)
      volume 0 (2 * Real.pi) :=
    hderivInt.norm.const_mul _
  rw [hmoment, norm_neg]
  calc
    ‖∫ θ : ℝ in 0..2 * Real.pi, U θ * deriv q θ‖ ≤
        ∫ θ : ℝ in 0..2 * Real.pi,
          R ^ (k + 1) / (k + 1) * ‖deriv q θ‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le Real.two_pi_pos.le
      · filter_upwards with θ _hθ
        rw [norm_mul, hUnorm θ]
      · exact hgInt
    _ = R ^ (k + 1) / (k + 1) *
        (∫ θ : ℝ in 0..2 * Real.pi, ‖deriv q θ‖) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ R ^ (k + 1) / (k + 1) * D :=
      mul_le_mul_of_nonneg_left hderivBound hconst0

/-- Unit Euclidean coefficients inherit the Kreiss resolvent bound on an
exterior circle. -/
lemma norm_spijkerResolventCoefficient_le
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖spijkerResolventCoefficient A u v z‖ ≤ K / (R - 1) := by
  have hRsub : 0 < R - 1 := sub_pos.mpr hR
  have hznorm : ‖z‖ = R := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hres : ‖resolvent A z‖ ≤ K / (R - 1) := by
    apply (le_div_iff₀ hRsub).2
    rw [mul_comm, ← hznorm]
    exact (hK z (by simpa [hznorm] using hR)).2
  let M : CMatrix n n := fun i j => resolvent A z i j
  let T := (complexMatrixEuclideanLin M).toContinuousLinearMap
  have hTnorm : ‖T‖ = ‖resolvent A z‖ := by
    calc
      ‖T‖ = complexMatrixOp2 M :=
        (complexMatrixOp2_eq_norm_euclideanLin M).symm
      _ = ‖CStarMatrix.ofMatrix (M : Matrix (Fin n) (Fin n) ℂ)‖ :=
        (cstarMatrix_norm_eq_complexMatrixOp2 M).symm
      _ = ‖resolvent A z‖ := by rfl
  calc
    ‖spijkerResolventCoefficient A u v z‖ =
        ‖inner ℂ v (T u)‖ := by rfl
    _ ≤ ‖v‖ * ‖T u‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖T‖ * ‖u‖) := by
      gcongr
      exact T.le_opNorm u
    _ = ‖T‖ := by rw [hu, hv]; ring
    _ = ‖resolvent A z‖ := hTnorm
    _ ≤ K / (R - 1) := hres

/-- Spijker's arc-length bound plus integration by parts gives the sharp
scalar coefficient estimate on every exterior circle. -/
lemma norm_cstarMatrixEuclideanCoefficient_pow_le_of_spijker
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (k : ℕ) :
    ‖cstarMatrixEuclideanCoefficientCLM u v (A ^ k)‖ ≤
      R ^ (k + 1) / (k + 1) * (n * (K / (R - 1))) := by
  have hK0 : 0 ≤ K := kreissResolventBound_nonneg hK
  have hRsub : 0 < R - 1 := sub_pos.mpr hR
  have hC0 : 0 ≤ K / (R - 1) := div_nonneg hK0 hRsub.le
  have hderivInt :=
    spijkerResolventCoefficientCurve_deriv_intervalIntegrable
      A u v hK hR
  have hderivBound :=
    hS A u v K R (K / (R - 1)) hK hR hC0
      (fun z hz => norm_spijkerResolventCoefficient_le
        A u v hK hR hu hv hz)
  have hmoment := norm_spijkerMoment_le_arcLength
    A u v hK hR k hderivInt hderivBound
  rw [spijkerResolventCoefficient_pow_eq_intervalIntegral
    A u v hK hR k]
  have htwoPi : 0 < 2 * Real.pi := Real.two_pi_pos
  calc
    ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ θ : ℝ in 0..2 * Real.pi,
          circleMap 0 R θ ^ (k + 1) *
            spijkerResolventCoefficientCurve A u v R θ)‖ =
        (2 * Real.pi)⁻¹ *
          ‖∫ θ : ℝ in 0..2 * Real.pi,
            circleMap 0 R θ ^ (k + 1) *
              spijkerResolventCoefficientCurve A u v R θ‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos htwoPi]
    _ ≤ (2 * Real.pi)⁻¹ *
        (R ^ (k + 1) / (k + 1) *
          (2 * Real.pi * n * (K / (R - 1)))) := by
      exact mul_le_mul_of_nonneg_left hmoment (inv_nonneg.mpr htwoPi.le)
    _ = R ^ (k + 1) / (k + 1) * (n * (K / (R - 1))) := by
      field_simp [Real.pi_ne_zero]

/-- Operator-norm form of the Spijker circle estimate. -/
lemma norm_pow_le_of_spijker_circle
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) (k : ℕ) :
    ‖A ^ k‖ ≤ R ^ (k + 1) / (k + 1) * (n * (K / (R - 1))) := by
  let C : ℝ := R ^ (k + 1) / (k + 1) * (n * (K / (R - 1)))
  have hK0 : 0 ≤ K := kreissResolventBound_nonneg hK
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (div_nonneg (pow_nonneg (zero_le_one.trans hR.le) _) (by positivity))
      (mul_nonneg (Nat.cast_nonneg n)
        (div_nonneg hK0 (sub_nonneg.mpr hR.le)))
  let M : CMatrix n n := fun i j => (A ^ k) i j
  let T := (complexMatrixEuclideanLin M).toContinuousLinearMap
  have hT : ‖T‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC0
    intro x y hx hy
    calc
      re (inner ℂ (T x) y) ≤ ‖inner ℂ (T x) y‖ := re_le_norm _
      _ = ‖inner ℂ y (T x)‖ := norm_inner_symm _ _
      _ = ‖cstarMatrixEuclideanCoefficientCLM x y (A ^ k)‖ := by rfl
      _ ≤ C := norm_cstarMatrixEuclideanCoefficient_pow_le_of_spijker
        hS A x y hK hR hx hy k
  calc
    ‖A ^ k‖ = complexMatrixOp2 M := by
      exact cstarMatrix_norm_eq_complexMatrixOp2 M
    _ = ‖T‖ := complexMatrixOp2_eq_norm_euclideanLin M
    _ ≤ C := hT

/-- **Interface form of the sharp reverse Kreiss inequality, pointwise.**

Within this module the only mathematical premise is `SpijkerArcLengthBound n`;
no power bound, Cayley--Hamilton coefficient estimate, or target-bearing
premise is used.  The premise is discharged downstream by
`spijkerArcLengthBound_proved`. -/
theorem norm_pow_le_exp_mul_dim_of_spijker
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ) {K : ℝ}
    (hK : KreissResolventBound A K) (k : ℕ) :
    ‖A ^ k‖ ≤ Real.exp 1 * n * K := by
  let m : ℝ := (k + 1 : ℕ)
  have hm : 0 < m := by positivity
  let R : ℝ := 1 + m⁻¹
  have hR : 1 < R := by
    dsimp only [R]
    exact lt_add_of_pos_right _ (inv_pos.mpr hm)
  have hraw := norm_pow_le_of_spijker_circle hS A hK hR k
  have hK0 : 0 ≤ K := kreissResolventBound_nonneg hK
  have hbase : R ≤ Real.exp (m⁻¹) := by
    dsimp only [R]
    simpa [add_comm] using Real.add_one_le_exp m⁻¹
  have hpow : R ^ (k + 1) ≤ Real.exp 1 := by
    calc
      R ^ (k + 1) ≤ (Real.exp (m⁻¹)) ^ (k + 1) :=
        pow_le_pow_left₀ (zero_lt_one.trans hR).le hbase _
      _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp only [m]
        field_simp
  calc
    ‖A ^ k‖ ≤ R ^ (k + 1) / (k + 1) *
        (n * (K / (R - 1))) := hraw
    _ = R ^ (k + 1) * n * K := by
      dsimp only [R, m]
      field_simp
      push_cast
      ring
    _ ≤ Real.exp 1 * n * K := by
      gcongr

/-- Interface form of the uniform power bound supplied by Spijker's theorem. -/
theorem powerBound_exp_mul_dim_of_spijker
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ) {K : ℝ}
    (hK : KreissResolventBound A K) :
    PowerBound A (Real.exp 1 * n * K) :=
  fun k => norm_pow_le_exp_mul_dim_of_spijker hS A hK k

/-- **Interface form of the literal upper endpoint in Higham's notation:**
`sup_k ‖A^k‖₂ ≤ e n φ(A)`. -/
theorem higham18_kreiss_upper_of_spijker
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    matrixPowerNormSup A ≤
      Real.exp 1 * n * kreissConstant A := by
  apply csSup_le
  · exact ⟨‖A ^ 0‖, 0, rfl⟩
  · intro x hx
    rcases hx with ⟨k, rfl⟩
    exact norm_pow_le_exp_mul_dim_of_spijker hS A
      (kreissResolventBound_kreissConstant A hres hbdd) k

/-- Interface form of the two-sided finite-dimensional Kreiss theorem. -/
theorem higham18_kreiss_two_sided_of_spijker
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    kreissConstant A ≤ matrixPowerNormSup A ∧
      matrixPowerNormSup A ≤ Real.exp 1 * n * kreissConstant A := by
  have hK := kreissResolventBound_kreissConstant A hres hbdd
  have hpowers : BddAbove (matrixPowerNormSet A) := by
    refine ⟨Real.exp 1 * n * kreissConstant A, ?_⟩
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact norm_pow_le_exp_mul_dim_of_spijker hS A hK k
  exact ⟨higham18_kreiss_lower A hpowers,
    higham18_kreiss_upper_of_spijker hS A hres hbdd⟩

end

end NumStability
