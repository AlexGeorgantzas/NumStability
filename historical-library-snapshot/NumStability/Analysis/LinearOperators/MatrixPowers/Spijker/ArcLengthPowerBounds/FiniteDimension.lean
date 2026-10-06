import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import NumStability.Analysis.FunctionalCalculus.Resolvent.Analyticity
import NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.DistanceToInstability
import NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.ResolventBound
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ResolventCoefficients.Analytic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.SingularValues.Basic

/-!
# Analysis.LinearOperators.MatrixPowers.Spijker.ArcLengthPowerBounds.FiniteDimension

R07 canonical `reusable` leaf. Declaration-level review groups 7 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.SpijkerArcLengthBound`, `NumStability.norm_cstarMatrixEuclideanCoefficient_pow_le_of_spijker`, `NumStability.norm_pow_le_exp_mul_dim_of_spijker`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped Real Topology ComplexOrder

open Complex Metric Set MeasureTheory

noncomputable section

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

end

end NumStability
