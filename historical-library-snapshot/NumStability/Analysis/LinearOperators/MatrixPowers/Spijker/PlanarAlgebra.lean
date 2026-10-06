import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational

/-!
# Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAlgebra

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
# Spijker's planar projection proof: algebraic crossing core

For a rational function `P/Q` of order at most `n`, Spijker's 1991 proof
projects the image of a circle onto a real line and observes that every level
is crossed at most `2n` times.  This file formalizes that algebraic assertion.

The key construction is the degree-`2n` polynomial obtained after replacing
complex conjugation on the unit circle by a reflected coefficientwise-
conjugate polynomial.  The final theorem is stated directly for
`RationalOrderCertificate`, works on every centered circle, and counts actual
distinct circle parameters in a half-open turn.
-/





namespace NumStability

open scoped Real Topology ComplexConjugate
open Complex Polynomial Set MeasureTheory

noncomputable section

def spijkerConjugatePolynomial (p : ℂ[X]) : ℂ[X] :=
  p.map (starRingEnd ℂ)

def spijkerCircleConjugateLift (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  (spijkerConjugatePolynomial p).reflect n

lemma spijkerConjugatePolynomial_natDegree_le (p : ℂ[X]) :
    (spijkerConjugatePolynomial p).natDegree ≤ p.natDegree := by
  exact Polynomial.natDegree_map_le

lemma spijkerCircleConjugateLift_natDegree_le {n : ℕ} {p : ℂ[X]}
    (hp : p.natDegree ≤ n) :
    (spijkerCircleConjugateLift n p).natDegree ≤ n := by
  unfold spijkerCircleConjugateLift
  exact (Polynomial.natDegree_reflect_le.trans (by
    rw [max_le_iff]
    exact ⟨le_rfl, (spijkerConjugatePolynomial_natDegree_le p).trans hp⟩))

lemma eval_spijkerConjugatePolynomial (p : ℂ[X]) (z : ℂ) :
    (spijkerConjugatePolynomial p).eval z =
      conj (p.eval (conj z)) := by
  rw [spijkerConjugatePolynomial, Polynomial.eval_map]
  convert Polynomial.eval₂_at_apply (p := p) (starRingEnd ℂ) (conj z) using 1 <;>
    simp

lemma eval_spijkerCircleConjugateLift_of_norm_one
    {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (spijkerCircleConjugateLift n p).eval z = z ^ n * conj (p.eval z) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    simp at hz
  have hzinv0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
  letI : Invertible z⁻¹ := invertibleOfNonzero hzinv0
  have hq : (spijkerConjugatePolynomial p).natDegree ≤ n :=
    (spijkerConjugatePolynomial_natDegree_le p).trans hp
  have hreflect := Polynomial.eval₂_reflect_mul_pow
    (RingHom.id ℂ) z⁻¹ n (spijkerConjugatePolynomial p) hq
  have hconj : conj z = z⁻¹ := (Complex.inv_eq_conj hz).symm
  have hright :
      (spijkerConjugatePolynomial p).eval z⁻¹ = conj (p.eval z) := by
    rw [eval_spijkerConjugatePolynomial, map_inv₀, hconj, inv_inv]
  have hreflect' :
      (spijkerCircleConjugateLift n p).eval z * (z⁻¹) ^ n =
        conj (p.eval z) := by
    simpa [spijkerCircleConjugateLift, hright] using hreflect
  calc
    (spijkerCircleConjugateLift n p).eval z =
        ((spijkerCircleConjugateLift n p).eval z * (z⁻¹) ^ n) * z ^ n := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, mul_one]
    _ = conj (p.eval z) * z ^ n := by rw [hreflect']
    _ = z ^ n * conj (p.eval z) := mul_comm _ _

def spijkerRealProjection (ω w : ℂ) : ℝ := (ω * w).re

def spijkerProjectionCrossingPolynomial
    (n : ℕ) (P Q : ℂ[X]) (ω : ℂ) (x : ℝ) : ℂ[X] :=
  C ω * P * spijkerCircleConjugateLift n Q +
    C (conj ω) * spijkerCircleConjugateLift n P * Q -
      C (2 * (x : ℂ)) * Q * spijkerCircleConjugateLift n Q






























lemma eval_spijkerProjectionCrossingPolynomial_of_norm_one
    {n : ℕ} {P Q : ℂ[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (ω : ℂ) (x : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    (spijkerProjectionCrossingPolynomial n P Q ω x).eval z =
      z ^ n *
        (ω * P.eval z * conj (Q.eval z) +
          conj ω * conj (P.eval z) * Q.eval z -
          2 * (x : ℂ) * Q.eval z * conj (Q.eval z)) := by
  rw [spijkerProjectionCrossingPolynomial,
    Polynomial.eval_sub, Polynomial.eval_add]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [eval_spijkerCircleConjugateLift_of_norm_one hQ hz,
    eval_spijkerCircleConjugateLift_of_norm_one hP hz]
  ring

lemma spijkerProjectionCrossingPolynomial_eval_eq_zero_of_projection_eq
    {n : ℕ} {P Q : ℂ[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (ω : ℂ) (x : ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    (hQz : Q.eval z ≠ 0)
    (hproj : spijkerRealProjection ω (P.eval z / Q.eval z) = x) :
    (spijkerProjectionCrossingPolynomial n P Q ω x).eval z = 0 := by
  rw [eval_spijkerProjectionCrossingPolynomial_of_norm_one hP hQ ω x hz]
  apply mul_eq_zero_of_right
  have hw :
      ω * (P.eval z / Q.eval z) + conj (ω * (P.eval z / Q.eval z)) =
        (2 * x : ℂ) := by
    rw [Complex.add_conj]
    norm_cast
    simpa [spijkerRealProjection] using
      congrArg (fun r : ℝ => 2 * r) hproj
  simp only [map_mul, div_eq_mul_inv, map_inv₀] at hw
  field_simp [hQz] at hw
  linear_combination hw

lemma spijkerRealProjection_eq_of_crossingPolynomial_eval_eq_zero
    {n : ℕ} {P Q : ℂ[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (ω : ℂ) (x : ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    (hQz : Q.eval z ≠ 0)
    (heval : (spijkerProjectionCrossingPolynomial n P Q ω x).eval z = 0) :
    spijkerRealProjection ω (P.eval z / Q.eval z) = x := by
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    simp at hz
  rw [eval_spijkerProjectionCrossingPolynomial_of_norm_one hP hQ ω x hz] at heval
  have hbracket :
      ω * P.eval z * conj (Q.eval z) +
          conj ω * conj (P.eval z) * Q.eval z -
          2 * (x : ℂ) * Q.eval z * conj (Q.eval z) = 0 :=
    (mul_eq_zero.mp heval).resolve_left (pow_ne_zero n hz0)
  have hw :
      ω * (P.eval z / Q.eval z) + conj (ω * (P.eval z / Q.eval z)) =
        (2 * x : ℂ) := by
    simp only [map_mul, div_eq_mul_inv, map_inv₀]
    field_simp [hQz]
    linear_combination hbracket
  rw [Complex.add_conj] at hw
  have hwreal :
      2 * spijkerRealProjection ω (P.eval z / Q.eval z) = 2 * x := by
    norm_cast at hw
  linarith

lemma spijkerProjectionCrossingPolynomial_ne_zero_of_exists_projection_ne
    {n : ℕ} {P Q : ℂ[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (ω : ℂ) (x : ℝ)
    (hex : ∃ z : ℂ, ‖z‖ = 1 ∧ Q.eval z ≠ 0 ∧
      spijkerRealProjection ω (P.eval z / Q.eval z) ≠ x) :
    spijkerProjectionCrossingPolynomial n P Q ω x ≠ 0 := by
  obtain ⟨z, hz, hQz, hne⟩ := hex
  intro hzero
  apply hne
  apply spijkerRealProjection_eq_of_crossingPolynomial_eval_eq_zero
    hP hQ ω x hz hQz
  rw [hzero]
  simp

/-- Polynomial pullback along radial scaling, used to reduce an arbitrary
circle of radius `R` to the unit circle without changing rational order. -/
def spijkerRadialScalePolynomial (R : ℝ) (p : ℂ[X]) : ℂ[X] :=
  p.comp (C (R : ℂ) * X)

lemma spijkerRadialScalePolynomial_natDegree_le
    {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (R : ℝ) :
    (spijkerRadialScalePolynomial R p).natDegree ≤ n := by
  have hlin : (C (R : ℂ) * X).natDegree ≤ 1 := by
    calc
      (C (R : ℂ) * X).natDegree ≤ (C (R : ℂ)).natDegree + X.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + 1 := by simp
      _ = 1 := by norm_num
  calc
    (spijkerRadialScalePolynomial R p).natDegree ≤
        p.natDegree * (C (R : ℂ) * X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ n * 1 := Nat.mul_le_mul hp hlin
    _ = n := by simp

@[simp]
lemma eval_spijkerRadialScalePolynomial
    (R : ℝ) (p : ℂ[X]) (z : ℂ) :
    (spijkerRadialScalePolynomial R p).eval z = p.eval ((R : ℂ) * z) := by
  simp [spijkerRadialScalePolynomial, Polynomial.eval_comp]

lemma radialScale_unitCircle_eq_circleMap (R t : ℝ) :
    (R : ℂ) * circleMap 0 1 t = circleMap 0 R t := by
  simp [circleMap]



































































































/-! ## Exact analytic bridge isolated after root counting -/

/-- Unit complex direction used for planar projections. -/
def spijkerProjectionDirection (θ : ℝ) : ℂ :=
  circleMap 0 1 (-θ)

@[simp]
lemma norm_spijkerProjectionDirection (θ : ℝ) :
    ‖spijkerProjectionDirection θ‖ = 1 := by
  simp [spijkerProjectionDirection, circleMap, Complex.norm_exp]

/-- Real projection of a planar curve in direction `θ`. -/
def spijkerProjectedCurve (γ : ℝ → ℂ) (θ t : ℝ) : ℝ :=
  spijkerRealProjection (spijkerProjectionDirection θ) (γ t)

/-- A continuously differentiable planar curve has continuously
differentiable real projections. -/
lemma spijkerProjectedCurve_contDiff
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (θ : ℝ) :
    ContDiff ℝ 1 (spijkerProjectedCurve γ θ) := by
  have hmul : ContDiff ℝ 1
      (fun t : ℝ => spijkerProjectionDirection θ * γ t) :=
    contDiff_const.mul hγ
  simpa [spijkerProjectedCurve, spijkerRealProjection, Function.comp_def] using
    Complex.reCLM.contDiff.comp hmul

/-- Projection cannot increase distance from the origin. -/
lemma abs_spijkerProjectedCurve_le_norm
    (γ : ℝ → ℂ) (θ t : ℝ) :
    |spijkerProjectedCurve γ θ t| ≤ ‖γ t‖ := by
  unfold spijkerProjectedCurve spijkerRealProjection
  calc
    |(spijkerProjectionDirection θ * γ t).re| ≤
        ‖spijkerProjectionDirection θ * γ t‖ := abs_re_le_norm _
    _ = ‖γ t‖ := by
      rw [norm_mul, norm_spijkerProjectionDirection, one_mul]

/-- Total variation of one real projection, expressed by the derivative
integral used in Spijker's equation (6). -/
noncomputable def spijkerProjectedVariation
    (γ : ℝ → ℂ) (θ : ℝ) : ℝ :=
  ∫ t : ℝ in 0..2 * Real.pi,
    |deriv (spijkerProjectedCurve γ θ) t|

/-- The exact standard real-analysis bridge used by Spijker's planar proof.

The first field is equation (6), i.e. the Cauchy--Crofton projection-average
identity.  The second field is the one-dimensional Banach-indicatrix
principle: if every nonconstant level has at most `m` crossings, then total
variation is at most `2m` times the range radius.  All rational-function
algebra and the value `m = 2n` are proved above.  This structure isolates the
two general analytic facts; `MatrixPowersSpijkerPlanarAnalysis` constructs it
from Fubini and a finite layer-cake argument. -/
structure SpijkerPlanarAnalyticBridge : Prop where
  projection_average :
    ∀ (γ : ℝ → ℂ), ContDiff ℝ 1 γ →
      IntervalIntegrable (spijkerProjectedVariation γ) volume
        0 (2 * Real.pi) ∧
      (∫ t : ℝ in 0..2 * Real.pi, ‖deriv γ t‖) =
        (1 / 4 : ℝ) *
          ∫ θ : ℝ in 0..2 * Real.pi, spijkerProjectedVariation γ θ
  crossing_variation :
    ∀ (F : ℝ → ℝ) (m : ℕ) (C : ℝ),
      ContDiff ℝ 1 F → 0 ≤ C →
      (∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), |F t| ≤ C) →
      (∀ x : ℝ,
        (∃ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi), F t ≠ x) →
        ∀ s : Finset ℝ,
          (∀ t ∈ s, t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) →
          (∀ t ∈ s, F t = x) →
          s.card ≤ m) →
      (∫ t : ℝ in 0..2 * Real.pi, |deriv F t|) ≤
        2 * (m : ℝ) * C



































































end
end NumStability
