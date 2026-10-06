import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Integral.CircleAverage
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation Moments

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Moments` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators Interval ComplexConjugate

open MeasureTheory intervalIntegral Complex Real

namespace NumStability

/-- The zero-based parametrized moment matrix
`Mᵢⱼ = ∫ conj(z(t))^i z(t)^j w(t) dt`. -/
noncomputable def intervalMomentMatrix
    (n : ℕ) (a b : ℝ) (z : ℝ → ℂ) (w : ℝ → ℝ) : CMatrix n n :=
  fun i j => ∫ t in a..b,
    (starRingEnd ℂ (z t)) ^ i.val * (z t) ^ j.val * (w t : ℂ)

/-- The polynomial `∑ⱼ yⱼ z(t)^j` appearing in `yᴴMy`. -/
noncomputable def momentPolynomial
    {n : ℕ} (z : ℝ → ℂ) (y : CVec n) (t : ℝ) : ℂ :=
  ∑ j : Fin n, y j * (z t) ^ j.val

/-- The complex quadratic form `yᴴMy`. -/
noncomputable def complexQuadraticForm
    {n : ℕ} (M : CMatrix n n) (y : CVec n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (y i) * M i j * y j

/-- Higham, 2nd ed., Section 28.4, pp. 518--519: the quadratic form of a
moment matrix is the integral of the positive-weight squared polynomial. -/
theorem intervalMomentMatrix_quadraticForm
    {n : ℕ} {a b : ℝ} {z : ℝ → ℂ} {w : ℝ → ℝ}
    (hInt : ∀ i j : Fin n, IntervalIntegrable
      (fun t => (starRingEnd ℂ (z t)) ^ i.val * (z t) ^ j.val * (w t : ℂ))
      volume a b)
    (y : CVec n) :
    complexQuadraticForm (intervalMomentMatrix n a b z w) y =
      (↑(∫ t in a..b, w t * Complex.normSq (momentPolynomial z y t)) : ℂ) := by
  unfold complexQuadraticForm intervalMomentMatrix
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (y i) *
          (∫ t in a..b,
            starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ)) * y j) =
        ∑ i : Fin n, ∑ j : Fin n,
          ∫ t in a..b,
            starRingEnd ℂ (y i) *
              (starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ)) * y j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        starRingEnd ℂ (y i) *
              (∫ t in a..b,
                starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ)) * y j =
            (∫ t in a..b,
              starRingEnd ℂ (y i) *
                (starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ))) * y j := by
          exact congrArg (fun q : ℂ => q * y j)
            (intervalIntegral.integral_const_mul
              (a := a) (b := b) (μ := volume) (starRingEnd ℂ (y i))
              (fun t => starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ))).symm
        _ = ∫ t in a..b,
              starRingEnd ℂ (y i) *
                (starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ)) * y j := by
          exact (intervalIntegral.integral_mul_const
            (a := a) (b := b) (μ := volume) (y j)
            (fun t => starRingEnd ℂ (y i) *
              (starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ)))).symm
    _ = ∫ t in a..b,
        ∑ i : Fin n, ∑ j : Fin n,
          starRingEnd ℂ (y i) *
            (starRingEnd ℂ (z t) ^ i.val * z t ^ j.val * (w t : ℂ)) * y j := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_finset_sum]
        intro j _
        exact ((hInt i j).const_mul (starRingEnd ℂ (y i))).mul_const (y j)
      · intro i _
        have hs := IntervalIntegrable.sum Finset.univ fun j _ =>
          ((hInt i j).const_mul (starRingEnd ℂ (y i))).mul_const (y j)
        convert hs using 1
        ext t
        simp
    _ = ∫ t in a..b,
        ((w t * Complex.normSq (momentPolynomial z y t) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only
      rw [Complex.ofReal_mul]
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [momentPolynomial, map_sum, map_mul, map_pow]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A nonnegative weight makes the real part of every moment quadratic form
nonnegative. -/
theorem intervalMomentMatrix_quadraticForm_re_nonneg
    {n : ℕ} {a b : ℝ} {z : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (hw : ∀ t ∈ Set.Icc a b, 0 ≤ w t)
    (hInt : ∀ i j : Fin n, IntervalIntegrable
      (fun t => (starRingEnd ℂ (z t)) ^ i.val * (z t) ^ j.val * (w t : ℂ))
      volume a b)
    (y : CVec n) :
    0 ≤ (complexQuadraticForm (intervalMomentMatrix n a b z w) y).re := by
  rw [intervalMomentMatrix_quadraticForm hInt]
  simp only [ofReal_re]
  exact intervalIntegral.integral_nonneg hab fun t ht =>
    mul_nonneg (hw t ht) (Complex.normSq_nonneg _)

/-- A positive weight makes the moment quadratic form strictly positive once
the parametrization is nondegenerate for nonzero coefficient vectors.  The
explicit support hypothesis records the condition needed to exclude atomic or
otherwise degenerate contours. -/
theorem intervalMomentMatrix_quadraticForm_re_pos
    {n : ℕ} {a b : ℝ} {z : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a < b) (hw : ∀ t, 0 < w t)
    (hInt : ∀ i j : Fin n, IntervalIntegrable
      (fun t => (starRingEnd ℂ (z t)) ^ i.val * (z t) ^ j.val * (w t : ℂ))
      volume a b)
    (hQuadInt : ∀ y : CVec n, IntervalIntegrable
      (fun t => w t * Complex.normSq (momentPolynomial z y t)) volume a b)
    (hNondegenerate : ∀ y : CVec n, y ≠ 0 →
      0 < volume (Function.support (momentPolynomial z y) ∩ Set.Ioc a b))
    {y : CVec n} (hy : y ≠ 0) :
    0 < (complexQuadraticForm (intervalMomentMatrix n a b z w) y).re := by
  rw [intervalMomentMatrix_quadraticForm hInt]
  simp only [ofReal_re]
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun t =>
      mul_nonneg (le_of_lt (hw t)) (Complex.normSq_nonneg _)) (hQuadInt y)]
  refine ⟨hab, ?_⟩
  have hsupp :
      Function.support (fun t => w t * Complex.normSq (momentPolynomial z y t)) ∩ Set.Ioc a b =
        Function.support (momentPolynomial z y) ∩ Set.Ioc a b := by
    ext t
    simp only [Function.mem_support, Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · intro h
      exact ⟨fun hp => h.1 (by simp [hp]), h.2⟩
    · rintro ⟨hp, ht⟩
      refine ⟨mul_ne_zero (hw t).ne' ?_, ht⟩
      exact (Complex.normSq_pos.mpr hp).ne'
  rw [hsupp]
  exact hNondegenerate y hy

/-- The Hilbert moment integrands are interval integrable on `[0,1]`. -/
theorem hilbert_intervalMoment_integrable
    {n : ℕ} (i j : Fin n) :
    IntervalIntegrable
      (fun t : ℝ =>
        starRingEnd ℂ (t : ℂ) ^ i.val * (t : ℂ) ^ j.val * (1 : ℂ))
      volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- Higham, 2nd ed., p. 519: the Hilbert matrix is the moment matrix on
`[0,1]` with `z(t) = t` and unit weight. -/
theorem hilbertMatrix_eq_intervalMomentMatrix (n : ℕ) :
    intervalMomentMatrix n 0 1 (fun t : ℝ => (t : ℂ)) (fun _ => 1) =
      fun i j => (hilbertMatrix n i j : ℂ) := by
  ext i j
  unfold intervalMomentMatrix
  change (∫ t : ℝ in 0..1,
      starRingEnd ℂ (t : ℂ) ^ i.val * (t : ℂ) ^ j.val * (1 : ℂ)) =
    (hilbertMatrix n i j : ℂ)
  have hIntegral : (∫ t : ℝ in 0..1,
      starRingEnd ℂ (t : ℂ) ^ i.val * (t : ℂ) ^ j.val * (1 : ℂ)) =
      (↑(∫ t : ℝ in 0..1, t ^ (i.val + j.val)) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _
    simp [pow_add]
  rw [hIntegral]
  rw [integral_pow]
  simp [hilbertMatrix_apply]

/-- The printed Hilbert moment representation at the quadratic-form level. -/
theorem hilbertMatrix_quadraticForm (n : ℕ) (y : CVec n) :
    complexQuadraticForm (fun i j => (hilbertMatrix n i j : ℂ)) y =
      (↑(∫ t : ℝ in 0..1,
        Complex.normSq (momentPolynomial (fun s : ℝ => (s : ℂ)) y t)) : ℂ) := by
  rw [← hilbertMatrix_eq_intervalMomentMatrix]
  simpa using intervalMomentMatrix_quadraticForm
    (z := fun t : ℝ => (t : ℂ)) (w := fun _ => 1)
    (fun i j => hilbert_intervalMoment_integrable i j) y

/-- The positive constant-weight Pascal angle integrands are interval
integrable. -/
theorem pascal_intervalMoment_integrable
    {n : ℕ} (i j : Fin n) :
    IntervalIntegrable
      (fun θ : ℝ =>
        starRingEnd ℂ (circleMap 1 1 θ) ^ i.val * circleMap 1 1 θ ^ j.val *
          (((2 * Real.pi)⁻¹ : ℝ) : ℂ)) volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  fun_prop

end NumStability
