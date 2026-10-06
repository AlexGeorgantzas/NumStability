/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28
import NumStability.Analysis.Norms
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage

open scoped BigOperators Interval ComplexConjugate
open MeasureTheory intervalIntegral Complex Real

/-! # Higham Chapter 28: moment representations of Hilbert and Pascal matrices

This module formalizes the moment-matrix paragraph on pp. 518--519.  It proves
the quadratic-form identity for a positive real weight on a parametrized
contour, the `[0,1]` representation of the Hilbert matrix, and both the
positive-angle and printed contour-weight representations of the Pascal
matrix.
-/

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

private theorem integral_exp_int_mul_I (m : ℤ) :
    (∫ θ : ℝ in 0..2 * Real.pi,
        Complex.exp (((m : ℂ) * Complex.I) * (θ : ℂ))) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst m
    rw [if_pos rfl]
    calc
      (∫ θ : ℝ in 0..2 * Real.pi,
          Complex.exp ((((0 : ℤ) : ℂ) * Complex.I) * (θ : ℂ))) =
          (↑(∫ _θ : ℝ in 0..2 * Real.pi, (1 : ℝ)) : ℂ) := by
            rw [← intervalIntegral.integral_ofReal]
            apply intervalIntegral.integral_congr
            intro θ _
            simp
      _ = (2 * Real.pi : ℂ) := by simp
  · rw [if_neg hm]
    have hc : (m : ℂ) * Complex.I ≠ 0 := by
      exact mul_ne_zero (Int.cast_ne_zero.mpr hm) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have hperiod := Complex.exp_int_mul_two_pi_mul_I m
    have hexp : Complex.exp
        (((m : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show ((m : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) =
          (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast
        ring]
      exact hperiod
    rw [hexp]
    simp

private theorem circleMap_one_one (θ : ℝ) :
    circleMap 1 1 θ =
      1 + Complex.exp (Complex.I * (θ : ℂ)) := by
  simp [circleMap]
  ring

private theorem star_circleMap_one_one (θ : ℝ) :
    starRingEnd ℂ (circleMap 1 1 θ) =
      1 + Complex.exp ((-Complex.I) * (θ : ℂ)) := by
  rw [circleMap_one_one]
  simp only [map_add, map_one, starRingEnd_apply]
  congr 1
  change conj (Complex.exp (Complex.I * (θ : ℂ))) =
    Complex.exp ((-Complex.I) * (θ : ℂ))
  rw [← Complex.exp_conj]
  congr 1
  simp

private theorem integral_exp_nat_sub_mul_I (k l : ℕ) :
    (∫ θ : ℝ in 0..2 * Real.pi,
        Complex.exp ((((l : ℂ) - (k : ℂ)) * Complex.I) * (θ : ℂ))) =
      if k = l then (2 * Real.pi : ℂ) else 0 := by
  have h := integral_exp_int_mul_I ((l : ℤ) - (k : ℤ))
  convert h using 1
  · apply intervalIntegral.integral_congr
    intro θ _
    push_cast
    rfl
  · have hiff : ((l : ℤ) - (k : ℤ) = 0) ↔ k = l := by
      constructor
      · intro hzero
        have hcast : (l : ℤ) = (k : ℤ) := sub_eq_zero.mp hzero
        exact (Int.ofNat_inj.mp hcast).symm
      · intro hkl
        subst l
        simp
    by_cases hkl : k = l
    · simp [hkl]
    · have hzero : ¬((l : ℤ) - (k : ℤ) = 0) := fun h => hkl (hiff.mp h)
      simp [hkl, hzero]

private theorem pascalMoment_integrand_expand (i j : ℕ) (θ : ℝ) :
    starRingEnd ℂ (circleMap 1 1 θ) ^ i * circleMap 1 1 θ ^ j =
      ∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (j + 1),
        ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          Complex.exp ((((l : ℂ) - (k : ℂ)) * Complex.I) * (θ : ℂ)) := by
  rw [star_circleMap_one_one, circleMap_one_one]
  rw [show 1 + Complex.exp ((-Complex.I) * (θ : ℂ)) =
      Complex.exp ((-Complex.I) * (θ : ℂ)) + 1 by ring]
  rw [show 1 + Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) + 1 by ring]
  rw [add_pow, add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  calc
    (Complex.exp ((-Complex.I) * (θ : ℂ)) ^ k * (Nat.choose i k : ℂ)) *
          (Complex.exp (Complex.I * (θ : ℂ)) ^ l * (Nat.choose j l : ℂ)) =
        ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          (Complex.exp ((-Complex.I) * (θ : ℂ)) ^ k *
            Complex.exp (Complex.I * (θ : ℂ)) ^ l) := by ring
    _ = ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          Complex.exp ((((l : ℂ) - (k : ℂ)) * Complex.I) * (θ : ℂ)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2
      ring

private theorem pascalMoment_integral_double_sum (i j : ℕ) :
    (∫ θ : ℝ in 0..2 * Real.pi,
        starRingEnd ℂ (circleMap 1 1 θ) ^ i * circleMap 1 1 θ ^ j) =
      ∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (j + 1),
        ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          (if k = l then (2 * Real.pi : ℂ) else 0) := by
  calc
    (∫ θ : ℝ in 0..2 * Real.pi,
        starRingEnd ℂ (circleMap 1 1 θ) ^ i * circleMap 1 1 θ ^ j) =
        ∫ θ : ℝ in 0..2 * Real.pi,
          ∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (j + 1),
            ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
              Complex.exp ((((l : ℂ) - (k : ℂ)) * Complex.I) * (θ : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact pascalMoment_integrand_expand i j θ
    _ = ∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (j + 1),
        ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          (if k = l then (2 * Real.pi : ℂ) else 0) := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [intervalIntegral.integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro l hl
          calc
            (∫ θ : ℝ in 0..2 * Real.pi,
                ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
                  Complex.exp ((((l : ℂ) - (k : ℂ)) * Complex.I) * (θ : ℂ))) =
                ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
                  ∫ θ : ℝ in 0..2 * Real.pi,
                    Complex.exp ((((l : ℂ) - (k : ℂ)) * Complex.I) * (θ : ℂ)) := by
              exact intervalIntegral.integral_const_mul
                ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ))
                (fun θ : ℝ =>
                  Complex.exp ((((l : ℂ) - (k : ℂ)) * Complex.I) * (θ : ℂ)))
            _ = ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
                (if k = l then (2 * Real.pi : ℂ) else 0) := by
              rw [integral_exp_nat_sub_mul_I]
        · intro l hl
          apply Continuous.intervalIntegrable
          fun_prop
      · intro k hk
        apply Continuous.intervalIntegrable
        fun_prop

private theorem pascalMoment_double_sum (i j : ℕ) :
    (∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (j + 1),
        ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          (if k = l then (2 * Real.pi : ℂ) else 0)) =
      (2 * Real.pi : ℂ) * (Nat.choose (i + j) j : ℂ) := by
  classical
  have hinner : ∀ k : ℕ,
      (∑ l ∈ Finset.range (j + 1),
        ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          (if k = l then (2 * Real.pi : ℂ) else 0)) =
        ((Nat.choose i k : ℂ) * (Nat.choose j k : ℂ)) *
          (2 * Real.pi : ℂ) := by
    intro k
    by_cases hk : k ∈ Finset.range (j + 1)
    · rw [Finset.sum_eq_single k]
      · simp
      · intro l hl hlk
        have hkl : k ≠ l := Ne.symm hlk
        simp [hkl]
      · exact fun h => (h hk).elim
    · have hjk : j < k := by
        have hnlt : ¬k < j + 1 := by simpa using hk
        omega
      calc
        (∑ l ∈ Finset.range (j + 1),
            ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
              (if k = l then (2 * Real.pi : ℂ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          have hkl : k ≠ l := by
            intro hkl
            subst l
            exact hk hl
          simp [hkl]
        _ = ((Nat.choose i k : ℂ) * (Nat.choose j k : ℂ)) *
            (2 * Real.pi : ℂ) := by
          rw [Nat.choose_eq_zero_of_lt hjk]
          simp
  calc
    (∑ k ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (j + 1),
        ((Nat.choose i k : ℂ) * (Nat.choose j l : ℂ)) *
          (if k = l then (2 * Real.pi : ℂ) else 0)) =
        ∑ k ∈ Finset.range (i + 1),
          ((Nat.choose i k : ℂ) * (Nat.choose j k : ℂ)) *
            (2 * Real.pi : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hinner k
    _ = (∑ k ∈ Finset.range (i + 1),
          (Nat.choose i k : ℂ) * (Nat.choose j k : ℂ)) *
            (2 * Real.pi : ℂ) := by
      rw [Finset.sum_mul]
    _ = (Nat.choose (i + j) j : ℂ) * (2 * Real.pi : ℂ) := by
      congr 1
      have hgram := pascal_choose_gram i j
      rw [Nat.choose_symm_add] at hgram
      exact_mod_cast hgram
    _ = (2 * Real.pi : ℂ) * (Nat.choose (i + j) j : ℂ) := by ring

/-- Fourier orthogonality and Vandermonde's identity evaluate the unnormalized
Pascal angle moment. -/
theorem pascalMoment_integral (i j : ℕ) :
    (∫ θ : ℝ in 0..2 * Real.pi,
        starRingEnd ℂ (circleMap 1 1 θ) ^ i * circleMap 1 1 θ ^ j) =
      (2 * Real.pi : ℂ) * (Nat.choose (i + j) j : ℂ) := by
  rw [pascalMoment_integral_double_sum]
  exact pascalMoment_double_sum i j

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

/-- Higham, 2nd ed., p. 519: after `z = 1 + exp(iθ)`, the Pascal matrix is
the moment matrix on `[0,2π]` with positive weight `1/(2π)`. -/
theorem pascalMatrix_eq_intervalMomentMatrix (n : ℕ) :
    intervalMomentMatrix n 0 (2 * Real.pi) (circleMap 1 1)
        (fun _ => (2 * Real.pi)⁻¹) =
      fun i j => (pascalMatrix n i j : ℂ) := by
  ext i j
  unfold intervalMomentMatrix
  change (∫ t : ℝ in 0..2 * Real.pi,
      starRingEnd ℂ (circleMap 1 1 t) ^ i.val * circleMap 1 1 t ^ j.val *
        (((2 * Real.pi)⁻¹ : ℝ) : ℂ)) = (pascalMatrix n i j : ℂ)
  calc
    (∫ t : ℝ in 0..2 * Real.pi,
        starRingEnd ℂ (circleMap 1 1 t) ^ i.val * circleMap 1 1 t ^ j.val *
          (((2 * Real.pi)⁻¹ : ℝ) : ℂ)) =
        (∫ t : ℝ in 0..2 * Real.pi,
          starRingEnd ℂ (circleMap 1 1 t) ^ i.val * circleMap 1 1 t ^ j.val) *
            (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
      exact intervalIntegral.integral_mul_const
        (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
        (fun t : ℝ =>
          starRingEnd ℂ (circleMap 1 1 t) ^ i.val * circleMap 1 1 t ^ j.val)
    _ = (pascalMatrix n i j : ℂ) := by
      rw [pascalMoment_integral]
      simp only [pascalMatrix_apply]
      push_cast
      field_simp [Real.pi_ne_zero]

/-- The positive-angle Pascal moment representation at the quadratic-form
level. -/
theorem pascalMatrix_quadraticForm (n : ℕ) (y : CVec n) :
    complexQuadraticForm (fun i j => (pascalMatrix n i j : ℂ)) y =
      (↑(∫ θ : ℝ in 0..2 * Real.pi,
        (2 * Real.pi)⁻¹ *
          Complex.normSq (momentPolynomial (circleMap 1 1) y θ)) : ℂ) := by
  rw [← pascalMatrix_eq_intervalMomentMatrix]
  simpa using intervalMomentMatrix_quadraticForm
    (z := circleMap 1 1) (w := fun _ => (2 * Real.pi)⁻¹)
    (fun i j => pascal_intervalMoment_integrable i j) y

private theorem complex_real_innerProduct_smul_eq (r : ℝ) (z : ℂ) :
    @SMul.smul ℝ ℂ instInnerProductSpaceRealComplex.toSMul r z =
      (r : ℂ) * z := by
  rfl

/-- The Pascal entry is the rotation-invariant average of
`conj(z)^i z^j` on the circle `|z-1|=1`. -/
theorem pascal_circleAverage (i j : ℕ) :
    Real.circleAverage
        (fun z : ℂ => starRingEnd ℂ z ^ i * z ^ j) 1 1 =
      (Nat.choose (i + j) j : ℂ) := by
  rw [Real.circleAverage_def]
  rw [pascalMoment_integral]
  calc
    (2 * Real.pi)⁻¹ •
        ((2 * Real.pi : ℂ) * (Nat.choose (i + j) j : ℂ)) =
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ((2 * Real.pi : ℂ) * (Nat.choose (i + j) j : ℂ))) := by
      exact complex_real_innerProduct_smul_eq _ _
    _ = (Nat.choose (i + j) j : ℂ) := by
      push_cast
      field_simp [Real.pi_ne_zero]

/-- The circle-average identity rewritten as a normalized circle integral. -/
theorem pascal_circleMoment_normalized (i j : ℕ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C((1 : ℂ), 1),
          (z - 1)⁻¹ * (starRingEnd ℂ z ^ i * z ^ j)) =
      (Nat.choose (i + j) j : ℂ) := by
  have h := Real.circleAverage_eq_circleIntegral
    (f := fun z : ℂ => starRingEnd ℂ z ^ i * z ^ j)
    (c := (1 : ℂ)) (R := (1 : ℝ)) one_ne_zero
  calc
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C((1 : ℂ), 1),
          (z - 1)⁻¹ * (starRingEnd ℂ z ^ i * z ^ j)) =
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          (∮ z in C((1 : ℂ), 1),
            (z - 1)⁻¹ • (starRingEnd ℂ z ^ i * z ^ j)) := by
      simp only [smul_eq_mul]
    _ = Real.circleAverage
        (fun z : ℂ => starRingEnd ℂ z ^ i * z ^ j) 1 1 := h.symm
    _ = (Nat.choose (i + j) j : ℂ) := by
      rw [Real.circleAverage_def]
      rw [pascalMoment_integral]
      calc
        (2 * Real.pi)⁻¹ •
            ((2 * Real.pi : ℂ) * (Nat.choose (i + j) j : ℂ)) =
          ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
            ((2 * Real.pi : ℂ) * (Nat.choose (i + j) j : ℂ))) := by
          exact complex_real_innerProduct_smul_eq _ _
        _ = (Nat.choose (i + j) j : ℂ) := by
          push_cast
          field_simp [Real.pi_ne_zero]

/-- Higham, 2nd ed., p. 519: the Pascal entries are moments on
`|z-1|=1` with the corrected weight `(2π i (z-1))⁻¹`. -/
theorem pascal_circleMoment (i j : ℕ) :
    (∮ z in C((1 : ℂ), 1),
        (2 * (Real.pi : ℂ) * Complex.I * (z - 1))⁻¹ *
          (starRingEnd ℂ z ^ i * z ^ j)) =
      (Nat.choose (i + j) j : ℂ) := by
  calc
    (∮ z in C((1 : ℂ), 1),
        (2 * (Real.pi : ℂ) * Complex.I * (z - 1))⁻¹ *
          (starRingEnd ℂ z ^ i * z ^ j)) =
        (∮ z in C((1 : ℂ), 1),
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ((z - 1)⁻¹ * (starRingEnd ℂ z ^ i * z ^ j))) := by
      congr 1
      funext z
      rw [mul_inv_rev]
      ring
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C((1 : ℂ), 1),
          (z - 1)⁻¹ * (starRingEnd ℂ z ^ i * z ^ j)) := by
      exact circleIntegral.integral_const_mul
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹
        (fun z : ℂ => (z - 1)⁻¹ * (starRingEnd ℂ z ^ i * z ^ j)) 1 1
    _ = (Nat.choose (i + j) j : ℂ) := pascal_circleMoment_normalized i j

end NumStability
