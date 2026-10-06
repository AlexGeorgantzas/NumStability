/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-! # The shifted Hilbert finite-section norm

This file proves the precise finite-section estimate behind the statement
`‖H̃ₙ‖₂ = π + O(1 / log n)` on p. 514.  The upper bound is a weighted Schur
test.  The lower bound uses the vector with entries `1 / √(i+1)`.
-/

namespace NumStability

open Filter Asymptotics Set MeasureTheory
open scoped BigOperators Topology Matrix.Norms.L2Operator Interval

/-- The continuous kernel used to compare a weighted Hilbert row with an
integral. -/
noncomputable def shiftedHilbertSchurKernel (a x : ℝ) : ℝ :=
  (Real.sqrt (x / a) * (a + x))⁻¹

/-- An antiderivative of `shiftedHilbertSchurKernel a` on the positive
half-line. -/
noncomputable def shiftedHilbertSchurPrimitive (a x : ℝ) : ℝ :=
  2 * Real.arctan (Real.sqrt (x / a))

lemma shiftedHilbertSchurKernel_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < shiftedHilbertSchurKernel a x := by
  unfold shiftedHilbertSchurKernel
  positivity

lemma shiftedHilbertSchurKernel_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ shiftedHilbertSchurKernel a x := by
  by_cases hzero : x = 0
  · subst x
    simp [shiftedHilbertSchurKernel]
  · exact (shiftedHilbertSchurKernel_pos ha (lt_of_le_of_ne hx (Ne.symm hzero))).le

lemma hasDerivAt_shiftedHilbertSchurPrimitive {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (shiftedHilbertSchurPrimitive a)
      (shiftedHilbertSchurKernel a x) x := by
  have ha0 : a ≠ 0 := ha.ne'
  have hxa : x / a ≠ 0 := div_ne_zero hx.ne' ha0
  have hsqrt : Real.sqrt (x / a) ≠ 0 := (Real.sqrt_pos.2 (div_pos hx ha)).ne'
  have hdiv : HasDerivAt (fun y : ℝ => y / a) (1 / a) x :=
    hasDerivAt_id x |>.div_const a
  have hs := hdiv.sqrt hxa
  have hatan := hs.arctan
  have hsq : Real.sqrt (x / a) ^ 2 = x / a :=
    Real.sq_sqrt (le_of_lt (div_pos hx ha))
  unfold shiftedHilbertSchurPrimitive shiftedHilbertSchurKernel
  convert hatan.const_mul 2 using 1
  rw [hsq]
  field_simp [ha0, hsqrt]

lemma shiftedHilbertSchurKernel_antitoneOn {a u v : ℝ}
    (ha : 0 < a) (hu : 0 < u) (huv : u ≤ v) :
    shiftedHilbertSchurKernel a v ≤ shiftedHilbertSchurKernel a u := by
  have hv : 0 < v := hu.trans_le huv
  unfold shiftedHilbertSchurKernel
  apply inv_anti₀
  · positivity
  · gcongr

lemma shiftedHilbertSchurKernel_integral {a u v : ℝ}
    (ha : 0 < a) (hu : 0 < u) (huv : u ≤ v) :
    (∫ x in u..v, shiftedHilbertSchurKernel a x) =
      shiftedHilbertSchurPrimitive a v - shiftedHilbertSchurPrimitive a u := by
  have hprim : ContinuousOn (shiftedHilbertSchurPrimitive a) (Icc u v) := by
    intro x hx
    exact (hasDerivAt_shiftedHilbertSchurPrimitive ha (hu.trans_le hx.1)).continuousAt.continuousWithinAt
  have hkernel : ContinuousOn (shiftedHilbertSchurKernel a) (Icc u v) := by
    intro x hx
    have hxpos : 0 < x := hu.trans_le hx.1
    unfold shiftedHilbertSchurKernel
    have hbase : ContinuousAt (fun y : ℝ => Real.sqrt (y / a) * (a + y)) x := by
      fun_prop
    exact (hbase.inv₀ (mul_ne_zero
      (Real.sqrt_pos.2 (div_pos hxpos ha)).ne' (by linarith))).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huv
  · exact hprim
  · intro x hx
    exact (hasDerivAt_shiftedHilbertSchurPrimitive ha (hu.trans hx.1)).hasDerivWithinAt
  · exact hkernel.intervalIntegrable_of_Icc huv

/-- A convenient elementary lower bound for arctangent. -/
lemma div_one_add_sq_le_arctan {t : ℝ} (ht : 0 ≤ t) :
    t / (1 + t ^ 2) ≤ Real.arctan t := by
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 + t ^ 2)⁻¹)
      volume 0 t := continuousOn_const.intervalIntegrable_of_Icc ht
  have hrat : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
      volume 0 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht
    exact (continuousOn_const.add ((continuousOn_id' (Icc (0 : ℝ) t)).pow 2)).inv₀
      (fun x hx => by
        change 1 + x ^ 2 ≠ 0
        nlinarith [sq_nonneg x])
  have hmono := intervalIntegral.integral_mono_on ht hconst hrat
      (fun x hx => by
        apply inv_anti₀
        · positivity
        · nlinarith [((sq_le_sq₀ hx.1 ht).2 hx.2)])
  simpa [div_eq_mul_inv] using hmono

/-- On the nonnegative half-line, arctangent lies below the identity. -/
lemma arctan_le_self_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Real.arctan t ≤ t := by
  have hrat : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
      volume 0 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht
    exact (continuousOn_const.add ((continuousOn_id' (Icc (0 : ℝ) t)).pow 2)).inv₀
      (fun x hx => by
        change 1 + x ^ 2 ≠ 0
        nlinarith [sq_nonneg x])
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t :=
    continuousOn_const.intervalIntegrable_of_Icc ht
  have hmono := intervalIntegral.integral_mono_on ht hrat hone
    (fun x hx => by
      have hden : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
      simpa using ((inv_le_one₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)).2 hden))
  simpa using hmono

/-- The first weighted row entry is absorbed by the initial part of the
arctangent integral. -/
lemma shiftedHilbertSchurKernel_one_le_primitive_one {a : ℝ} (ha : 0 < a) :
    shiftedHilbertSchurKernel a 1 ≤ shiftedHilbertSchurPrimitive a 1 := by
  let t := Real.sqrt (1 / a)
  have ht : 0 < t := Real.sqrt_pos.2 (one_div_pos.2 ha)
  have ht0 : t ≠ 0 := ht.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hsq : t ^ 2 = 1 / a := by
    exact Real.sq_sqrt (one_div_nonneg.2 ha.le)
  have hkernel : shiftedHilbertSchurKernel a 1 = t / (1 + t ^ 2) := by
    unfold shiftedHilbertSchurKernel
    change (t * (a + 1))⁻¹ = t / (1 + t ^ 2)
    rw [hsq]
    have hta : t ^ 2 * a = 1 := by
      rw [hsq]
      field_simp [ha0]
    field_simp [ha0, ht0]
    exact hta.symm
  have hprimitive : shiftedHilbertSchurPrimitive a 1 = 2 * Real.arctan t := by
    rfl
  rw [hkernel, hprimitive]
  have hbase := div_one_add_sq_le_arctan ht.le
  have hatan : 0 ≤ Real.arctan t := (Real.arctan_nonneg.2 ht.le)
  nlinarith

/-- Quantitative lower estimate for the row-comparison integral. -/
lemma shiftedHilbertSchurPrimitive_sub_lower {a N : ℝ}
    (ha : 0 < a) (hN : 0 < N) :
    Real.pi - 2 * Real.sqrt (a / N) - 2 / Real.sqrt a ≤
      shiftedHilbertSchurPrimitive a N -
        shiftedHilbertSchurPrimitive a 1 := by
  let A := Real.sqrt (N / a)
  let B := Real.sqrt (1 / a)
  have hA : 0 < A := Real.sqrt_pos.2 (div_pos hN ha)
  have hB : 0 < B := Real.sqrt_pos.2 (one_div_pos.2 ha)
  have ha0 : a ≠ 0 := ha.ne'
  have hN0 : N ≠ 0 := hN.ne'
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have hAinv : A⁻¹ = Real.sqrt (a / N) := by
    unfold A
    rw [Real.sqrt_div hN.le, Real.sqrt_div ha.le]
    field_simp [hsa, hsN]
  have hBform : B = 1 / Real.sqrt a := by
    unfold B
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hrec := Real.arctan_inv_of_pos hA
  have hAtan : Real.arctan A = Real.pi / 2 - Real.arctan A⁻¹ := by
    linarith
  have hAupper := arctan_le_self_of_nonneg (inv_nonneg.2 hA.le)
  have hBupper := arctan_le_self_of_nonneg hB.le
  unfold shiftedHilbertSchurPrimitive
  change Real.pi - 2 * Real.sqrt (a / N) - 2 / Real.sqrt a ≤
    2 * Real.arctan A - 2 * Real.arctan B
  rw [hAinv] at hAupper
  rw [hBform] at hBupper
  rw [hAtan, hAinv, hBform]
  have hA2 : 2 * Real.arctan (Real.sqrt (a / N)) ≤
      2 * Real.sqrt (a / N) :=
    mul_le_mul_of_nonneg_left hAupper (by norm_num)
  have hB2 : 2 * Real.arctan (1 / Real.sqrt a) ≤
      2 * (1 / Real.sqrt a) :=
    mul_le_mul_of_nonneg_left hBupper (by norm_num)
  calc
    Real.pi - 2 * Real.sqrt (a / N) - 2 / Real.sqrt a =
        (Real.pi - 2 * Real.sqrt (a / N)) -
          2 * (1 / Real.sqrt a) := by ring
    _ ≤ (Real.pi - 2 * Real.arctan (Real.sqrt (a / N))) -
          2 * Real.arctan (1 / Real.sqrt a) :=
      sub_le_sub (sub_le_sub_left hA2 Real.pi) hB2
    _ = 2 * (Real.pi / 2 - Real.arctan (Real.sqrt (a / N))) -
          2 * Real.arctan (1 / Real.sqrt a) := by ring

/-- Lower integral comparison for a finite weighted row. -/
lemma shiftedHilbertSchurPrimitive_sub_le_sum (a : ℝ) (ha : 0 < a) (n : ℕ) :
    shiftedHilbertSchurPrimitive a (n + 1) -
        shiftedHilbertSchurPrimitive a 1 ≤
      ∑ j : Fin n, shiftedHilbertSchurKernel a (j.val + 1) := by
  have hanti : AntitoneOn (shiftedHilbertSchurKernel a)
      (Icc (1 : ℝ) (1 + n)) := by
    intro u hu v hv huv
    exact shiftedHilbertSchurKernel_antitoneOn ha (by linarith [hu.1]) huv
  have hsum := hanti.integral_le_sum
  rw [shiftedHilbertSchurKernel_integral ha (by norm_num)
    (by exact le_add_of_nonneg_right (Nat.cast_nonneg n) : (1 : ℝ) ≤ 1 + n)] at hsum
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => shiftedHilbertSchurKernel a (j + 1)) n]
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hsum

/-- Every finite weighted shifted-Hilbert row sum is bounded by `π`. -/
lemma shiftedHilbertSchur_sum_le_pi (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∑ j : Fin n, shiftedHilbertSchurKernel a (j.val + 1)) ≤ Real.pi := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => shiftedHilbertSchurKernel a (j + 1)) n]
  cases n with
  | zero => simp [Real.pi_pos.le]
  | succ m =>
      have hanti : AntitoneOn (shiftedHilbertSchurKernel a)
          (Icc (1 : ℝ) (1 + m)) := by
        intro u hu v hv huv
        exact shiftedHilbertSchurKernel_antitoneOn ha (by linarith [hu.1]) huv
      have htail := hanti.sum_le_integral
      rw [shiftedHilbertSchurKernel_integral ha (by norm_num)
        (by exact le_add_of_nonneg_right (Nat.cast_nonneg m) : (1 : ℝ) ≤ 1 + m)] at htail
      have hfirst := shiftedHilbertSchurKernel_one_le_primitive_one ha
      have hprim_lt : shiftedHilbertSchurPrimitive a (m + 1) < Real.pi := by
        unfold shiftedHilbertSchurPrimitive
        linarith [Real.arctan_lt_pi_div_two (Real.sqrt ((m + 1 : ℝ) / a))]
      rw [Finset.sum_range_succ']
      have htail' :
          (∑ x ∈ Finset.range m,
              shiftedHilbertSchurKernel a (1 + (x + 1 : ℕ))) ≤
            shiftedHilbertSchurPrimitive a (m + 1) -
              shiftedHilbertSchurPrimitive a 1 := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using htail
      norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] at htail' ⊢
      linarith

/-- Weighted Schur's test for finite real symmetric matrices. -/
lemma opNorm2_le_of_weighted_schur {n : ℕ}
    (M : Fin n → Fin n → ℝ) (w : Fin n → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hw : ∀ i, 0 < w i)
    (hM : ∀ i j, 0 ≤ M i j)
    (hsym : ∀ i j, M i j = M j i)
    (hrow : ∀ i, (∑ j : Fin n, M i j * w j) ≤ c * w i) :
    opNorm2 M ≤ c := by
  apply opNorm2_le_of_opNorm2Le M hc
  intro x
  have hrowCS : ∀ i : Fin n,
      (∑ j : Fin n, M i j * x j) ^ 2 ≤
        (∑ j : Fin n, M i j * w j) *
          ∑ j : Fin n, M i j * x j ^ 2 / w j := by
    intro i
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (R := ℝ) Finset.univ
      (r := fun j => M i j * x j)
      (f := fun j => M i j * w j)
      (g := fun j => M i j * x j ^ 2 / w j)
      (fun j hj => mul_nonneg (hM i j) (hw j).le)
      (fun j hj => div_nonneg (mul_nonneg (hM i j) (sq_nonneg (x j))) (hw j).le)
      (fun j hj => by
        field_simp [(hw j).ne'])
    simpa using h
  have hrowSq : ∀ i : Fin n,
      (∑ j : Fin n, M i j * x j) ^ 2 ≤
        (c * w i) * ∑ j : Fin n, M i j * x j ^ 2 / w j := by
    intro i
    exact (hrowCS i).trans (mul_le_mul_of_nonneg_right (hrow i)
      (Finset.sum_nonneg fun j hj =>
        div_nonneg (mul_nonneg (hM i j) (sq_nonneg (x j))) (hw j).le))
  have hsq :
      vecNorm2Sq (matMulVec n M x) ≤ c ^ 2 * vecNorm2Sq x := by
    unfold vecNorm2Sq matMulVec
    calc
      (∑ i : Fin n, (∑ j : Fin n, M i j * x j) ^ 2) ≤
          ∑ i : Fin n,
            (c * w i) * ∑ j : Fin n, M i j * x j ^ 2 / w j :=
        Finset.sum_le_sum fun i hi => hrowSq i
      _ = c * ∑ j : Fin n,
            (x j ^ 2 / w j) * ∑ i : Fin n, M j i * w i := by
        calc
          (∑ i : Fin n, (c * w i) * ∑ j : Fin n, M i j * x j ^ 2 / w j) =
              ∑ i : Fin n, c * (w i * ∑ j : Fin n, M i j * x j ^ 2 / w j) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = c * ∑ i : Fin n,
              (w i * ∑ j : Fin n, M i j * x j ^ 2 / w j) := by
            rw [Finset.mul_sum]
          _ = c * ∑ i : Fin n, ∑ j : Fin n,
              w i * (M i j * x j ^ 2 / w j) := by
            apply congrArg (fun z : ℝ => c * z)
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = c * ∑ j : Fin n, ∑ i : Fin n,
              w i * (M i j * x j ^ 2 / w j) := by
            rw [Finset.sum_comm]
          _ = c * ∑ j : Fin n,
              (x j ^ 2 / w j) * ∑ i : Fin n, M j i * w i := by
            apply congrArg (fun z : ℝ => c * z)
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← hsym i j]
            ring
      _ ≤ c * ∑ j : Fin n, (x j ^ 2 / w j) * (c * w j) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hrow j)
          (div_nonneg (sq_nonneg (x j)) (hw j).le)
      _ = c ^ 2 * ∑ j : Fin n, x j ^ 2 := by
        calc
          c * ∑ j : Fin n, (x j ^ 2 / w j) * (c * w j) =
              ∑ j : Fin n, c * ((x j ^ 2 / w j) * (c * w j)) := by
            rw [Finset.mul_sum]
          _ = ∑ j : Fin n, c ^ 2 * x j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            field_simp [(hw j).ne']
          _ = c ^ 2 * ∑ j : Fin n, x j ^ 2 := by
            rw [Finset.mul_sum]
  apply (sq_le_sq₀ (vecNorm2_nonneg _) (mul_nonneg hc (vecNorm2_nonneg _))).mp
  rw [vecNorm2_sq, mul_pow, vecNorm2_sq]
  exact hsq

/-- Positive Schur weights for the shifted Hilbert matrix. -/
noncomputable def shiftedHilbertSchurWeight {n : ℕ} (i : Fin n) : ℝ :=
  (Real.sqrt (i.val + 1 : ℝ))⁻¹

lemma shiftedHilbertSchurWeight_pos {n : ℕ} (i : Fin n) :
    0 < shiftedHilbertSchurWeight i := by
  unfold shiftedHilbertSchurWeight
  positivity

lemma shiftedHilbert_entry_mul_weight {n : ℕ} (i j : Fin n) :
    shiftedHilbertMatrix n i j * shiftedHilbertSchurWeight j =
      shiftedHilbertSchurWeight i *
        shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by
  have hai : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
  have haj : (0 : ℝ) < (j.val : ℝ) + 1 := by positivity
  have hsi : Real.sqrt (i.val + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.2 hai).ne'
  have hsj : Real.sqrt (j.val + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.2 haj).ne'
  unfold shiftedHilbertMatrix shiftedHilbertSchurWeight shiftedHilbertSchurKernel
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [Real.sqrt_div haj.le]
  field_simp [hsi, hsj]
  ring

lemma shiftedHilbert_weighted_row_le (n : ℕ) (i : Fin n) :
    (∑ j : Fin n,
        shiftedHilbertMatrix n i j * shiftedHilbertSchurWeight j) ≤
      Real.pi * shiftedHilbertSchurWeight i := by
  calc
    (∑ j : Fin n,
        shiftedHilbertMatrix n i j * shiftedHilbertSchurWeight j) =
        shiftedHilbertSchurWeight i *
          ∑ j : Fin n,
            shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact shiftedHilbert_entry_mul_weight i j
    _ ≤ shiftedHilbertSchurWeight i * Real.pi := by
      exact mul_le_mul_of_nonneg_left
        (shiftedHilbertSchur_sum_le_pi (i.val + 1) (by positivity) n)
        (shiftedHilbertSchurWeight_pos i).le
    _ = Real.pi * shiftedHilbertSchurWeight i := mul_comm _ _

/-- Hilbert's sharp constant gives the uniform upper bound for every finite
shifted-Hilbert section. -/
theorem opNorm2_shiftedHilbert_le_pi (n : ℕ) :
    opNorm2 (shiftedHilbertMatrix n) ≤ Real.pi := by
  apply opNorm2_le_of_weighted_schur
    (shiftedHilbertMatrix n) shiftedHilbertSchurWeight Real.pi_pos.le
  · exact shiftedHilbertSchurWeight_pos
  · intro i j
    unfold shiftedHilbertMatrix
    positivity
  · intro i j
    unfold shiftedHilbertMatrix
    congr 2
    omega
  · exact shiftedHilbert_weighted_row_le n

/-- A telescoping majorant for `1 / √(x+1)`. -/
lemma inv_sqrt_add_one_le_two_sqrt_sub {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.sqrt (x + 1) ≤
      2 * (Real.sqrt (x + 1) - Real.sqrt x) := by
  let p := Real.sqrt (x + 1)
  let q := Real.sqrt x
  have hp : 0 < p := Real.sqrt_pos.2 (by linarith)
  have hp2 : p ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = x := Real.sq_sqrt hx
  change 1 / p ≤ 2 * (p - q)
  apply (div_le_iff₀ hp).2
  nlinarith [sq_nonneg (p - q)]

/-- The first elementary error sum in the Hilbert lower bound. -/
lemma sum_inv_sqrt_succ_le_two_sqrt (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / Real.sqrt (k + 1 : ℝ)) ≤
      2 * Real.sqrt n := by
  calc
    (∑ k ∈ Finset.range n, 1 / Real.sqrt (k + 1 : ℝ)) ≤
        ∑ k ∈ Finset.range n,
          2 * (Real.sqrt (k + 1 : ℝ) - Real.sqrt k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact inv_sqrt_add_one_le_two_sqrt_sub (by positivity)
    _ = 2 * Real.sqrt n := by
      rw [← Finset.mul_sum]
      have htel := Finset.sum_range_sub'
        (fun k : ℕ => Real.sqrt (k : ℝ)) n
      simp only [Nat.cast_add, Nat.cast_one] at htel
      have htel' : (∑ k ∈ Finset.range n,
          (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k)) = Real.sqrt n := by
        calc
          (∑ k ∈ Finset.range n,
              (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k)) =
              -(∑ k ∈ Finset.range n,
                (Real.sqrt k - Real.sqrt ((k : ℝ) + 1))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = Real.sqrt n := by rw [htel]; simp
      rw [htel']

/-- A summable telescoping majorant for `1 / (x√x)`.  The constant six is
chosen to keep the proof elementary; sharpness is irrelevant here. -/
lemma inv_mul_inv_sqrt_le_six_telescope {x : ℝ} (hx : 1 ≤ x) :
    1 / (x * Real.sqrt x) ≤
      6 * (1 / Real.sqrt x - 1 / Real.sqrt (x + 1)) := by
  let p := Real.sqrt x
  let q := Real.sqrt (x + 1)
  have hp : 0 < p := Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) hx)
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hp2 : p ^ 2 = x := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hqle : q ≤ 2 * p := by
    apply (sq_le_sq₀ hq.le (by positivity)).1
    rw [hq2]
    nlinarith
  change 1 / (x * p) ≤ 6 * (1 / p - 1 / q)
  field_simp [hp.ne', hq.ne']
  nlinarith [mul_nonneg hq.le (sub_nonneg.2 hqle),
    mul_nonneg hp.le (sub_nonneg.2 hqle)]

/-- The second elementary error sum in the Hilbert lower bound is uniformly
bounded. -/
lemma sum_inv_mul_sqrt_succ_le_six (n : ℕ) :
    (∑ k ∈ Finset.range n,
      1 / ((k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ))) ≤ 6 := by
  calc
    (∑ k ∈ Finset.range n,
        1 / ((k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ))) ≤
        ∑ k ∈ Finset.range n,
          6 * (1 / Real.sqrt (k + 1 : ℝ) -
            1 / Real.sqrt ((k + 1 : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact inv_mul_inv_sqrt_le_six_telescope
        (x := (k + 1 : ℝ)) (by norm_num)
    _ ≤ 6 := by
      rw [← Finset.mul_sum]
      have htel := Finset.sum_range_sub'
        (fun k : ℕ => 1 / Real.sqrt (k + 1 : ℝ)) n
      simp only [Nat.cast_add, Nat.cast_one] at htel
      rw [htel]
      have hnonneg : 0 ≤ 1 / Real.sqrt (n + 1 : ℝ) := by positivity
      norm_num

lemma shiftedHilbertSchurWeight_sq {n : ℕ} (i : Fin n) :
    shiftedHilbertSchurWeight i ^ 2 = 1 / (i.val + 1 : ℝ) := by
  have hpos : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
  have hs : Real.sqrt ((i.val : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  unfold shiftedHilbertSchurWeight
  rw [inv_pow, Real.sq_sqrt hpos.le]
  simp only [one_div]

lemma shiftedHilbert_weighted_entry_product {n : ℕ} (i j : Fin n) :
    shiftedHilbertSchurWeight i * shiftedHilbertMatrix n i j *
        shiftedHilbertSchurWeight j =
      (1 / (i.val + 1 : ℝ)) *
        shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by
  calc
    shiftedHilbertSchurWeight i * shiftedHilbertMatrix n i j *
          shiftedHilbertSchurWeight j =
        shiftedHilbertSchurWeight i *
          (shiftedHilbertMatrix n i j * shiftedHilbertSchurWeight j) := by ring
    _ = shiftedHilbertSchurWeight i *
          (shiftedHilbertSchurWeight i *
            shiftedHilbertSchurKernel (i.val + 1) (j.val + 1)) := by
      rw [shiftedHilbert_entry_mul_weight]
    _ = shiftedHilbertSchurWeight i ^ 2 *
          shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by ring
    _ = (1 / (i.val + 1 : ℝ)) *
          shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by
      rw [shiftedHilbertSchurWeight_sq]

lemma shiftedHilbert_weight_quadratic (n : ℕ) :
    finiteQuadraticForm (shiftedHilbertMatrix n)
        (fun i => shiftedHilbertSchurWeight i) =
      ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
        ∑ j : Fin n,
          shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by
  rw [finiteQuadraticForm_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact shiftedHilbert_weighted_entry_product i j

lemma shiftedHilbert_weight_norm_sq (n : ℕ) :
    finiteVecNorm2Sq (fun i : Fin n => shiftedHilbertSchurWeight i) =
      ∑ i : Fin n, 1 / (i.val + 1 : ℝ) := by
  unfold finiteVecNorm2Sq
  apply Finset.sum_congr rfl
  intro i hi
  exact shiftedHilbertSchurWeight_sq i

lemma shiftedHilbertSchur_row_lower (n : ℕ) (i : Fin n) :
    Real.pi - 2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) -
        2 / Real.sqrt (i.val + 1 : ℝ) ≤
      ∑ j : Fin n,
        shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by
  exact (shiftedHilbertSchurPrimitive_sub_lower
    (a := (i.val + 1 : ℝ)) (N := (n + 1 : ℝ)) (by positivity) (by positivity)).trans
      (shiftedHilbertSchurPrimitive_sub_le_sum
        (i.val + 1 : ℝ) (by positivity) n)

lemma shiftedHilbert_error_first_identity {n : ℕ} (i : Fin n) :
    (1 / (i.val + 1 : ℝ)) *
        (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ))) =
      (2 / Real.sqrt (n + 1 : ℝ)) *
        (1 / Real.sqrt (i.val + 1 : ℝ)) := by
  have hai : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsi : Real.sqrt ((i.val : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hai).ne'
  have hsN : Real.sqrt ((n : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  rw [Real.sqrt_div hai.le]
  field_simp [hsi, hsN]
  nlinarith [Real.sq_sqrt hai.le]

lemma shiftedHilbert_weighted_error_sum_le_sixteen (n : ℕ) :
    (∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
      (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) +
        2 / Real.sqrt (i.val + 1 : ℝ))) ≤ 16 := by
  have hfirst :
      (∑ i : Fin n, 1 / Real.sqrt (i.val + 1 : ℝ)) ≤
        2 * Real.sqrt n := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => 1 / Real.sqrt (k + 1 : ℝ)) n]
    exact sum_inv_sqrt_succ_le_two_sqrt n
  have hsecond :
      (∑ i : Fin n,
        1 / ((i.val + 1 : ℝ) * Real.sqrt (i.val + 1 : ℝ))) ≤ 6 := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => 1 / ((k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ))) n]
    exact sum_inv_mul_sqrt_succ_le_six n
  have hcoef : 0 ≤ 2 / Real.sqrt (n + 1 : ℝ) := by positivity
  have hfirstScaled :
      (2 / Real.sqrt (n + 1 : ℝ)) *
          (∑ i : Fin n, 1 / Real.sqrt (i.val + 1 : ℝ)) ≤ 4 := by
    calc
      (2 / Real.sqrt (n + 1 : ℝ)) *
          (∑ i : Fin n, 1 / Real.sqrt (i.val + 1 : ℝ)) ≤
          (2 / Real.sqrt (n + 1 : ℝ)) * (2 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hfirst hcoef
      _ = 4 * (Real.sqrt n / Real.sqrt (n + 1 : ℝ)) := by ring
      _ ≤ 4 := by
        have hsN : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
        have hsle : Real.sqrt n ≤ Real.sqrt (n + 1 : ℝ) := by
          exact Real.sqrt_le_sqrt (by norm_num)
        have hratio : Real.sqrt n / Real.sqrt (n + 1 : ℝ) ≤ 1 :=
          (div_le_one₀ hsN).2 hsle
        linarith
  calc
    (∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
        (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) +
          2 / Real.sqrt (i.val + 1 : ℝ))) =
        (2 / Real.sqrt (n + 1 : ℝ)) *
            (∑ i : Fin n, 1 / Real.sqrt (i.val + 1 : ℝ)) +
          2 * (∑ i : Fin n,
            1 / ((i.val + 1 : ℝ) * Real.sqrt (i.val + 1 : ℝ))) := by
      calc
        (∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
            (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) +
              2 / Real.sqrt (i.val + 1 : ℝ))) =
            (∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
              (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)))) +
            ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
              (2 / Real.sqrt (i.val + 1 : ℝ)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i : Fin n,
              (2 / Real.sqrt (n + 1 : ℝ)) *
                (1 / Real.sqrt (i.val + 1 : ℝ))) +
            ∑ i : Fin n, 2 *
              (1 / ((i.val + 1 : ℝ) * Real.sqrt (i.val + 1 : ℝ))) := by
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro i hi
            exact shiftedHilbert_error_first_identity i
          · apply Finset.sum_congr rfl
            intro i hi
            have hai : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
            have hsi : Real.sqrt ((i.val : ℝ) + 1) ≠ 0 :=
              (Real.sqrt_pos.2 hai).ne'
            field_simp [hai.ne', hsi]
        _ = (2 / Real.sqrt (n + 1 : ℝ)) *
              (∑ i : Fin n, 1 / Real.sqrt (i.val + 1 : ℝ)) +
            2 * (∑ i : Fin n,
              1 / ((i.val + 1 : ℝ) * Real.sqrt (i.val + 1 : ℝ))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 + 2 * 6 := add_le_add hfirstScaled
      (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = 16 := by norm_num

/-- The harmonic test-vector Rayleigh quotient is within `16` (before
normalization) of `π` times its squared norm. -/
lemma shiftedHilbert_quadratic_lower (n : ℕ) :
    Real.pi * (∑ i : Fin n, 1 / (i.val + 1 : ℝ)) - 16 ≤
      finiteQuadraticForm (shiftedHilbertMatrix n)
        (fun i => shiftedHilbertSchurWeight i) := by
  rw [shiftedHilbert_weight_quadratic]
  have herr := shiftedHilbert_weighted_error_sum_le_sixteen n
  calc
    Real.pi * (∑ i : Fin n, 1 / (i.val + 1 : ℝ)) - 16 ≤
        Real.pi * (∑ i : Fin n, 1 / (i.val + 1 : ℝ)) -
          ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
            (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) +
              2 / Real.sqrt (i.val + 1 : ℝ)) :=
      sub_le_sub_left herr _
    _ = ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
          (Real.pi - 2 * Real.sqrt
              ((i.val + 1 : ℝ) / (n + 1 : ℝ)) -
            2 / Real.sqrt (i.val + 1 : ℝ)) := by
      calc
        Real.pi * (∑ i : Fin n, 1 / (i.val + 1 : ℝ)) -
            ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
              (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) +
                2 / Real.sqrt (i.val + 1 : ℝ)) =
            (∑ i : Fin n, (1 / (i.val + 1 : ℝ)) * Real.pi) -
              ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
                (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) +
                   2 / Real.sqrt (i.val + 1 : ℝ)) := by
          rw [mul_comm Real.pi, Finset.sum_mul]
        _ = ∑ i : Fin n,
            ((1 / (i.val + 1 : ℝ)) * Real.pi -
              (1 / (i.val + 1 : ℝ)) *
                (2 * Real.sqrt ((i.val + 1 : ℝ) / (n + 1 : ℝ)) +
                  2 / Real.sqrt (i.val + 1 : ℝ))) :=
          by rw [Finset.sum_sub_distrib]
        _ = ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
            (Real.pi - 2 * Real.sqrt
                ((i.val + 1 : ℝ) / (n + 1 : ℝ)) -
              2 / Real.sqrt (i.val + 1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ ≤ ∑ i : Fin n, (1 / (i.val + 1 : ℝ)) *
          ∑ j : Fin n,
            shiftedHilbertSchurKernel (i.val + 1) (j.val + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (shiftedHilbertSchur_row_lower n i)
        (by positivity)

/-- Rayleigh lower bound in harmonic-denominator form. -/
theorem pi_sub_sixteen_div_harmonic_le_opNorm2_shiftedHilbert
    (n : ℕ) (hn : 0 < n) :
    Real.pi - 16 / (∑ i : Fin n, 1 / (i.val + 1 : ℝ)) ≤
      opNorm2 (shiftedHilbertMatrix n) := by
  let D : ℝ := ∑ i : Fin n, 1 / (i.val + 1 : ℝ)
  have hDpos : 0 < D := by
    let i0 : Fin n := ⟨0, hn⟩
    have hnonneg : ∀ i : Fin n, i ∈ (Finset.univ : Finset (Fin n)) →
        0 ≤ 1 / (i.val + 1 : ℝ) := by
      intro i hi
      positivity
    have hzero : i0 ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hterm : 0 < 1 / (i0.val + 1 : ℝ) := by positivity
    exact Finset.sum_pos' hnonneg ⟨i0, hzero, hterm⟩
  have hray :
      finiteQuadraticForm (shiftedHilbertMatrix n)
          (fun i => shiftedHilbertSchurWeight i) ≤
        opNorm2 (shiftedHilbertMatrix n) * D := by
    have h := finiteQuadraticForm_le_of_finiteOpNorm2Le
      (shiftedHilbertMatrix n)
      (finiteOpNorm2Le_of_opNorm2Le (shiftedHilbertMatrix n)
        (opNorm2Le_opNorm2 (shiftedHilbertMatrix n)))
      (fun i => shiftedHilbertSchurWeight i)
    rw [shiftedHilbert_weight_norm_sq] at h
    exact h
  have hprod : Real.pi * D - 16 ≤
      opNorm2 (shiftedHilbertMatrix n) * D :=
    (shiftedHilbert_quadratic_lower n).trans hray
  have hdiv : (Real.pi * D - 16) / D ≤
      opNorm2 (shiftedHilbertMatrix n) :=
    (div_le_iff₀ hDpos).2 (by simpa [mul_comm] using hprod)
  change Real.pi - 16 / D ≤ opNorm2 (shiftedHilbertMatrix n)
  convert hdiv using 1
  field_simp [hDpos.ne']

/-- The harmonic denominator dominates the corresponding logarithm. -/
lemma log_succ_le_shiftedHilbert_harmonic (n : ℕ) :
    Real.log (n + 1 : ℝ) ≤ ∑ i : Fin n, 1 / (i.val + 1 : ℝ) := by
  have hanti : AntitoneOn (fun x : ℝ => 1 / x)
      (Icc (1 : ℝ) (1 + n)) := by
    intro x hx y hy hxy
    apply one_div_le_one_div_of_le
    · linarith [hx.1]
    · exact hxy
  have hsum := hanti.integral_le_sum
  rw [integral_one_div_of_pos (by norm_num)
    (by positivity : (0 : ℝ) < 1 + n)] at hsum
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => 1 / (k + 1 : ℝ)) n]
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hsum

/-- Explicit logarithmic lower bound for the finite-section norm. -/
theorem pi_sub_sixteen_div_log_succ_le_opNorm2_shiftedHilbert
    (n : ℕ) (hn : 0 < n) :
    Real.pi - 16 / Real.log (n + 1 : ℝ) ≤
      opNorm2 (shiftedHilbertMatrix n) := by
  let D : ℝ := ∑ i : Fin n, 1 / (i.val + 1 : ℝ)
  have hbase := pi_sub_sixteen_div_harmonic_le_opNorm2_shiftedHilbert n hn
  change Real.pi - 16 / D ≤ opNorm2 (shiftedHilbertMatrix n) at hbase
  have hlogpos : 0 < Real.log (n + 1 : ℝ) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hn)
  have hD : Real.log (n + 1 : ℝ) ≤ D :=
    log_succ_le_shiftedHilbert_harmonic n
  have hfrac : 16 / D ≤ 16 / Real.log (n + 1 : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) hlogpos hD
  linarith

/-- Pointwise error estimate in the exact scale used by the source's
`O(1/log n)` statement. -/
lemma abs_opNorm2_shiftedHilbert_sub_pi_le (n : ℕ) (hn : 2 ≤ n) :
    |opNorm2 (shiftedHilbertMatrix n) - Real.pi| ≤
      16 * (1 / Real.log n) := by
  have hupper := opNorm2_shiftedHilbert_le_pi n
  have hlower := pi_sub_sixteen_div_log_succ_le_opNorm2_shiftedHilbert n
    (by omega)
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogs : 0 < Real.log (n + 1 : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
  have hlogle : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) :=
    Real.log_le_log (by positivity) (by norm_num)
  have hinv : 1 / Real.log (n + 1 : ℝ) ≤ 1 / Real.log n := by
    exact one_div_le_one_div_of_le hlogn hlogle
  rw [abs_of_nonpos (sub_nonpos.2 hupper), neg_sub]
  calc
    Real.pi - opNorm2 (shiftedHilbertMatrix n) ≤
        16 / Real.log (n + 1 : ℝ) := by linarith
    _ ≤ 16 * (1 / Real.log n) := by
      have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 16)
      simpa [div_eq_mul_inv] using this

/-- Higham, 2nd ed., p. 514: the shifted Hilbert finite sections satisfy
`‖H̃ₙ‖₂ = π + O(1 / log n)`. -/
theorem shiftedHilbert_norm_asymptotic : ShiftedHilbertNormAsymptotic := by
  apply IsBigO.of_bound 16
  filter_upwards [eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
  have h := abs_opNorm2_shiftedHilbert_sub_pi_le n hn
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  simpa [Real.norm_eq_abs, abs_of_pos hlog,
    abs_of_pos (one_div_pos.2 hlog)] using h

end NumStability
