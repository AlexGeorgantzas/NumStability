/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRank
import NumStability.Algorithms.TestMatrices.Higham28GinibreComplexPairs

/-! # Higham Chapter 28: signed count expectations

This file packages the alternating one-root and two-root counts as integrable
real-Ginibre observables.  The finite combinatorial identity then decomposes
the genuine expected root count into the two signed expectations used by the
iterated-incidence proof.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

noncomputable section

private local instance ginibreSignedExpectationMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- Alternating one-root observable on an `n × n` matrix. -/
def ginibreAlternatingEigenvalueCount (n : ℕ) (A : RSqMat n) : ℝ :=
  ginibreAlternatingCount (realEigenvalueCount n A)

/-- Alternating ordered-pair observable on an `n × n` matrix. -/
def ginibreAlternatingPairEigenvalueCount (n : ℕ) (A : RSqMat n) : ℝ :=
  ginibreAlternatingPairCount (realEigenvalueCount n A)

/-- Expected alternating one-root count. -/
def expectedGinibreAlternatingCount (n : ℕ) : ℝ :=
  ∫ A : RSqMat n, ginibreAlternatingEigenvalueCount n A
    ∂realGinibreMeasure n

/-- Expected alternating ordered-pair count.  This is the `T n` quantity in
the signed two-incidence recurrence. -/
def expectedGinibreAlternatingPairCount (n : ℕ) : ℝ :=
  ∫ A : RSqMat n, ginibreAlternatingPairEigenvalueCount n A
    ∂realGinibreMeasure n

theorem measurable_ginibreAlternatingEigenvalueCount (n : ℕ) :
    Measurable (ginibreAlternatingEigenvalueCount n) := by
  exact (measurable_of_countable (fun r : ℕ => ginibreAlternatingCount r)).comp
    (measurable_realEigenvalueCount n)

theorem measurable_ginibreAlternatingPairEigenvalueCount (n : ℕ) :
    Measurable (ginibreAlternatingPairEigenvalueCount n) := by
  exact (measurable_of_countable
    (fun r : ℕ => ginibreAlternatingPairCount r)).comp
      (measurable_realEigenvalueCount n)

/-- A crude sharp-enough bound for the alternating one-root sum. -/
theorem abs_ginibreAlternatingCount_le (r : ℕ) :
    |ginibreAlternatingCount r| ≤ (r : ℝ) := by
  unfold ginibreAlternatingCount
  calc
    |∑ j ∈ Finset.range r, (-1 : ℝ) ^ j| ≤
        ∑ j ∈ Finset.range r, |(-1 : ℝ) ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (r : ℝ) := by simp

/-- The alternating ordered-pair sum is bounded by the square of the number
of roots. -/
theorem abs_ginibreAlternatingPairCount_le_sq (r : ℕ) :
    |ginibreAlternatingPairCount r| ≤ (r : ℝ) ^ 2 := by
  unfold ginibreAlternatingPairCount
  calc
    |∑ j ∈ Finset.range r,
        ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)| ≤
        ∑ j ∈ Finset.range r,
          |∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range r, (r : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        |∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)| ≤
            ∑ i ∈ Finset.range j, |(-1 : ℝ) ^ (i + j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = (j : ℝ) := by simp
        _ ≤ (r : ℝ) := by
          exact_mod_cast (Nat.le_of_lt (Finset.mem_range.1 hj))
    _ = (r : ℝ) ^ 2 := by simp [pow_two]

theorem integrable_ginibreAlternatingEigenvalueCount (n : ℕ) :
    Integrable (ginibreAlternatingEigenvalueCount n)
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  refine Integrable.of_bound
    (measurable_ginibreAlternatingEigenvalueCount n).aestronglyMeasurable n ?_
  filter_upwards with A
  rw [Real.norm_eq_abs]
  exact (abs_ginibreAlternatingCount_le _).trans (by
    exact_mod_cast realEigenvalueCount_le n A)

theorem integrable_ginibreAlternatingPairEigenvalueCount (n : ℕ) :
    Integrable (ginibreAlternatingPairEigenvalueCount n)
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  refine Integrable.of_bound
    (measurable_ginibreAlternatingPairEigenvalueCount n).aestronglyMeasurable
      ((n : ℝ) ^ 2) ?_
  filter_upwards with A
  rw [Real.norm_eq_abs]
  exact (abs_ginibreAlternatingPairCount_le_sq _).trans (by
    gcongr
    exact_mod_cast realEigenvalueCount_le n A)

/-- Pointwise signed decomposition of the ordinary root count. -/
theorem realEigenvalueCount_cast_eq_alternating_sub_two_pairs
    (n : ℕ) (A : RSqMat n) :
    (realEigenvalueCount n A : ℝ) =
      ginibreAlternatingEigenvalueCount n A -
        2 * ginibreAlternatingPairEigenvalueCount n A := by
  exact natCast_eq_alternating_sub_two_pairs (realEigenvalueCount n A)

/-- Expected-count version of the signed rank/pair decomposition. -/
theorem expectedRealEigenvalueCount_eq_alternating_sub_two_pairs
    (n : ℕ) :
    expectedRealEigenvalueCount n =
      expectedGinibreAlternatingCount n -
        2 * expectedGinibreAlternatingPairCount n := by
  unfold expectedRealEigenvalueCount expectedGinibreAlternatingCount
    expectedGinibreAlternatingPairCount
  rw [show (fun A : RSqMat n => (realEigenvalueCount n A : ℝ)) =
      fun A => ginibreAlternatingEigenvalueCount n A -
        2 * ginibreAlternatingPairEigenvalueCount n A by
    funext A
    exact realEigenvalueCount_cast_eq_alternating_sub_two_pairs n A]
  rw [integral_sub
    (integrable_ginibreAlternatingEigenvalueCount n)
    ((integrable_ginibreAlternatingPairEigenvalueCount n).const_mul 2),
    integral_const_mul]

/-! ## The one-root signed term is deterministic -/

theorem ginibreAlternatingCount_add_two (r : ℕ) :
    ginibreAlternatingCount (r + 2) = ginibreAlternatingCount r := by
  unfold ginibreAlternatingCount
  rw [show r + 2 = (r + 1) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ, pow_succ]
  ring

theorem ginibreAlternatingCount_add_two_mul (r c : ℕ) :
    ginibreAlternatingCount (r + 2 * c) = ginibreAlternatingCount r := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.mul_succ]
      rw [show r + (2 * c + 2) = (r + 2 * c) + 2 by omega,
        ginibreAlternatingCount_add_two, ih]

/-- Because nonreal roots occur in conjugate pairs, the alternating one-root
observable depends only on the matrix dimension. -/
theorem ginibreAlternatingEigenvalueCount_eq_dimension
    (n : ℕ) (A : RSqMat n) :
    ginibreAlternatingEigenvalueCount n A = ginibreAlternatingCount n := by
  have hpair :=
    realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount n A
  unfold ginibreAlternatingEigenvalueCount
  calc
    ginibreAlternatingCount (realEigenvalueCount n A) =
        ginibreAlternatingCount
          (realEigenvalueCount n A +
            2 * complexUpperEigenvalueCount n A) :=
      (ginibreAlternatingCount_add_two_mul
        (realEigenvalueCount n A)
        (complexUpperEigenvalueCount n A)).symm
    _ = ginibreAlternatingCount n := by rw [hpair]

theorem expectedGinibreAlternatingCount_eq_dimension (n : ℕ) :
    expectedGinibreAlternatingCount n = ginibreAlternatingCount n := by
  unfold expectedGinibreAlternatingCount
  rw [show (fun A : RSqMat n => ginibreAlternatingEigenvalueCount n A) =
      fun _A : RSqMat n => ginibreAlternatingCount n by
    funext A
    exact ginibreAlternatingEigenvalueCount_eq_dimension n A]
  rw [integral_const]
  simp only [realGinibreMeasure_univ, measureReal_def, ENNReal.toReal_one,
    one_smul]

theorem expectedGinibreAlternatingCount_add_two (m : ℕ) :
    expectedGinibreAlternatingCount (m + 2) =
      expectedGinibreAlternatingCount m := by
  rw [expectedGinibreAlternatingCount_eq_dimension,
    expectedGinibreAlternatingCount_eq_dimension,
    ginibreAlternatingCount_add_two]

theorem expectedGinibreAlternatingPairCount_one :
    expectedGinibreAlternatingPairCount 1 = 0 := by
  unfold expectedGinibreAlternatingPairCount
    ginibreAlternatingPairEigenvalueCount ginibreAlternatingPairCount
  rw [show (fun A : RSqMat 1 =>
      ∑ j ∈ Finset.range (realEigenvalueCount 1 A),
        ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)) =
      fun _A : RSqMat 1 => 0 by
    funext A
    have h := realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount 1 A
    have hr : realEigenvalueCount 1 A = 1 := by omega
    rw [hr]
    norm_num]
  simp

/-- Consequently, a two-dimensional shift of the genuine expected count is
exactly minus twice the corresponding shift of the signed pair expectation. -/
theorem expectedRealEigenvalueCount_shift_eq_neg_two_mul_pair_shift
    (m : ℕ) :
    expectedRealEigenvalueCount (m + 2) -
        expectedRealEigenvalueCount m =
      -2 * (expectedGinibreAlternatingPairCount (m + 2) -
        expectedGinibreAlternatingPairCount m) := by
  rw [expectedRealEigenvalueCount_eq_alternating_sub_two_pairs,
    expectedRealEigenvalueCount_eq_alternating_sub_two_pairs,
    expectedGinibreAlternatingCount_add_two]
  ring

end

end NumStability
