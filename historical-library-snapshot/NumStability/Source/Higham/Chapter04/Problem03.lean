import Mathlib.Algebra.Order.Rearrangement
import NumStability.Algorithms.Summation.Recursive.Core

/-!
# Higham, Chapter 4, Problem 4.3

Source correspondence for Problem 4.3 in Nicholas J. Higham, *Accuracy and
Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002). This module
formalizes the variable-`gamma` expansion, its displayed weighted absolute-error
bound, and the conclusion that nondecreasing absolute-value order minimizes
that bound. Reusable recursive-summation definitions and source-independent
error lemmas live in `NumStability.Algorithms.Summation.Recursive.Core`.
-/

namespace NumStability

open scoped BigOperators

/-- Higham Problem 4.3, source-shaped variable-`gamma` expansion for
left-to-right recursive summation.

For `m + 2` inputs, the first exact zero-accumulator step means `x₁` and
`x₂` share the same suffix of `m + 1` rounded additions, while the later
term `x_{j+3}` carries only the remaining `m - j` rounded additions. -/
theorem recursiveSum_problem43_variableGamma (fp : FPModel) (m : ℕ)
    (v : Fin (m + 2) → ℝ) (hvalid : gammaValid fp (m + 1)) :
    ∃ θ12 : ℝ, ∃ θ : Fin m → ℝ,
      |θ12| ≤ gamma fp (m + 1) ∧
      (∀ j : Fin m, |θ j| ≤ gamma fp (m - j.val)) ∧
      fl_recursiveSum fp (m + 2) v =
        (v 0 + v (Fin.succ (0 : Fin (m + 1)))) * (1 + θ12) +
          ∑ j : Fin m, v j.succ.succ * (1 + θ j) := by
  have hpeel :
      fl_recursiveSum fp (m + 2) v =
        Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (v i.succ)) (v 0) := by
    have hfold :
        Fin.foldl ((m + 1) + 1) (fun acc i => fp.fl_add acc (v i)) 0 =
          Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (v i.succ))
            (fp.fl_add 0 (v 0)) :=
      Fin.foldl_succ _ _
    calc
      fl_recursiveSum fp (m + 2) v =
          Fin.foldl ((m + 1) + 1) (fun acc i => fp.fl_add acc (v i)) 0 := by
            simp [fl_recursiveSum, Nat.add_assoc]
      _ = Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (v i.succ))
            (fp.fl_add 0 (v 0)) := hfold
      _ = Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (v i.succ)) (v 0) := by
            rw [fp.fl_add_zero]
  obtain ⟨δ, hδ, hfold⟩ :=
    fl_sum_error_init_suffix_expansion fp (m + 1)
      (fun i : Fin (m + 1) => v i.succ) (v 0)
  have hprod_eq :
      (∏ i : Fin (m + 1), (1 + δ i)) =
        sumSuffixErrorProduct (m + 1) δ (0 : Fin (m + 1)) := by
    rw [sumSuffixErrorProduct_eq_prod_if]
    apply Finset.prod_congr rfl
    intro j _hj
    simp
  have hvalid0 : gammaValid fp ((m + 1) - (0 : Fin (m + 1)).val) := by
    simpa using hvalid
  obtain ⟨θ12, hθ12, hsuffix0⟩ :=
    sumSuffixErrorProduct_exists_theta_le_gamma fp (m + 1) δ hδ
      (0 : Fin (m + 1)) hvalid0
  have hθ12' : |θ12| ≤ gamma fp (m + 1) := by
    simpa using hθ12
  let witness : (j : Fin m) →
      ∃ η : ℝ, |η| ≤ gamma fp (m - j.val) ∧
        sumSuffixErrorProduct (m + 1) δ j.succ = 1 + η := by
    intro j
    have hvalidj : gammaValid fp ((m + 1) - j.succ.val) :=
      gammaValid_mono fp (by omega) hvalid
    obtain ⟨η, hη, hηeq⟩ :=
      sumSuffixErrorProduct_exists_theta_le_gamma fp (m + 1) δ hδ j.succ hvalidj
    refine ⟨η, ?_, hηeq⟩
    have hrem : (m + 1) - j.succ.val = m - j.val := by
      simp
    simpa [hrem] using hη
  let θtail : Fin m → ℝ := fun j => Classical.choose (witness j)
  have hθtail : ∀ j : Fin m, |θtail j| ≤ gamma fp (m - j.val) := by
    intro j
    exact (Classical.choose_spec (witness j)).1
  have hsuffi : ∀ j : Fin m,
      sumSuffixErrorProduct (m + 1) δ j.succ = 1 + θtail j := by
    intro j
    exact (Classical.choose_spec (witness j)).2
  refine ⟨θ12, θtail, hθ12', hθtail, ?_⟩
  rw [hpeel, hfold, Fin.sum_univ_succ, hprod_eq, hsuffix0]
  have htail :
      (∑ j : Fin m, v j.succ.succ * sumSuffixErrorProduct (m + 1) δ j.succ) =
        ∑ j : Fin m, v j.succ.succ * (1 + θtail j) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hsuffi j]
  rw [htail]
  ring

/-- Higham Problem 4.3, the displayed absolute-error consequence of
`recursiveSum_problem43_variableGamma`. -/
theorem recursiveSum_problem43_abs_error_bound (fp : FPModel) (m : ℕ)
    (v : Fin (m + 2) → ℝ) (hvalid : gammaValid fp (m + 1)) :
    |fl_recursiveSum fp (m + 2) v - ∑ i : Fin (m + 2), v i| ≤
      (|v 0| + |v (Fin.succ (0 : Fin (m + 1)))|) * gamma fp (m + 1) +
        ∑ j : Fin m, |v j.succ.succ| * gamma fp (m - j.val) := by
  obtain ⟨θ12, θ, hθ12, hθ, hfl⟩ :=
    recursiveSum_problem43_variableGamma fp m v hvalid
  have hsum_split :
      (∑ i : Fin (m + 2), v i) =
        v 0 + v (Fin.succ (0 : Fin (m + 1))) +
          ∑ j : Fin m, v j.succ.succ := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    ring
  have htail_decomp :
      (∑ j : Fin m, v j.succ.succ * (1 + θ j)) -
          ∑ j : Fin m, v j.succ.succ =
        ∑ j : Fin m, v j.succ.succ * θ j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have herr :
      fl_recursiveSum fp (m + 2) v - ∑ i : Fin (m + 2), v i =
        (v 0 + v (Fin.succ (0 : Fin (m + 1)))) * θ12 +
          ∑ j : Fin m, v j.succ.succ * θ j := by
    rw [hfl, hsum_split]
    calc
      ((v 0 + v (Fin.succ (0 : Fin (m + 1)))) * (1 + θ12) +
          ∑ j : Fin m, v j.succ.succ * (1 + θ j)) -
          (v 0 + v (Fin.succ (0 : Fin (m + 1))) +
            ∑ j : Fin m, v j.succ.succ) =
            (v 0 + v (Fin.succ (0 : Fin (m + 1)))) * θ12 +
              ((∑ j : Fin m, v j.succ.succ * (1 + θ j)) -
                ∑ j : Fin m, v j.succ.succ) := by ring
      _ = (v 0 + v (Fin.succ (0 : Fin (m + 1)))) * θ12 +
          ∑ j : Fin m, v j.succ.succ * θ j := by rw [htail_decomp]
  have hfirst :
      |(v 0 + v (Fin.succ (0 : Fin (m + 1)))) * θ12| ≤
        (|v 0| + |v (Fin.succ (0 : Fin (m + 1)))|) * gamma fp (m + 1) := by
    rw [abs_mul]
    exact mul_le_mul
      (abs_add_le (v 0) (v (Fin.succ (0 : Fin (m + 1))))) hθ12
      (abs_nonneg θ12) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have htail :
      |∑ j : Fin m, v j.succ.succ * θ j| ≤
        ∑ j : Fin m, |v j.succ.succ| * gamma fp (m - j.val) := by
    calc
      |∑ j : Fin m, v j.succ.succ * θ j|
          ≤ ∑ j : Fin m, |v j.succ.succ * θ j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin m, |v j.succ.succ| * |θ j| := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [abs_mul]
      _ ≤ ∑ j : Fin m, |v j.succ.succ| * gamma fp (m - j.val) := by
            apply Finset.sum_le_sum
            intro j _hj
            exact mul_le_mul_of_nonneg_left (hθ j) (abs_nonneg _)
  rw [herr]
  exact le_trans (abs_add_le _ _)
    (add_le_add hfirst htail)

/-- Problem 4.3's suffix weights are nonincreasing as the source position
moves from left to right. -/
theorem recursiveSum_problem43_tail_gamma_weight_mono (fp : FPModel) {m : ℕ}
    (hvalid : gammaValid fp (m + 1)) {i j : Fin m} (hij : i.val ≤ j.val) :
    gamma fp (m - j.val) ≤ gamma fp (m - i.val) := by
  have hle : m - j.val ≤ m - i.val := by omega
  have hvalid_i : gammaValid fp (m - i.val) :=
    gammaValid_mono fp (by omega) hvalid
  exact gamma_mono fp hle hvalid_i

/-- Problem 4.3's leading `(x₁+x₂)` coefficient uses the largest `gamma`
weight in the displayed bound. -/
theorem recursiveSum_problem43_leading_gamma_weight_ge_tail (fp : FPModel)
    {m : ℕ} (hvalid : gammaValid fp (m + 1)) (j : Fin m) :
    gamma fp (m - j.val) ≤ gamma fp (m + 1) := by
  exact gamma_mono fp (by omega) hvalid

/-- Problem 4.3 ordering certificate: for any two suffix positions with
position `i` no later than `j`, putting the smaller absolute value at `i`
and the larger absolute value at `j` cannot increase the displayed weighted
bound.  Thus repeated adjacent exchanges drive the source bound toward
nondecreasing absolute-value order. -/
theorem recursiveSum_problem43_tail_pair_exchange_le (fp : FPModel) {m : ℕ}
    (hvalid : gammaValid fp (m + 1)) {i j : Fin m} (hij : i.val ≤ j.val)
    {a b : ℝ} (hab : |a| ≤ |b|) :
    |a| * gamma fp (m - i.val) + |b| * gamma fp (m - j.val) ≤
      |b| * gamma fp (m - i.val) + |a| * gamma fp (m - j.val) := by
  have hweights :=
    recursiveSum_problem43_tail_gamma_weight_mono fp hvalid hij
  have h :=
    weighted_abs_pair_exchange_le (wa := gamma fp (m - i.val))
      (wb := gamma fp (m - j.val)) hweights hab
  simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h

/-- The position weight in Problem 4.3's displayed recursive-summation bound
for a vector of length `m + 2`.  The first two positions share
`gamma (m+1)`; position `k >= 2` has suffix weight `gamma (m+2-k)`. -/
noncomputable def recursiveSumProblem43GammaWeight (fp : FPModel) (m : ℕ)
    (i : Fin (m + 2)) : ℝ :=
  if i.val < 2 then gamma fp (m + 1) else gamma fp (m + 2 - i.val)

/-- The displayed weighted absolute-value bound from Problem 4.3, written as
a single indexed sum. -/
noncomputable def recursiveSumProblem43WeightedAbsBound (fp : FPModel) (m : ℕ)
    (v : Fin (m + 2) → ℝ) : ℝ :=
  ∑ i : Fin (m + 2), |v i| * recursiveSumProblem43GammaWeight fp m i

/-- The indexed weighted-bound definition is exactly Problem 4.3's displayed
right-hand side. -/
theorem recursiveSumProblem43WeightedAbsBound_eq_display (fp : FPModel)
    (m : ℕ) (v : Fin (m + 2) → ℝ) :
    recursiveSumProblem43WeightedAbsBound fp m v =
      (|v 0| + |v (Fin.succ (0 : Fin (m + 1)))|) * gamma fp (m + 1) +
        ∑ j : Fin m, |v j.succ.succ| * gamma fp (m - j.val) := by
  rw [recursiveSumProblem43WeightedAbsBound]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have htail :
      (∑ j : Fin m,
          |v j.succ.succ| *
            recursiveSumProblem43GammaWeight fp m j.succ.succ) =
        ∑ j : Fin m, |v j.succ.succ| * gamma fp (m - j.val) := by
    apply Finset.sum_congr rfl
    intro j _hj
    simp [recursiveSumProblem43GammaWeight]
  rw [htail]
  simp [recursiveSumProblem43GammaWeight]
  ring

/-- Problem 4.3's absolute-error bound in the single indexed-weight notation. -/
theorem recursiveSum_problem43_abs_error_bound_weighted (fp : FPModel) (m : ℕ)
    (v : Fin (m + 2) → ℝ) (hvalid : gammaValid fp (m + 1)) :
    |fl_recursiveSum fp (m + 2) v - ∑ i : Fin (m + 2), v i| ≤
      recursiveSumProblem43WeightedAbsBound fp m v := by
  rw [recursiveSumProblem43WeightedAbsBound_eq_display]
  exact recursiveSum_problem43_abs_error_bound fp m v hvalid

/-- The indexed `gamma` weights in Problem 4.3 are nonincreasing with the
source position. -/
theorem recursiveSum_problem43_gamma_weight_mono (fp : FPModel) {m : ℕ}
    (hvalid : gammaValid fp (m + 1)) {i j : Fin (m + 2)}
    (hij : i.val ≤ j.val) :
    recursiveSumProblem43GammaWeight fp m j ≤
      recursiveSumProblem43GammaWeight fp m i := by
  by_cases hj : j.val < 2
  · have hi : i.val < 2 := by omega
    simp [recursiveSumProblem43GammaWeight, hi, hj]
  · by_cases hi : i.val < 2
    · simp [recursiveSumProblem43GammaWeight, hi, hj]
      exact gamma_mono fp (by omega) hvalid
    · simp [recursiveSumProblem43GammaWeight, hi, hj]
      have hle : m + 2 - j.val ≤ m + 2 - i.val := by omega
      have hvalid_i : gammaValid fp (m + 2 - i.val) :=
        gammaValid_mono fp (by omega) hvalid
      exact gamma_mono fp hle hvalid_i

/-- If the input vector is already ordered by nondecreasing absolute value,
then its magnitudes antivary with the Problem 4.3 decreasing `gamma` weights. -/
theorem recursiveSum_problem43_antivary_abs_gammaWeight_of_increasingAbs
    (fp : FPModel) {m : ℕ} (hvalid : gammaValid fp (m + 1))
    (v : Fin (m + 2) → ℝ)
    (hinc : ∀ i j : Fin (m + 2), i.val ≤ j.val → |v i| ≤ |v j|) :
    Antivary (fun i : Fin (m + 2) => |v i|)
      (recursiveSumProblem43GammaWeight fp m) := by
  intro i j hlt
  have hji : j.val ≤ i.val := by
    by_contra hnot
    have hij : i.val ≤ j.val := le_of_not_ge hnot
    have hw := recursiveSum_problem43_gamma_weight_mono fp hvalid hij
    linarith
  exact hinc j i hji

/-- Problem 4.3's ordering answer, in global permutation form: once the data
are arranged by nondecreasing absolute value, every finite reordering has a
weighted bound at least as large. -/
theorem recursiveSum_problem43_increasingAbs_weightedBound_le_perm
    (fp : FPModel) {m : ℕ} (hvalid : gammaValid fp (m + 1))
    (v : Fin (m + 2) → ℝ)
    (hinc : ∀ i j : Fin (m + 2), i.val ≤ j.val → |v i| ≤ |v j|)
    (σ : Fin (m + 2) ≃ Fin (m + 2)) :
    recursiveSumProblem43WeightedAbsBound fp m v ≤
      recursiveSumProblem43WeightedAbsBound fp m (fun i => v (σ i)) := by
  have hanti :=
    recursiveSum_problem43_antivary_abs_gammaWeight_of_increasingAbs fp
      hvalid v hinc
  simpa [recursiveSumProblem43WeightedAbsBound] using
    (Antivary.sum_mul_le_sum_comp_perm_mul
      (σ := σ) hanti)

end NumStability
