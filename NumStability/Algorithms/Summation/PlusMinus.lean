-- Algorithms/Summation/PlusMinus.lean
--
-- Higham Chapter 4, Problem 4.5.

import Mathlib.Tactic
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Analysis.Summation.Signs

namespace NumStability

open scoped BigOperators

/-!
# The Plus/Minus Summation Method

Reusable APIs for splitting inputs into positive and nonpositive parts,
summing each one-signed part recursively, and bounding their final rounded
recombination. The file proves exact preservation of the real sum, unit
condition number for each nonzero one-signed partial sum, and forward- and
relative-error bounds that expose cancellation in the final addition.

This method is the subject of Higham, Chapter 4, Problem 4.5. That provenance
motivates the API, while the definitions and theorems are source-independent.
-/

/-- Positive part of a scalar for the plus/minus method. -/
noncomputable def positivePart (x : ℝ) : ℝ :=
  if 0 < x then x else 0

/-- Nonpositive part of a scalar for the plus/minus method. -/
noncomputable def nonpositivePart (x : ℝ) : ℝ :=
  if 0 < x then 0 else x

/-- Positive parts are nonnegative. -/
theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  by_cases hx : 0 < x
  · simp [positivePart, hx, le_of_lt hx]
  · simp [positivePart, hx]

/-- Nonpositive parts are nonpositive. -/
theorem nonpositivePart_nonpos (x : ℝ) : nonpositivePart x ≤ 0 := by
  by_cases hx : 0 < x
  · simp [nonpositivePart, hx]
  · simp [nonpositivePart, hx, le_of_not_gt hx]

/-- The positive and nonpositive parts add back to the original scalar. -/
theorem positivePart_add_nonpositivePart (x : ℝ) :
    positivePart x + nonpositivePart x = x := by
  by_cases hx : 0 < x
  · simp [positivePart, nonpositivePart, hx]
  · simp [positivePart, nonpositivePart, hx]

/-- Positive split vector. -/
noncomputable def plusMinusPositive {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => positivePart (v i)

/-- Nonpositive split vector. -/
noncomputable def plusMinusNonpositive {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => nonpositivePart (v i)

/-- Exact positive partial sum for the plus/minus method. -/
noncomputable def plusMinusExactPositive (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, plusMinusPositive v i

/-- Exact nonpositive partial sum for the plus/minus method. -/
noncomputable def plusMinusExactNonpositive (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, plusMinusNonpositive v i

/-- The exact split preserves the original sum. -/
theorem plusMinusExactNonpositive_add_positive (n : ℕ) (v : Fin n → ℝ) :
    plusMinusExactNonpositive n v + plusMinusExactPositive n v =
      ∑ i : Fin n, v i := by
  rw [plusMinusExactNonpositive, plusMinusExactPositive,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [plusMinusPositive, plusMinusNonpositive, add_comm,
    positivePart_add_nonpositivePart]

/-- The positive split is one-signed. -/
theorem plusMinusPositive_oneSigned {n : ℕ} (v : Fin n → ℝ) :
    OneSigned (plusMinusPositive v) :=
  Or.inl fun i => positivePart_nonneg (v i)

/-- The nonpositive split is one-signed. -/
theorem plusMinusNonpositive_oneSigned {n : ℕ} (v : Fin n → ℝ) :
    OneSigned (plusMinusNonpositive v) :=
  Or.inr fun i => nonpositivePart_nonpos (v i)

/-- Advantage of the positive side: its summation condition number is one
whenever its exact partial sum is nonzero. -/
theorem plusMinusPositive_conditionNumber_eq_one {n : ℕ} (v : Fin n → ℝ)
    (hsum : plusMinusExactPositive n v ≠ 0) :
    summationConditionNumber (plusMinusPositive v) = 1 := by
  simpa [plusMinusExactPositive] using
    summationConditionNumber_eq_one_of_oneSigned
      (plusMinusPositive v) (plusMinusPositive_oneSigned v) hsum

/-- Advantage of the nonpositive side: its summation condition number is one
whenever its exact partial sum is nonzero. -/
theorem plusMinusNonpositive_conditionNumber_eq_one {n : ℕ} (v : Fin n → ℝ)
    (hsum : plusMinusExactNonpositive n v ≠ 0) :
    summationConditionNumber (plusMinusNonpositive v) = 1 := by
  simpa [plusMinusExactNonpositive] using
    summationConditionNumber_eq_one_of_oneSigned
      (plusMinusNonpositive v) (plusMinusNonpositive_oneSigned v) hsum

/-- Abstract final-add error bound for the plus/minus method.  The hypotheses
allow the two separated sums to be produced by any method. -/
theorem plusMinus_final_add_error_bound (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (sNonposHat sPosHat epsNonpos epsPos : ℝ)
    (hNonpos :
      |sNonposHat - plusMinusExactNonpositive n v| ≤ epsNonpos)
    (hPos : |sPosHat - plusMinusExactPositive n v| ≤ epsPos) :
    |fp.fl_add sNonposHat sPosHat - ∑ i : Fin n, v i| ≤
      epsNonpos + epsPos + fp.u * (|sNonposHat| + |sPosHat|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add sNonposHat sPosHat
  have hsplit := plusMinusExactNonpositive_add_positive n v
  have hround :
      |(sNonposHat + sPosHat) * δ| ≤
        fp.u * (|sNonposHat| + |sPosHat|) := by
    calc
      |(sNonposHat + sPosHat) * δ|
          = |sNonposHat + sPosHat| * |δ| := by rw [abs_mul]
      _ ≤ (|sNonposHat| + |sPosHat|) * fp.u := by
          exact mul_le_mul (abs_add_le _ _) hδ (abs_nonneg _) (by positivity)
      _ = fp.u * (|sNonposHat| + |sPosHat|) := by ring
  calc
    |fp.fl_add sNonposHat sPosHat - ∑ i : Fin n, v i|
        = |(sNonposHat - plusMinusExactNonpositive n v) +
            (sPosHat - plusMinusExactPositive n v) +
            (sNonposHat + sPosHat) * δ| := by
            rw [hfl, ← hsplit]
            ring_nf
    _ ≤ |sNonposHat - plusMinusExactNonpositive n v| +
          |sPosHat - plusMinusExactPositive n v| +
          |(sNonposHat + sPosHat) * δ| := by
          calc
            |(sNonposHat - plusMinusExactNonpositive n v) +
                (sPosHat - plusMinusExactPositive n v) +
                (sNonposHat + sPosHat) * δ|
                ≤ |(sNonposHat - plusMinusExactNonpositive n v) +
                    (sPosHat - plusMinusExactPositive n v)| +
                    |(sNonposHat + sPosHat) * δ| := abs_add_le _ _
            _ ≤ |sNonposHat - plusMinusExactNonpositive n v| +
                  |sPosHat - plusMinusExactPositive n v| +
                  |(sNonposHat + sPosHat) * δ| := by
                  linarith [abs_add_le
                    (sNonposHat - plusMinusExactNonpositive n v)
                    (sPosHat - plusMinusExactPositive n v)]
    _ ≤ epsNonpos + epsPos + fp.u * (|sNonposHat| + |sPosHat|) := by
        linarith

/-- Concrete recursive implementation of the plus/minus method. -/
noncomputable def fl_plusMinusRecursiveSum (fp : FPModel)
    (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  fp.fl_add
    (fl_recursiveSum fp n (plusMinusNonpositive v))
    (fl_recursiveSum fp n (plusMinusPositive v))

/-- Absolute-error bound for recursive plus/minus summation.  The first term is the
cost of the two one-signed recursive sums; the second term is the final
rounded-add cost and is the visible cancellation-sensitive part. -/
theorem fl_plusMinusRecursiveSum_error_bound (fp : FPModel)
    (n : ℕ) (v : Fin n → ℝ) (hn : gammaValid fp (n - 1)) :
    |fl_plusMinusRecursiveSum fp n v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) *
          ((∑ i : Fin n, |plusMinusNonpositive v i|) +
            ∑ i : Fin n, |plusMinusPositive v i|) +
        fp.u *
          (|fl_recursiveSum fp n (plusMinusNonpositive v)| +
            |fl_recursiveSum fp n (plusMinusPositive v)|) := by
  have hNonpos :=
    recursiveSum_forward_error_bound fp n (plusMinusNonpositive v) hn
  have hPos :=
    recursiveSum_forward_error_bound fp n (plusMinusPositive v) hn
  have hfinal :=
    plusMinus_final_add_error_bound fp n v
      (fl_recursiveSum fp n (plusMinusNonpositive v))
      (fl_recursiveSum fp n (plusMinusPositive v))
      (gamma fp (n - 1) * ∑ i : Fin n, |plusMinusNonpositive v i|)
      (gamma fp (n - 1) * ∑ i : Fin n, |plusMinusPositive v i|)
      (by simpa [plusMinusExactNonpositive] using hNonpos)
      (by simpa [plusMinusExactPositive] using hPos)
  simpa [fl_plusMinusRecursiveSum, mul_add, add_comm, add_left_comm,
    add_assoc] using hfinal

/-- Relative-error consequence for recursive plus/minus summation.  This is the
formal disadvantage: even when the separated sums are well conditioned, the
final relative error is divided by the magnitude of the total sum. -/
theorem fl_plusMinusRecursiveSum_relError_bound (fp : FPModel)
    (n : ℕ) (v : Fin n → ℝ) (hn : gammaValid fp (n - 1))
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_plusMinusRecursiveSum fp n v) (∑ i : Fin n, v i) ≤
      (gamma fp (n - 1) *
          ((∑ i : Fin n, |plusMinusNonpositive v i|) +
            ∑ i : Fin n, |plusMinusPositive v i|) +
        fp.u *
          (|fl_recursiveSum fp n (plusMinusNonpositive v)| +
            |fl_recursiveSum fp n (plusMinusPositive v)|)) /
        |∑ i : Fin n, v i| := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := fl_plusMinusRecursiveSum_error_bound fp n v hn
  unfold relError
  exact div_le_div_of_nonneg_right hbound (le_of_lt hden)

end NumStability
