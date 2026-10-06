-- Algorithms/ContinuedFraction.lean
--
-- Higham Chapter 3, Problem 3.3.

import Mathlib.Tactic

namespace NumStability

/-!
# Continued-Fraction Running Error

Higham Chapter 3, Problem 3.3 asks for a running error analysis of a continued
fraction evaluated by backward recurrence.  The local theorem below isolates
the central step: if the next denominator has already been bounded within
`muNext` and remains separated from zero, then the current step error is the
local rounding residual plus the usual denominator-amplified inherited error.

The final theorem packages this into a reverse-induction certificate for the
whole recurrence.
-/

/-- Exact continued-fraction backward step `a_k + b_k / q_{k+1}`. -/
noncomputable def continuedFractionStep (a b qnext : ℝ) : ℝ :=
  a + b / qnext

/-- Error amplification from perturbing the next denominator. -/
noncomputable def continuedFractionStepAmplification
    (b qhatNext muNext : ℝ) : ℝ :=
  |b| * muNext / (|qhatNext| * (|qhatNext| - muNext))

/-- **Problem 3.3, one backward-recurrence step.**

If `q = a + b/qnext`, the computed local step is within `tau` of
`a + b/qhatNext`, and the next denominator satisfies
`|qhatNext - qnext| <= muNext < |qhatNext|`, then

`|qhat - q| <= tau + |b|*muNext/(|qhatNext|(|qhatNext|-muNext))`.

The strict separation hypothesis is the explicit nonzero-denominator condition
needed for the displayed running-error formula. -/
theorem continuedFraction_step_error_le
    {a b q qhat qnext qhatNext tau muNext : ℝ}
    (hlocal : |qhat - continuedFractionStep a b qhatNext| ≤ tau)
    (hexact : q = continuedFractionStep a b qnext)
    (hnext : |qhatNext - qnext| ≤ muNext)
    (hmu_nonneg : 0 ≤ muNext)
    (hsep : muNext < |qhatNext|) :
    |qhat - q| ≤
      tau + continuedFractionStepAmplification b qhatNext muNext := by
  have hqhat_abs_pos : 0 < |qhatNext| := by
    exact lt_of_le_of_lt hmu_nonneg hsep
  have hgap_pos : 0 < |qhatNext| - muNext := sub_pos.mpr hsep
  have hqhat_ne : qhatNext ≠ 0 := by
    exact abs_pos.mp hqhat_abs_pos
  have hnext_comm : |qnext - qhatNext| ≤ muNext := by
    simpa [abs_sub_comm] using hnext
  have hqnext_abs_lb : |qhatNext| - muNext ≤ |qnext| := by
    have hrev := abs_sub_abs_le_abs_sub qhatNext qnext
    linarith
  have hqnext_abs_pos : 0 < |qnext| := lt_of_lt_of_le hgap_pos hqnext_abs_lb
  have hqnext_ne : qnext ≠ 0 := by
    exact abs_pos.mp hqnext_abs_pos
  have hden_lb :
      |qhatNext| * (|qhatNext| - muNext) ≤ |qhatNext| * |qnext| := by
    exact mul_le_mul_of_nonneg_left hqnext_abs_lb (abs_nonneg qhatNext)
  have hden_pos : 0 < |qhatNext| * (|qhatNext| - muNext) := by
    exact mul_pos hqhat_abs_pos hgap_pos
  have hquot :
      |b / qhatNext - b / qnext| ≤
        continuedFractionStepAmplification b qhatNext muNext := by
    have hdiff :
        b / qhatNext - b / qnext =
          b * (qnext - qhatNext) / (qhatNext * qnext) := by
      field_simp [hqhat_ne, hqnext_ne]
    calc
      |b / qhatNext - b / qnext|
          = |b| * |qnext - qhatNext| / (|qhatNext| * |qnext|) := by
            rw [hdiff, abs_div, abs_mul, abs_mul]
      _ ≤ |b| * muNext / (|qhatNext| * |qnext|) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnext_comm (abs_nonneg b))
              (mul_nonneg (abs_nonneg qhatNext) (abs_nonneg qnext))
      _ ≤ |b| * muNext / (|qhatNext| * (|qhatNext| - muNext)) := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg (abs_nonneg b) hmu_nonneg) hden_pos hden_lb
      _ = continuedFractionStepAmplification b qhatNext muNext := rfl
  have hbridge :
      |continuedFractionStep a b qhatNext - q| ≤
        continuedFractionStepAmplification b qhatNext muNext := by
    calc
      |continuedFractionStep a b qhatNext - q|
          = |b / qhatNext - b / qnext| := by
            rw [hexact]
            simp [continuedFractionStep]
      _ ≤ continuedFractionStepAmplification b qhatNext muNext := hquot
  calc
    |qhat - q|
        = |(qhat - continuedFractionStep a b qhatNext) +
            (continuedFractionStep a b qhatNext - q)| := by
            ring_nf
    _ ≤ |qhat - continuedFractionStep a b qhatNext| +
          |continuedFractionStep a b qhatNext - q| := abs_add_le _ _
    _ ≤ tau + continuedFractionStepAmplification b qhatNext muNext := by
          linarith

/-- **Problem 3.3, end-to-end running-error certificate.**

For a backward recurrence `q_k = a_k + b_k/q_{k+1}`, suppose the terminal
quantity `q_{N+1}` is already bounded by `mu_{N+1}` and every preceding step
has a local residual `tau_k` whose one-step inherited bound is absorbed by
`mu_k`.  Then every computed `qhat_k`, in particular `qhat_0`, is within its
running error budget `mu_k`. -/
theorem continuedFraction_running_error_bound
    (N : ℕ) (a b q qhat tau mu : ℕ → ℝ)
    (hterminal : |qhat (N + 1) - q (N + 1)| ≤ mu (N + 1))
    (hmu_nonneg : ∀ k, 0 ≤ mu k)
    (hexact :
      ∀ k, k ≤ N → q k = continuedFractionStep (a k) (b k) (q (k + 1)))
    (hlocal :
      ∀ k, k ≤ N →
        |qhat k - continuedFractionStep (a k) (b k) (qhat (k + 1))| ≤ tau k)
    (hsep : ∀ k, k ≤ N → mu (k + 1) < |qhat (k + 1)|)
    (hstep :
      ∀ k, k ≤ N →
        tau k +
            continuedFractionStepAmplification (b k) (qhat (k + 1)) (mu (k + 1)) ≤
          mu k) :
    ∀ k, k ≤ N + 1 → |qhat k - q k| ≤ mu k := by
  intro k hk
  refine Nat.decreasingInduction'
    (P := fun j => |qhat j - q j| ≤ mu j)
    (m := k) (n := N + 1) ?step hk hterminal
  intro j hj _hle hj_succ
  have hjN : j ≤ N := Nat.le_of_lt_succ hj
  have hone :=
    continuedFraction_step_error_le
      (a := a j) (b := b j) (q := q j) (qhat := qhat j)
      (qnext := q (j + 1)) (qhatNext := qhat (j + 1))
      (tau := tau j) (muNext := mu (j + 1))
      (hlocal j hjN) (hexact j hjN) hj_succ (hmu_nonneg (j + 1)) (hsep j hjN)
  exact le_trans hone (hstep j hjN)

end NumStability
