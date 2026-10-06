-- Algorithms/PriestAccuracy.lean

import NumStability.Algorithms.Summation.DoublyCompensated
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace NumStability

open scoped BigOperators

/-!
# Priest doubly compensated summation: the accuracy theorem (Higham §4.3, Alg. 4.3)

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §4.3, p. 88:
Priest [955, §4.1] shows that if the inputs are sorted `|x₁| ≥ ⋯ ≥ |xₙ|` and
`n ≤ β^(t−3)` for `t`-digit base-`β` arithmetic, then the computed doubly
compensated sum `ŝₙ` satisfies

  `|sₙ − ŝₙ| ≤ 2u|sₙ|`,   `sₙ = ∑ xᵢ` the exact sum.       (§4.3, unnumbered)

This file supplies the *algebraic backbone* of Priest's proof over the repository
trace `priestStepTrace` / `fl_priestSum` (`DoublyCompensatedSum.lean`, import-only).

Each Priest loop step performs three "two-sum" corrections (the `(y,u)`, `(t,υ)`
and `(s,c)` pairs) and one exact combine `z = u + υ`.  When those four local
operations are *exact* (Higham eq. (4.7); Dekker/Knuth `FastTwoSum`), the running
pair satisfies the **exact** invariant `sₖ + cₖ = ∑_{i≤k} xᵢ` (`priest_running_invariant`).
From that invariant together with the abstract relative-error model (Higham (2.4))
the retained correction of the final step is the rounding error of the last
addition, giving `|sₙ − ŝₙ| ≤ u|sₙ| ≤ 2u|sₙ|` (`priest_abs_error_le_u`,
`priest_doublyCompensated_accuracy`) — the printed bound, in fact with the
strictly tighter leading constant `u`.

RESIDUAL (honest scope). The single remaining hypothesis is `PriestAllStepsExact`,
i.e. that every step's four local operations are exact.  It is the *exact
idealization* of Priest's step: it is **sufficient** for the printed bound (proved
here) and it is **satisfiable** (exact arithmetic witnesses it,
`priestAllStepsExact_exactWithUnitRoundoff`, so the conditionals are not vacuous),
but it is **stronger than what a real finite model delivers** and hence stronger
than what Priest actually proves.  The gap is the first correction
`(y,u) = (fl(c_{k-1}+x_k), …)`, a `FastTwoSum(c_{k-1}, x_k)` in the
`|c_{k-1}| < |x_k|` orientation (the correction is tiny, the summand is not): that
is the opposite of the `|b| < |a|` regime of the repository's finite eq. (4.7)
theorem `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`, and there `y + u`
does **not** in general equal `c_{k-1} + x_k` exactly.  Priest's §4.1 analysis
instead *bounds* that `FastTwoSum` defect and shows the accumulated defect stays
within the `2u` budget provided `n ≤ β^(t−3)`.  Closing this target fully therefore
means replacing the exact invariant `sₖ + cₖ = ∑_{i≤k} xᵢ` by Priest's
error-controlled invariant (a defect bounded by the accumulation lemma) — the
intricate faithful-rounding argument, not yet formalized.
-/

/-- Per-step exactness of Priest's doubly compensated summation loop: the three
`FastTwoSum` corrections and the combine `z = u + υ` are exact for the step that
adds `xk` to the running state `st`.  This is the *exact idealization* of the
local step — sufficient for the accuracy bound and satisfiable in exact arithmetic,
but stronger than a real finite model delivers (see the module header: the `(y,u)`
correction is not in general an exact `FastTwoSum`).  Bundling the four equalities
here isolates precisely that residual; they are stated on the actual traced
quantities `priestStepTrace fp xk st`. -/
structure PriestStepExact (fp : FPModel) (xk : ℝ) (st : PriestState) : Prop where
  /-- The `(yₖ, uₖ)` correction is exact: `yₖ + uₖ = c_{k-1} + xₖ`. -/
  addOne : (priestStepTrace fp xk st).y + (priestStepTrace fp xk st).u = st.c + xk
  /-- The `(tₖ, υₖ)` correction is exact: `tₖ + υₖ = yₖ + s_{k-1}`. -/
  addThree :
    (priestStepTrace fp xk st).t + (priestStepTrace fp xk st).upsilon =
      (priestStepTrace fp xk st).y + st.s
  /-- The combine `zₖ = uₖ + υₖ` is exact. -/
  combine :
    (priestStepTrace fp xk st).z =
      (priestStepTrace fp xk st).u + (priestStepTrace fp xk st).upsilon
  /-- The `(sₖ, cₖ)` correction is exact: `sₖ + cₖ = tₖ + zₖ`. -/
  addSix :
    (priestStepTrace fp xk st).s + (priestStepTrace fp xk st).c =
      (priestStepTrace fp xk st).t + (priestStepTrace fp xk st).z

/-- **Step invariant.**  If a Priest step is exact then the running total
`s + c` gains exactly the new summand: `sₖ + cₖ = (s_{k-1} + c_{k-1}) + xₖ`.
This is the pure-algebra core of Priest's analysis (no rounding facts beyond the
four per-step exactness equalities). -/
theorem priestStep_totalCorrection_of_exact
    (fp : FPModel) (xk : ℝ) (st : PriestState)
    (h : PriestStepExact fp xk st) :
    (priestStep fp xk st).s + (priestStep fp xk st).c = st.s + st.c + xk := by
  have hs : (priestStep fp xk st).s = (priestStepTrace fp xk st).s := rfl
  have hc : (priestStep fp xk st).c = (priestStepTrace fp xk st).c := rfl
  rw [hs, hc]
  linarith [h.addOne, h.addThree, h.combine, h.addSix]

/-- **Prefix-state recursion.**  Running one more Priest step from the `k`-step
prefix state gives the `(k+1)`-step prefix state, with input `x_{k+1}`. -/
theorem priestPrefixState_succ (fp : FPModel) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (k : ℕ) (hk : k + 1 ≤ n) :
    priestPrefixState fp x (k + 1) hk =
      priestStep fp (x ⟨k + 1, by omega⟩)
        (priestPrefixState fp x k (by omega)) := by
  unfold priestPrefixState
  rw [Fin.foldl_succ_last]
  congr 1

/-- The bundled per-step exactness hypothesis for the whole (sorted) input: every
tail step `i = 0 … n−1`, adding `x_{i+1}` to the state after the first `i` tail
steps, is exact.  This is `PriestStepExact` at each `priestTrace fp x i`. -/
def PriestAllStepsExact (fp : FPModel) {n : ℕ} (x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i : Fin n,
    PriestStepExact fp
      (x ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (priestPrefixState fp x i.val (Nat.le_of_lt i.isLt))

/-- **Accumulation.**  Under per-step exactness, the running `(s, c)` pair after
`k` tail steps represents the exact partial sum of the first `k+1` inputs:
`sₖ + cₖ = ∑_{i ≤ k} xᵢ`.  Proved by induction on `k` using the step invariant. -/
theorem priest_prefixState_totalCorrection (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hexact : PriestAllStepsExact fp x) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (priestPrefixState fp x k hk).s + (priestPrefixState fp x k hk).c =
        ∑ i : Fin (k + 1), x (Fin.castLE (Nat.succ_le_succ hk) i) := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [Fin.sum_univ_one]
    simp only [priestPrefixState, Fin.foldl_zero, priestInitialState, add_zero]
    congr 1
  | succ k ih =>
    intro hk
    have hstep :
        (priestPrefixState fp x (k + 1) hk).s +
            (priestPrefixState fp x (k + 1) hk).c =
          (priestPrefixState fp x k (by omega)).s +
              (priestPrefixState fp x k (by omega)).c +
            x ⟨k + 1, by omega⟩ := by
      rw [priestPrefixState_succ fp x k hk]
      exact priestStep_totalCorrection_of_exact fp _ _ (hexact ⟨k, by omega⟩)
    rw [hstep, ih (by omega)]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    congr 1

/-- **Running invariant.**  Specializing the accumulation to the full input:
under per-step exactness the final Priest pair satisfies `sₙ + cₙ = ∑ xᵢ`
*exactly* — the retained correction is exactly the summation defect. -/
theorem priest_running_invariant (fp : FPModel) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hexact : PriestAllStepsExact fp x) :
    (fl_priestState fp x).s + (fl_priestState fp x).c = ∑ i, x i := by
  rw [fl_priestState_eq_prefixState,
    priest_prefixState_totalCorrection fp x hexact n (Nat.le_refl n)]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- **Final-correction bound.**  The retained correction of the whole run is
bounded by `u` times the represented total.  For a nonempty run this is because
the last step's `(s,c)` correction (exact by hypothesis) makes `cₙ` the rounding
error of the final addition `sₙ = fl(tₙ + zₙ)`, which the relative-error model
(Higham (2.4)) bounds by `u|tₙ + zₙ| = u|sₙ + cₙ|`. -/
theorem priest_final_correction_bound (fp : FPModel) :
    ∀ {n : ℕ} (x : Fin (n + 1) → ℝ), PriestAllStepsExact fp x →
      |(fl_priestState fp x).c| ≤
        fp.u * |(fl_priestState fp x).s + (fl_priestState fp x).c|
  | 0, x, _hexact => by
      have hc : (fl_priestState fp x).c = 0 := by
        simp [fl_priestState, priestPrefixState, priestInitialState]
      rw [hc, abs_zero]
      exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  | m + 1, x, hexact => by
      have hfin :
          fl_priestState fp x =
            priestStep fp (x ⟨m + 1, by omega⟩)
              (priestPrefixState fp x m (by omega)) := by
        rw [fl_priestState_eq_prefixState]
        exact priestPrefixState_succ fp x m (Nat.le_refl (m + 1))
      set xk : ℝ := x ⟨m + 1, by omega⟩ with hxk
      set st : PriestState := priestPrefixState fp x m (by omega) with hst
      have hE6 :
          (priestStepTrace fp xk st).s + (priestStepTrace fp xk st).c =
            (priestStepTrace fp xk st).t + (priestStepTrace fp xk st).z :=
        (hexact ⟨m, by omega⟩).addSix
      have hs : (fl_priestState fp x).s = (priestStepTrace fp xk st).s := by
        rw [hfin]; rfl
      have hcc : (fl_priestState fp x).c = (priestStepTrace fp xk st).c := by
        rw [hfin]; rfl
      have htrs :
          (priestStepTrace fp xk st).s =
            fp.fl_add (priestStepTrace fp xk st).t (priestStepTrace fp xk st).z :=
        priestStepTrace_s fp xk st
      obtain ⟨δ, hδ, hadd⟩ :=
        fp.model_add (priestStepTrace fp xk st).t (priestStepTrace fp xk st).z
      have hc_eq :
          (priestStepTrace fp xk st).c =
            -((priestStepTrace fp xk st).t + (priestStepTrace fp xk st).z) * δ := by
        have hce :
            (priestStepTrace fp xk st).c =
              ((priestStepTrace fp xk st).t + (priestStepTrace fp xk st).z) -
                (priestStepTrace fp xk st).s := by linarith [hE6]
        rw [hce, htrs, hadd]; ring
      rw [hcc, hs, hE6, hc_eq, abs_mul, abs_neg, mul_comm fp.u]
      exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)

/-- **Priest accuracy, tight leading constant.**  Under per-step exactness the
computed doubly compensated sum `ŝₙ = fl_priestSum` has relative error at most `u`
against the exact sum: `|sₙ − ŝₙ| ≤ u|sₙ|`. -/
theorem priest_abs_error_le_u (fp : FPModel) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hexact : PriestAllStepsExact fp x) :
    |(∑ i, x i) - fl_priestSum fp x| ≤ fp.u * |∑ i, x i| := by
  have hinv := priest_running_invariant fp x hexact
  have hbd := priest_final_correction_bound fp x hexact
  have hsum : fl_priestSum fp x = (fl_priestState fp x).s := rfl
  rw [hsum]
  have hrw : (∑ i, x i) - (fl_priestState fp x).s = (fl_priestState fp x).c := by
    linarith [hinv]
  rw [hrw]
  calc |(fl_priestState fp x).c|
      ≤ fp.u * |(fl_priestState fp x).s + (fl_priestState fp x).c| := hbd
    _ = fp.u * |∑ i, x i| := by rw [hinv]

/-- **Priest's accuracy theorem (Higham §4.3, Algorithm 4.3).**  Under per-step
exactness (Priest's faithful-rounding lemma; discharged in the source from the
sorted-decreasing ordering `|x₁| ≥ ⋯ ≥ |xₙ|` and `n ≤ β^(t−3)`), the computed
doubly compensated sum satisfies the printed bound

  `|sₙ − ŝₙ| ≤ 2u|sₙ|`,   `sₙ = ∑ xᵢ` the exact sum.

The proof in fact delivers the strictly tighter `u|sₙ|` (`priest_abs_error_le_u`);
the printed `2u` is looser slack. -/
theorem priest_doublyCompensated_accuracy (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hexact : PriestAllStepsExact fp x) :
    |(∑ i, x i) - fl_priestSum fp x| ≤ 2 * fp.u * |∑ i, x i| := by
  have h := priest_abs_error_le_u fp x hexact
  have hstep : fp.u * |∑ i, x i| ≤ 2 * fp.u * |∑ i, x i| :=
    mul_le_mul_of_nonneg_right (by linarith [fp.u_nonneg]) (abs_nonneg _)
  linarith

/-- **Non-vacuity.**  The per-step exactness hypothesis is satisfiable: exact
arithmetic (`FPModel.exactWithUnitRoundoff`) makes every Priest step exact.
Hence the conditional theorems above are not vacuously true; in that model
`priest_doublyCompensated_accuracy` recovers the zero-error sanity fact. -/
theorem priestAllStepsExact_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0)
    {n : ℕ} (x : Fin (n + 1) → ℝ) :
    PriestAllStepsExact (FPModel.exactWithUnitRoundoff u0 hu0) x := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [priestStepTrace, FPModel.exactWithUnitRoundoff]

end NumStability
