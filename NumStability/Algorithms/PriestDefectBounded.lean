-- Algorithms/PriestDefectBounded.lean

import NumStability.Algorithms.PriestAccuracy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination

namespace NumStability

open scoped BigOperators

/-!
# Priest doubly compensated summation: the *defect-bounded* invariant (Higham §4.3)

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §4.3,
Algorithm 4.3, p. 88: for sorted inputs `|x₁| ≥ ⋯ ≥ |xₙ|` and `n ≤ β^(t−3)`,
the computed doubly compensated sum `ŝₙ` satisfies `|sₙ − ŝₙ| ≤ 2u|sₙ|`.

`PriestAccuracy.lean` reduced this to `PriestAllStepsExact` — every step's four
local `FastTwoSum`/combine operations *exact*.  As its header records, that is
**stronger than a finite model delivers**: the first correction
`(yₖ,uₖ) = FastTwoSum(c_{k-1}, xₖ)` runs in the `|c_{k-1}| < |xₖ|` orientation
(tiny addend, large summand), the *opposite* of the repository exactness lemma
`finiteCorrectionFormulaTrace_exact_of_base2_abs_gt` (which needs `|b| < |a|`),
and there `yₖ + uₖ ≠ c_{k-1} + xₖ` in general.

This file **replaces the exact idealization with Priest's defect-bounded
invariant**, assuming *no* exactness anywhere:

* `priestDB_twoSum_defect_bound` — the master `FastTwoSum` defect bound valid in
  **either** orientation, purely from the relative-error model (Higham (2.4)):
  for the retained pair `(sr, e)` with `w = fl(sr − a)`, `e = fl(b − w)`,
  `|(sr + e) − (a + b)| ≤ u|sr − a| + u|b − w|`.  Neither `δ` of the two
  subtractions is assumed zero — this is the honest wrong-orientation defect.
* `priestDB_ft1_defect_wrongOrientation` — the crux `(yₖ,uₖ)` correction in the
  `|c| ≤ |x|` (wrong) orientation has defect `≤ (u + 5u² + 2u³)|x|`, i.e. of
  order `u|x|`, derived (not assumed).
* `priestDB_stepDefect` / `priestDB_stepDefect_eq_sum` / `priestDB_stepDefect_bound`
  — the total per-step defect equals the sum of the four local defects and is
  bounded by `u` times the local operand magnitudes.
* `priestDB_running_invariant` — the exact accumulation *with defect*:
  `sₙ + cₙ = Σ xᵢ + Σⱼ Eⱼ` where `Eⱼ` is the per-step defect (generalizing
  `priest_running_invariant`, which forced `Σ Eⱼ = 0`).
* `priestDB_doublyCompensated_accuracy` — the printed `2u|sₙ|` bound, under the
  single residual `priestDB_defectBudget`.

RESIDUAL (honest scope). The one remaining hypothesis is `priestDB_defectBudget`:
`|cₙ| + Σⱼ |Eⱼ| ≤ 2u|Σ xᵢ|`, i.e. *the retained correction plus the accumulated
per-step defect stays within the 2u budget*.  This is **strictly weaker** than
`PriestAllStepsExact` — the latter forces every `Eⱼ = 0` and (with the imported
final-correction bound) implies `priestDB_defectBudget`
(`priestDB_defectBudget_of_allStepsExact`) — and it is exactly the accumulation
Priest's thesis (§4.1) controls from the sorted ordering and `n ≤ β^(t−3)`.
`priestDB_stepDefect_bound` reduces it to a concrete finite sum of `u·(magnitude)`
terms; discharging that sum under the sorted hypothesis is the faithful-rounding
argument not yet formalized.
-/

/-! ## The master `FastTwoSum` defect bound (either orientation) -/

/-- **Plain rounded-add defect.**  From the relative-error model,
`|fl(a + b) − (a + b)| ≤ u |a + b|`. -/
theorem priestDB_add_defect_bound (fp : FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  have hrw : fp.fl_add a b - (a + b) = (a + b) * δ := by rw [hadd]; ring
  rw [hrw, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

/-- **Plain rounded-sub defect.**  From the relative-error model,
`|fl(a − b) − (a − b)| ≤ u |a − b|`. -/
theorem priestDB_sub_defect_bound (fp : FPModel) (a b : ℝ) :
    |fp.fl_sub a b - (a - b)| ≤ fp.u * |a - b| := by
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub a b
  have hrw : fp.fl_sub a b - (a - b) = (a - b) * δ := by rw [hsub]; ring
  rw [hrw, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

/-- **Master `FastTwoSum` defect bound, either orientation.**

For the Dekker/Priest correction `w = fl(sr − a)`, `e = fl(b − w)` retaining the
pair `(sr, e)` for a leading value `sr` (in Priest, `sr = fl(a + b)`), the
relative-error model gives the identity
`(sr + e) − (a + b) = (b − w)·δ_e − (sr − a)·δ_w`,
hence `|(sr + e) − (a + b)| ≤ u|sr − a| + u|b − w|`.

Crucially **neither subtraction is assumed exact**: this is the honest defect in
the `|a| < |b|` (wrong) orientation where Dekker/Knuth exactness fails.  Setting
`a := c, b := x, sr := fl(c + x)` gives the Priest first-correction defect. -/
theorem priestDB_twoSum_defect_bound (fp : FPModel) (a b sr : ℝ) :
    |(sr + fp.fl_sub b (fp.fl_sub sr a)) - (a + b)|
      ≤ fp.u * |sr - a| + fp.u * |b - fp.fl_sub sr a| := by
  obtain ⟨δw, hδw, hw⟩ := fp.model_sub sr a
  obtain ⟨δe, hδe, he⟩ := fp.model_sub b (fp.fl_sub sr a)
  have hid :
      (sr + fp.fl_sub b (fp.fl_sub sr a)) - (a + b)
        = (b - fp.fl_sub sr a) * δe - (sr - a) * δw := by
    rw [he]; linear_combination -hw
  rw [hid]
  have h1 : |(b - fp.fl_sub sr a) * δe| ≤ |b - fp.fl_sub sr a| * fp.u := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hδe (abs_nonneg _)
  have h2 : |(sr - a) * δw| ≤ |sr - a| * fp.u := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hδw (abs_nonneg _)
  calc |(b - fp.fl_sub sr a) * δe - (sr - a) * δw|
      ≤ |(b - fp.fl_sub sr a) * δe| + |(sr - a) * δw| := by
          have h := abs_add_le ((b - fp.fl_sub sr a) * δe) (-((sr - a) * δw))
          rwa [← sub_eq_add_neg, abs_neg] at h
    _ ≤ |b - fp.fl_sub sr a| * fp.u + |sr - a| * fp.u := add_le_add h1 h2
    _ = fp.u * |sr - a| + fp.u * |b - fp.fl_sub sr a| := by ring

/-- **The crux: Priest's first correction in the wrong orientation.**

The `(yₖ, uₖ)` correction is `yₖ = fl(c + x)`, `uₖ = fl(x − fl(yₖ − c))`, i.e.
`FastTwoSum(c, x)` with the *tiny* addend `c` first and the *large* summand `x`
second: `|c| ≤ |x|`.  This is the opposite of the Dekker/Knuth order under which
`finiteCorrectionFormulaTrace_exact_of_base2_abs_gt` gives exactness, so
`yₖ + uₖ ≠ c + x` in general.  Derived (not assumed) from the relative-error
model, the defect is nonetheless of order `u|x|`:

`|(yₖ + uₖ) − (c + x)| ≤ (u + 5u² + 2u³)|x|`.

This is the honest replacement for the too-strong `PriestStepExact.addOne`. -/
theorem priestDB_ft1_defect_wrongOrientation (fp : FPModel) (c x : ℝ)
    (h : |c| ≤ |x|) :
    |(fp.fl_add c x + fp.fl_sub x (fp.fl_sub (fp.fl_add c x) c)) - (c + x)|
      ≤ (fp.u + 5 * fp.u ^ 2 + 2 * fp.u ^ 3) * |x| := by
  have hu := fp.u_nonneg
  have hbound := priestDB_twoSum_defect_bound fp c x (fp.fl_add c x)
  obtain ⟨δs, hδs, hs⟩ := fp.model_add c x
  obtain ⟨δw, hδw, hw⟩ := fp.model_sub (fp.fl_add c x) c
  have hYc : |fp.fl_add c x - c| ≤ |x| + |c + x| * fp.u := by
    have hrw : fp.fl_add c x - c = x + (c + x) * δs := by rw [hs]; ring
    rw [hrw]
    calc |x + (c + x) * δs| ≤ |x| + |(c + x) * δs| := abs_add_le _ _
      _ = |x| + |c + x| * |δs| := by rw [abs_mul]
      _ ≤ |x| + |c + x| * fp.u := by gcongr
  have hxW : |x - fp.fl_sub (fp.fl_add c x) c|
      ≤ |c + x| * fp.u + |fp.fl_add c x - c| * fp.u := by
    have hrw : x - fp.fl_sub (fp.fl_add c x) c
        = -((c + x) * δs) - (fp.fl_add c x - c) * δw := by rw [hw, hs]; ring
    rw [hrw]
    calc |-((c + x) * δs) - (fp.fl_add c x - c) * δw|
        ≤ |-((c + x) * δs)| + |(fp.fl_add c x - c) * δw| := abs_sub _ _
      _ = |c + x| * |δs| + |fp.fl_add c x - c| * |δw| := by
            rw [abs_neg, abs_mul, abs_mul]
      _ ≤ |c + x| * fp.u + |fp.fl_add c x - c| * fp.u := by gcongr
  have hcx : |c + x| ≤ 2 * |x| :=
    calc |c + x| ≤ |c| + |x| := abs_add_le _ _
      _ ≤ 2 * |x| := by linarith
  set X := |x| with hXdef
  set C := |c + x| with hCdef
  set Yc := |fp.fl_add c x - c| with hYcdef
  set xW := |x - fp.fl_sub (fp.fl_add c x) c| with hxWdef
  have hXnn : 0 ≤ X := abs_nonneg _
  have hCnn : 0 ≤ C := abs_nonneg _
  have hxW2 : xW ≤ C * fp.u + (X + C * fp.u) * fp.u :=
    calc xW ≤ C * fp.u + Yc * fp.u := hxW
      _ ≤ C * fp.u + (X + C * fp.u) * fp.u := by gcongr
  have e1 : fp.u * Yc ≤ fp.u * (X + C * fp.u) := by gcongr
  have e2 : fp.u * xW ≤ fp.u * (C * fp.u + (X + C * fp.u) * fp.u) := by gcongr
  have hfinal :
      fp.u * Yc + fp.u * xW ≤ (fp.u + 5 * fp.u ^ 2 + 2 * fp.u ^ 3) * X := by
    nlinarith [e1, e2,
      mul_nonneg (mul_nonneg hu hu) (by linarith : (0:ℝ) ≤ 2 * X - C),
      mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) (by linarith : (0:ℝ) ≤ 2 * X - C)]
  linarith [hbound, hfinal]

/-! ## The per-step total defect -/

/-- **Per-step total defect.**  The amount by which one Priest step fails to add
`xₖ` exactly to the running total `s + c`.  Under exact arithmetic this is `0`
(`priestDB_stepDefect_eq_zero_of_exact`); in a finite model it is the sum of the
four local `FastTwoSum`/combine defects (`priestDB_stepDefect_bound`). -/
noncomputable def priestDB_stepDefect (fp : FPModel) (xk : ℝ) (st : PriestState) : ℝ :=
  ((priestStep fp xk st).s + (priestStep fp xk st).c) - (st.s + st.c + xk)

/-- Definitional form: one step gains `xₖ` up to its per-step defect. -/
theorem priestDB_step_totalCorrection (fp : FPModel) (xk : ℝ) (st : PriestState) :
    (priestStep fp xk st).s + (priestStep fp xk st).c
      = st.s + st.c + xk + priestDB_stepDefect fp xk st := by
  unfold priestDB_stepDefect; ring

/-- Under a per-step exact step (Priest's *idealization*), the per-step defect
vanishes.  Hence the defect-bounded invariant strictly generalizes the exact
invariant of `PriestAccuracy.lean`. -/
theorem priestDB_stepDefect_eq_zero_of_exact
    (fp : FPModel) (xk : ℝ) (st : PriestState) (h : PriestStepExact fp xk st) :
    priestDB_stepDefect fp xk st = 0 := by
  unfold priestDB_stepDefect
  rw [priestStep_totalCorrection_of_exact fp xk st h]; ring

/-- **Per-step defect bound.**  The per-step defect is bounded by `u` times the
operand magnitudes of the step's four local operations: the FT1 correction
`(y,u) = FastTwoSum(c,x)`, the FT2 correction `(t,υ) = FastTwoSum(s,y)`, the
combine `z = fl(u+υ)`, and the FT3 correction `(s',c') = FastTwoSum(t,z)`.  Each
term comes from `priestDB_twoSum_defect_bound` / `priestDB_add_defect_bound`; none
assumes exactness.  Summing this over the sorted loop is Priest's accumulation. -/
theorem priestDB_stepDefect_bound (fp : FPModel) (xk : ℝ) (st : PriestState) :
    |priestDB_stepDefect fp xk st| ≤
      (fp.u * |(priestStepTrace fp xk st).y - st.c|
        + fp.u * |xk - fp.fl_sub (priestStepTrace fp xk st).y st.c|)
      + (fp.u * |(priestStepTrace fp xk st).t - st.s|
        + fp.u * |(priestStepTrace fp xk st).y
            - fp.fl_sub (priestStepTrace fp xk st).t st.s|)
      + fp.u * |(priestStepTrace fp xk st).u + (priestStepTrace fp xk st).upsilon|
      + (fp.u * |(priestStepTrace fp xk st).s - (priestStepTrace fp xk st).t|
        + fp.u * |(priestStepTrace fp xk st).z
            - fp.fl_sub (priestStepTrace fp xk st).s (priestStepTrace fp xk st).t|) := by
  set T := priestStepTrace fp xk st with hT
  -- The four raw local defects.
  have hd1 : |(T.y + T.u) - (st.c + xk)|
      ≤ fp.u * |T.y - st.c| + fp.u * |xk - fp.fl_sub T.y st.c| := by
    have := priestDB_twoSum_defect_bound fp st.c xk T.y
    -- T.u = fp.fl_sub xk (fp.fl_sub T.y st.c)
    have hu : T.u = fp.fl_sub xk (fp.fl_sub T.y st.c) := priestStepTrace_u fp xk st
    rw [hu]; simpa using this
  have hd2 : |(T.t + T.upsilon) - (st.s + T.y)|
      ≤ fp.u * |T.t - st.s| + fp.u * |T.y - fp.fl_sub T.t st.s| := by
    have := priestDB_twoSum_defect_bound fp st.s T.y T.t
    have hups : T.upsilon = fp.fl_sub T.y (fp.fl_sub T.t st.s) :=
      priestStepTrace_upsilon fp xk st
    rw [hups]; simpa using this
  have hd3 : |T.z - (T.u + T.upsilon)| ≤ fp.u * |T.u + T.upsilon| := by
    have := priestDB_add_defect_bound fp T.u T.upsilon
    have hz : T.z = fp.fl_add T.u T.upsilon := priestStepTrace_z fp xk st
    rw [hz]; simpa using this
  have hd4 : |(T.s + T.c) - (T.t + T.z)|
      ≤ fp.u * |T.s - T.t| + fp.u * |T.z - fp.fl_sub T.s T.t| := by
    have := priestDB_twoSum_defect_bound fp T.t T.z T.s
    have hc : T.c = fp.fl_sub T.z (fp.fl_sub T.s T.t) := priestStepTrace_c fp xk st
    rw [hc]; simpa using this
  -- stepDefect equals the sum of the four raw defects.
  have hsum : priestDB_stepDefect fp xk st
      = ((T.y + T.u) - (st.c + xk)) + ((T.t + T.upsilon) - (st.s + T.y))
        + (T.z - (T.u + T.upsilon)) + ((T.s + T.c) - (T.t + T.z)) := by
    have hs : (priestStep fp xk st).s = T.s := rfl
    have hc : (priestStep fp xk st).c = T.c := rfl
    unfold priestDB_stepDefect
    rw [hs, hc]; ring
  rw [hsum]
  calc |((T.y + T.u) - (st.c + xk)) + ((T.t + T.upsilon) - (st.s + T.y))
          + (T.z - (T.u + T.upsilon)) + ((T.s + T.c) - (T.t + T.z))|
      ≤ (|(T.y + T.u) - (st.c + xk)| + |(T.t + T.upsilon) - (st.s + T.y)|
          + |T.z - (T.u + T.upsilon)|) + |(T.s + T.c) - (T.t + T.z)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add hd1 hd2) hd3) hd4
        linarith [this]

/-! ## The defect-bounded accumulation invariant -/

/-- **Defect-bounded accumulation.**  After `k` tail steps the running pair
`(s, c)` equals the exact partial sum of the first `k+1` inputs *plus* the
accumulated per-step defect.  This generalizes `priest_prefixState_totalCorrection`
(which forced every defect to be `0`): here no exactness is assumed. -/
theorem priestDB_prefixState_accumulation (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (priestPrefixState fp x k hk).s + (priestPrefixState fp x k hk).c
        = (∑ i : Fin (k + 1), x (Fin.castLE (Nat.succ_le_succ hk) i))
          + ∑ j : Fin k, priestDB_stepDefect fp
              (x ⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.isLt hk)⟩)
              (priestPrefixState fp x j.val
                (Nat.le_of_lt (Nat.lt_of_lt_of_le j.isLt hk))) := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [Fin.sum_univ_one, Fin.sum_univ_zero, add_zero]
    simp only [priestPrefixState, Fin.foldl_zero, priestInitialState, add_zero]
    congr 1
  | succ k ih =>
    intro hk
    have hstep :
        (priestPrefixState fp x (k + 1) hk).s +
            (priestPrefixState fp x (k + 1) hk).c
          = ((priestPrefixState fp x k (by omega)).s +
              (priestPrefixState fp x k (by omega)).c)
            + x ⟨k + 1, by omega⟩
            + priestDB_stepDefect fp (x ⟨k + 1, by omega⟩)
                (priestPrefixState fp x k (by omega)) := by
      rw [priestPrefixState_succ fp x k hk]
      exact priestDB_step_totalCorrection fp _ _
    have hXsplit :
        (∑ i : Fin (k + 1 + 1), x (Fin.castLE (Nat.succ_le_succ hk) i))
          = (∑ i : Fin (k + 1),
              x (Fin.castLE (Nat.succ_le_succ (by omega : k ≤ n)) i))
            + x ⟨k + 1, by omega⟩ := by
      rw [Fin.sum_univ_castSucc]
      congr 1
    have hDsplit :
        (∑ j : Fin (k + 1), priestDB_stepDefect fp
            (x ⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.isLt hk)⟩)
            (priestPrefixState fp x j.val
              (Nat.le_of_lt (Nat.lt_of_lt_of_le j.isLt hk))))
          = (∑ j : Fin k, priestDB_stepDefect fp
              (x ⟨j.val + 1,
                Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.isLt (by omega : k ≤ n))⟩)
              (priestPrefixState fp x j.val
                (Nat.le_of_lt (Nat.lt_of_lt_of_le j.isLt (by omega : k ≤ n)))))
            + priestDB_stepDefect fp (x ⟨k + 1, by omega⟩)
                (priestPrefixState fp x k (by omega)) := by
      rw [Fin.sum_univ_castSucc]
      congr 1
    rw [hstep, ih (by omega), hXsplit, hDsplit]
    ring

/-- The accumulated per-step defect over the full sorted run. -/
noncomputable def priestDB_totalDefect (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j : Fin n, priestDB_stepDefect fp
    (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
    (priestPrefixState fp x j.val (Nat.le_of_lt j.isLt))

/-- **Defect-bounded running invariant.**  The final Priest pair satisfies
`sₙ + cₙ = Σ xᵢ + (accumulated defect)`.  When every step is exact
(`PriestAllStepsExact`) the accumulated defect is `0` and this is exactly
`priest_running_invariant`; in general the defect is controlled by
`priestDB_stepDefect_bound`. -/
theorem priestDB_running_invariant (fp : FPModel) {n : ℕ} (x : Fin (n + 1) → ℝ) :
    (fl_priestState fp x).s + (fl_priestState fp x).c
      = (∑ i, x i) + priestDB_totalDefect fp x := by
  rw [fl_priestState_eq_prefixState,
    priestDB_prefixState_accumulation fp x n (Nat.le_refl n)]
  congr 1

/-- The accumulated defect is bounded by the sum of the per-step defect
magnitudes (triangle inequality over the loop). -/
theorem priestDB_totalDefect_abs_le (fp : FPModel) {n : ℕ} (x : Fin (n + 1) → ℝ) :
    |priestDB_totalDefect fp x|
      ≤ ∑ j : Fin n, |priestDB_stepDefect fp
          (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
          (priestPrefixState fp x j.val (Nat.le_of_lt j.isLt))| := by
  unfold priestDB_totalDefect
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## The residual and the printed accuracy bound -/

/-- **Priest's accumulated-defect budget** (the residual).

`|cₙ| + Σⱼ |Eⱼ| ≤ 2u|Σ xᵢ|`: the retained correction plus the accumulated
per-step defect stays within the `2u` budget.  This is **strictly weaker** than
`PriestAllStepsExact` (`priestDB_defectBudget_of_allStepsExact`), assumes **no**
exactness, and is exactly the accumulation Priest's thesis (§4.1) controls from
the sorted ordering `|x₁| ≥ ⋯ ≥ |xₙ|` and `n ≤ β^(t−3)`.
`priestDB_stepDefect_bound` reduces each `|Eⱼ|` to a concrete `u·(magnitude)`
sum. -/
def priestDB_defectBudget (fp : FPModel) {n : ℕ} (x : Fin (n + 1) → ℝ) : Prop :=
  |(fl_priestState fp x).c|
    + ∑ j : Fin n, |priestDB_stepDefect fp
        (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (priestPrefixState fp x j.val (Nat.le_of_lt j.isLt))|
      ≤ 2 * fp.u * |∑ i, x i|

/-- **Priest's accuracy theorem (Higham §4.3, Algorithm 4.3), defect-bounded
form.**  Under the accumulated-defect budget `priestDB_defectBudget` — the honest
replacement for the too-strong `PriestAllStepsExact` — the computed doubly
compensated sum satisfies the printed bound

  `|sₙ − ŝₙ| ≤ 2u|sₙ|`,   `sₙ = Σ xᵢ` the exact sum.

The proof uses the defect-bounded running invariant `sₙ + cₙ = Σ xᵢ + Σⱼ Eⱼ`:
then `Σ xᵢ − ŝₙ = cₙ − Σⱼ Eⱼ`, so `|Σ xᵢ − ŝₙ| ≤ |cₙ| + Σⱼ|Eⱼ| ≤ 2u|Σ xᵢ|`. -/
theorem priestDB_doublyCompensated_accuracy (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (H : priestDB_defectBudget fp x) :
    |(∑ i, x i) - fl_priestSum fp x| ≤ 2 * fp.u * |∑ i, x i| := by
  have hinv := priestDB_running_invariant fp x
  have hrw : (∑ i, x i) - fl_priestSum fp x
      = (fl_priestState fp x).c - priestDB_totalDefect fp x := by
    have hs : fl_priestSum fp x = (fl_priestState fp x).s := rfl
    rw [hs]; linarith [hinv]
  rw [hrw]
  calc |(fl_priestState fp x).c - priestDB_totalDefect fp x|
      ≤ |(fl_priestState fp x).c| + |priestDB_totalDefect fp x| := abs_sub _ _
    _ ≤ |(fl_priestState fp x).c|
          + ∑ j : Fin n, |priestDB_stepDefect fp
              (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (priestPrefixState fp x j.val (Nat.le_of_lt j.isLt))| := by
        gcongr
        exact priestDB_totalDefect_abs_le fp x
    _ ≤ 2 * fp.u * |∑ i, x i| := H

/-- **Non-vacuity and strict weakening.**  The exact-idealization hypothesis
`PriestAllStepsExact` of `PriestAccuracy.lean` implies the residual
`priestDB_defectBudget`: under it every per-step defect `Eⱼ` vanishes and the
imported final-correction bound gives `|cₙ| ≤ u|sₙ| ≤ 2u|sₙ|`.  Hence
`priestDB_defectBudget` is a genuine relaxation — a single accumulated-defect
inequality in place of the `4n` per-step exactness equations — and
`priestDB_doublyCompensated_accuracy` recovers the earlier
`priest_doublyCompensated_accuracy` as a special case. -/
theorem priestDB_defectBudget_of_allStepsExact (fp : FPModel) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hexact : PriestAllStepsExact fp x) :
    priestDB_defectBudget fp x := by
  unfold priestDB_defectBudget
  have hsum0 :
      (∑ j : Fin n, |priestDB_stepDefect fp
        (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (priestPrefixState fp x j.val (Nat.le_of_lt j.isLt))|) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [priestDB_stepDefect_eq_zero_of_exact fp _ _ (hexact j), abs_zero]
  rw [hsum0, add_zero]
  have hcbound := priest_final_correction_bound fp x hexact
  rw [priest_running_invariant fp x hexact] at hcbound
  have hu := fp.u_nonneg
  have hnn : (0:ℝ) ≤ |∑ i, x i| := abs_nonneg _
  nlinarith [hcbound, hu, hnn]

end NumStability
