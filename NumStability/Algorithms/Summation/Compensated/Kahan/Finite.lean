-- Algorithms/Summation/Compensated/Kahan/Finite.lean

import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients

namespace NumStability

/-!
# Kahan compensated summation: finite-format execution

This module provides the concrete finite round-to-even execution API,
finite-system closure, model realization bridges, and correction-subtraction
certificates used by higher reusable bounds and source audits.
-/

/-- One Algorithm 4.2 step specialized to the source-facing finite
round-to-even selector of a `FloatingPointFormat`.  This is the concrete
finite-format wrapper used for result-by-result audits such as Problem 4.10. -/
noncomputable def finiteKahanStepTrace (fmt : FloatingPointFormat) (x : ℝ)
    (state : KahanState) : KahanStepTrace :=
  let temp := state.s
  let y := fmt.finiteRoundToEvenOp BasicOp.add x state.e
  let s := fmt.finiteRoundToEvenOp BasicOp.add temp y
  let e := fmt.finiteRoundToEvenOp BasicOp.add
    (fmt.finiteRoundToEvenOp BasicOp.sub temp s) y
  { temp := temp, y := y, s := s, e := e }

/-- Persistent-state update induced by one finite-format Kahan step. -/
noncomputable def finiteKahanStep (fmt : FloatingPointFormat) (x : ℝ)
    (state : KahanState) : KahanState :=
  (finiteKahanStepTrace fmt x state).nextState




/-- The `temp` assignment in the finite-format Algorithm 4.2 wrapper. -/
theorem finiteKahanStepTrace_temp
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).temp = state.s := by
  rfl

/-- The `y = x_i + e` assignment in the finite-format Algorithm 4.2 wrapper. -/
theorem finiteKahanStepTrace_y
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).y =
      fmt.finiteRoundToEvenOp BasicOp.add x state.e := by
  rfl

/-- The `s = temp + y` assignment in the finite-format Algorithm 4.2 wrapper. -/
theorem finiteKahanStepTrace_s
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).s =
      fmt.finiteRoundToEvenOp BasicOp.add
        (finiteKahanStepTrace fmt x state).temp
        (finiteKahanStepTrace fmt x state).y := by
  rfl

/-- The `e = (temp - s) + y` assignment in the finite-format Algorithm 4.2
wrapper, in the displayed evaluation order. -/
theorem finiteKahanStepTrace_e
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    (finiteKahanStepTrace fmt x state).e =
      fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.finiteRoundToEvenOp BasicOp.sub
          (finiteKahanStepTrace fmt x state).temp
          (finiteKahanStepTrace fmt x state).s)
        (finiteKahanStepTrace fmt x state).y := by
  rfl

/-- Finite-format coherence for the first Algorithm 4.2 step: if the input is
finite representable, then the concrete finite round-to-even wrapper starts from
`s = 0; e = 0` exactly, returning `s = x` and zero correction.

This records the finite-format zero-add/subtract exactness that the abstract
`FPModel` interface intentionally does not assume. -/
theorem finiteKahanStepTrace_zero_of_finiteSystem
    (fmt : FloatingPointFormat) {x : ℝ} (hx : fmt.finiteSystem x) :
    finiteKahanStepTrace fmt x KahanState.zero =
      { temp := 0, y := x, s := x, e := 0 } := by
  have hy :
      fmt.finiteRoundToEvenOp BasicOp.add x 0 = x :=
    fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem hx
  have hs :
      fmt.finiteRoundToEvenOp BasicOp.add 0 x = x :=
    fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem hx
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub 0 x = -x := by
    have hfin : fmt.finiteSystem (BasicOp.exact BasicOp.sub 0 x) := by
      simpa [BasicOp.exact] using fmt.finiteSystem_neg hx
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := 0) (y := x) hfin)
  have he :
      fmt.finiteRoundToEvenOp BasicOp.add (-x) x = 0 := by
    have hfin : fmt.finiteSystem (BasicOp.exact BasicOp.add (-x) x) := by
      simpa [BasicOp.exact] using fmt.finiteSystem_zero
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add) (x := -x) (y := x) hfin)
  simp [finiteKahanStepTrace, KahanState.zero, hy, hs, hsub, he]

/-- Persistent-state form of `finiteKahanStepTrace_zero_of_finiteSystem`. -/
theorem finiteKahanStep_zero_of_finiteSystem
    (fmt : FloatingPointFormat) {x : ℝ} (hx : fmt.finiteSystem x) :
    finiteKahanStep fmt x KahanState.zero = { s := x, e := 0 } := by
  have htrace := finiteKahanStepTrace_zero_of_finiteSystem fmt hx
  simpa [finiteKahanStep, KahanStepTrace.nextState] using congrArg KahanStepTrace.nextState htrace

/-- State after the first `k` finite-format Kahan steps over a length-`n`
input. -/
noncomputable def finiteKahanPrefixState (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : KahanState :=
  Fin.foldl k
    (fun state i =>
      finiteKahanStep fmt (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) state)
    KahanState.zero

/-- One-element finite-format Kahan prefix state.  This is the prefix-level
version of the exact first-step coherence theorem and matches the source proof
initialization `S_1 = x_1`, with zero retained correction. -/
theorem finiteKahanPrefixState_one_of_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ} (v : Fin n → ℝ) (hn : 1 ≤ n)
    (hx :
      fmt.finiteSystem
        (v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩)) :
    finiteKahanPrefixState fmt v 1 hn =
      { s := v ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩, e := 0 } := by
  rw [finiteKahanPrefixState, Fin.foldl_succ]
  simpa using
    finiteKahanStep_zero_of_finiteSystem fmt hx

/-- The per-index finite-format Kahan step trace, with the input state obtained
by running all earlier finite-format steps. -/
noncomputable def finiteKahanTrace (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : KahanStepTrace :=
  finiteKahanStepTrace fmt (v i)
    (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- Final finite-format Kahan state after processing all `n` inputs. -/
noncomputable def finiteKahanState (fmt : FloatingPointFormat) (n : ℕ)
    (v : Fin n → ℝ) : KahanState :=
  finiteKahanPrefixState fmt v n (Nat.le_refl n)

/-- Final finite-format compensated-summation value returned by Algorithm 4.2. -/
noncomputable def finiteKahanSum (fmt : FloatingPointFormat) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (finiteKahanState fmt n v).s

/-- Final finite-format correction term retained by Algorithm 4.2. -/
noncomputable def finiteKahanCorrection (fmt : FloatingPointFormat) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  (finiteKahanState fmt n v).e

/-- The finite-format `y = fl(x+e)` value in one Kahan step is finite. -/
theorem finiteKahanStepTrace_y_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStepTrace fmt x state).y := by
  simpa [finiteKahanStepTrace] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add x state.e

/-- The finite-format returned-sum coordinate in one Kahan step is finite. -/
theorem finiteKahanStepTrace_s_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStepTrace fmt x state).s := by
  simpa [finiteKahanStepTrace] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add state.s
      (fmt.finiteRoundToEvenOp BasicOp.add x state.e)

/-- The finite-format retained-correction coordinate in one Kahan step is
finite. -/
theorem finiteKahanStepTrace_e_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStepTrace fmt x state).e := by
  simpa [finiteKahanStepTrace] using
    fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add
      (fmt.finiteRoundToEvenOp BasicOp.sub state.s
        (fmt.finiteRoundToEvenOp BasicOp.add state.s
          (fmt.finiteRoundToEvenOp BasicOp.add x state.e)))
      (fmt.finiteRoundToEvenOp BasicOp.add x state.e)

/-- One finite-format Kahan persistent-state update has finite coordinates. -/
theorem finiteKahanStep_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) (state : KahanState) :
    fmt.finiteSystem (finiteKahanStep fmt x state).s ∧
      fmt.finiteSystem (finiteKahanStep fmt x state).e := by
  constructor
  · simpa [finiteKahanStep, KahanStepTrace.nextState] using
      finiteKahanStepTrace_s_finiteSystem fmt x state
  · simpa [finiteKahanStep, KahanStepTrace.nextState] using
      finiteKahanStepTrace_e_finiteSystem fmt x state

/-- Every finite-format Kahan prefix state has finite coordinates. -/
theorem finiteKahanPrefixState_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).s ∧
        fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).e
  | 0, _hk => by
      simp [finiteKahanPrefixState, KahanState.zero, fmt.finiteSystem_zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := finiteKahanPrefixState fmt v k hprev_le
      have hfold :
          finiteKahanPrefixState fmt v (k + 1) hk =
            finiteKahanStep fmt (v idx) prev := by
        unfold finiteKahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      rw [hfold]
      exact finiteKahanStep_finiteSystem fmt (v idx) prev

/-- Stored-sum projection of `finiteKahanPrefixState_finiteSystem`. -/
theorem finiteKahanPrefixState_s_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).s :=
  (finiteKahanPrefixState_finiteSystem fmt v k hk).1

/-- Retained-correction projection of `finiteKahanPrefixState_finiteSystem`. -/
theorem finiteKahanPrefixState_e_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    fmt.finiteSystem (finiteKahanPrefixState fmt v k hk).e :=
  (finiteKahanPrefixState_finiteSystem fmt v k hk).2

/-- The `temp` coordinate in every finite-format Kahan trace step is finite. -/
theorem finiteKahanTrace_temp_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fmt.finiteSystem (finiteKahanTrace fmt v i).temp := by
  simpa [finiteKahanTrace, finiteKahanStepTrace] using
    finiteKahanPrefixState_s_finiteSystem
      fmt v i.val (Nat.le_of_lt i.isLt)

/-- The `y` coordinate in every finite-format Kahan trace step is finite. -/
theorem finiteKahanTrace_y_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fmt.finiteSystem (finiteKahanTrace fmt v i).y := by
  simpa [finiteKahanTrace] using
    finiteKahanStepTrace_y_finiteSystem fmt (v i)
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- The returned-sum coordinate in every finite-format Kahan trace step is
finite. -/
theorem finiteKahanTrace_s_finiteSystem
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fmt.finiteSystem (finiteKahanTrace fmt v i).s := by
  simpa [finiteKahanTrace] using
    finiteKahanStepTrace_s_finiteSystem fmt (v i)
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- Add/sub realization of a concrete finite round-to-even format by the
abstract `FPModel` operations used in Algorithm 4.2.

The Kahan returned-sum theorem is stated for `FPModel`, while the exact
subtraction obligations are naturally finite-format facts.  This small bridge
records only the two primitive operations needed to identify the abstract
Kahan trace with the finite round-to-even trace. -/
structure KahanAddSubFiniteRoundToEvenRealization
    (fp : FPModel) (fmt : FloatingPointFormat) : Prop where
  add :
    ∀ x y : ℝ, fp.fl_add x y = fmt.finiteRoundToEvenOp BasicOp.add x y
  sub :
    ∀ x y : ℝ, fp.fl_sub x y = fmt.finiteRoundToEvenOp BasicOp.sub x y

/-- One abstract Kahan trace equals the corresponding finite round-to-even
trace when the model's add/sub primitives realize that finite format. -/
theorem kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (x : ℝ) (state : KahanState) :
    kahanStepTrace fp x state = finiteKahanStepTrace fmt x state := by
  simp [kahanStepTrace, finiteKahanStepTrace, hround.add, hround.sub]

/-- Persistent-state version of
`kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven`. -/
theorem kahanStep_eq_finiteKahanStep_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (x : ℝ) (state : KahanState) :
    kahanStep fp x state = finiteKahanStep fmt x state := by
  simp [kahanStep, finiteKahanStep,
    kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven
      fp fmt hround x state]

/-- The abstract and finite Kahan prefix states agree when add/sub operations
are the same finite round-to-even operations. -/
theorem kahanPrefixState_eq_finiteKahanPrefixState_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      kahanPrefixState fp v k hk = finiteKahanPrefixState fmt v k hk
  | 0, _hk => by
      simp [kahanPrefixState, finiteKahanPrefixState, KahanState.zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prevFp := kahanPrefixState fp v k hprev_le
      let prevFinite := finiteKahanPrefixState fmt v k hprev_le
      have hih :
          prevFp = prevFinite := by
        simpa [prevFp, prevFinite] using
          kahanPrefixState_eq_finiteKahanPrefixState_of_addSubFiniteRoundToEven
            fp fmt hround v k hprev_le
      have hfoldFp :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prevFp := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hfoldFinite :
          finiteKahanPrefixState fmt v (k + 1) hk =
            finiteKahanStep fmt (v idx) prevFinite := by
        unfold finiteKahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      rw [hfoldFp, hfoldFinite, hih]
      exact
        kahanStep_eq_finiteKahanStep_of_addSubFiniteRoundToEven
          fp fmt hround (v idx) prevFinite

/-- Per-index abstract Kahan traces agree with the finite round-to-even traces
under add/sub realization. -/
theorem kahanTrace_eq_finiteKahanTrace_of_addSubFiniteRoundToEven
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    kahanTrace fp v i = finiteKahanTrace fmt v i := by
  unfold kahanTrace finiteKahanTrace
  have hprefix :=
    kahanPrefixState_eq_finiteKahanPrefixState_of_addSubFiniteRoundToEven
      fp fmt hround v i.val (Nat.le_of_lt i.isLt)
  rw [hprefix]
  exact
    kahanStepTrace_eq_finiteKahanStepTrace_of_addSubFiniteRoundToEven
      fp fmt hround (v i)
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt))

/-- Finite-format representability surface for the displayed Kahan correction
subtraction `temp - s` over a prefix. -/
def FiniteKahanPrefixCorrectionSubFinite
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp - (finiteKahanTrace fmt v idx).s)

/-- First-step split for the direct finite-subtraction route.

At index `0`, the Kahan trace has `temp = 0`, so `temp - s = -s` is finite
from the rounded trace itself.  Consequently a direct tail proof of finite
representability for `temp - s` is enough for the whole prefix. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hfiniteTail :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteSystem
          ((finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s)) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  change
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp -
        (finiteKahanTrace fmt v idx).s)
  by_cases hi0 : i.val = 0
  · have hs : fmt.finiteSystem (finiteKahanTrace fmt v idx).s :=
      finiteKahanTrace_s_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hrewrite :
        (finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s =
          -((finiteKahanTrace fmt v idx).s) := by
      rw [htemp]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hs
  · simpa [idx] using hfiniteTail i hi0

/-- Inclusive Sterbenz conditions on the displayed Kahan correction
subtractions provide the finite representability surface needed by the
exact-subtraction route. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_sterbenzRatioConditionLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hsterbenz :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  exact
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe
      (finiteKahanTrace_temp_finiteSystem fmt v idx)
      (finiteKahanTrace_s_finiteSystem fmt v idx)
      (by simpa [idx] using hsterbenz i)

/-- Inclusive Ferguson exponent conditions on the displayed Kahan correction
subtractions provide the same finite representability surface.  This exposes a
non-FastTwoSum finite/coherence route for the remaining Eq. (4.8) bottleneck. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_fergusonConditionLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hferguson :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have hnormal :
      fmt.normalizedSystem
        ((finiteKahanTrace fmt v idx).temp -
          (finiteKahanTrace fmt v idx).s) :=
    fmt.fergusonExponentConditionLe_sub_normalized
      (by simpa [idx] using hferguson i)
  exact Or.inr (Or.inl hnormal)

/-- First-step split for the inclusive Sterbenz finite-subtraction route.

At index `0`, the Kahan trace has `temp = 0`, so `temp - s = -s` is finite
from the rounded trace itself.  Only tail steps need an inclusive Sterbenz
condition on the displayed correction subtraction. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hsterbenz :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  change
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp - (finiteKahanTrace fmt v idx).s)
  by_cases hi0 : i.val = 0
  · have hs : fmt.finiteSystem (finiteKahanTrace fmt v idx).s :=
      finiteKahanTrace_s_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hrewrite :
        (finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s =
          -((finiteKahanTrace fmt v idx).s) := by
      rw [htemp]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hs
  · exact
      fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe
        (finiteKahanTrace_temp_finiteSystem fmt v idx)
        (finiteKahanTrace_s_finiteSystem fmt v idx)
        (by simpa [idx] using hsterbenz i hi0)

/-- First-step split for the inclusive Ferguson finite-subtraction route.

The first correction subtraction is finite because `temp = 0`; tail steps may
instead be discharged by Ferguson's exponent condition. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hferguson :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  change
    fmt.finiteSystem
      ((finiteKahanTrace fmt v idx).temp - (finiteKahanTrace fmt v idx).s)
  by_cases hi0 : i.val = 0
  · have hs : fmt.finiteSystem (finiteKahanTrace fmt v idx).s :=
      finiteKahanTrace_s_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hrewrite :
        (finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s =
          -((finiteKahanTrace fmt v idx).s) := by
      rw [htemp]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hs
  · have hnormal :
        fmt.normalizedSystem
          ((finiteKahanTrace fmt v idx).temp -
            (finiteKahanTrace fmt v idx).s) :=
      fmt.fergusonExponentConditionLe_sub_normalized
        (by simpa [idx] using hferguson i hi0)
    exact Or.inr (Or.inl hnormal)

/-- Per-step FastTwoSum finite certificates for the Kahan correction formula
over a prefix.  The field `finite_a_sub_s` is exactly the representability
needed for the displayed subtraction in Algorithm 4.2. -/
def KahanPrefixFastTwoSumFiniteCertificates
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    FastTwoSumFiniteCertificate fmt
      (finiteKahanTrace fmt v idx).temp
      (finiteKahanTrace fmt v idx).y

/-- Pointwise base-2 absolute-order FastTwoSum hypotheses supply the prefix
finite certificates needed by the Kahan exact-subtraction bridge. -/
theorem KahanPrefixFastTwoSumFiniteCertificates.of_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hfiniteTemp :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteSystem (finiteKahanTrace fmt v idx).temp)
    (hfiniteY :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteSystem (finiteKahanTrace fmt v idx).y)
    (horder :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        |(finiteKahanTrace fmt v idx).y| <
          |(finiteKahanTrace fmt v idx).temp|)
    (hrange :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v idx).temp +
            (finiteKahanTrace fmt v idx).y)) :
    KahanPrefixFastTwoSumFiniteCertificates fmt v k hk := by
  intro i
  exact
    FastTwoSumFiniteCertificate.of_base2_abs_gt
      fmt hbeta ht
      (hfiniteTemp i)
      (hfiniteY i)
      (horder i)
      (hrange i)

/-- Kahan-prefix FastTwoSum certificates with the initialized first step split
off.

At index `0`, the Kahan `temp` value is exactly zero, so the usual strict
absolute-order premise `|y| < |temp|` is not the right hypothesis.  The first
step instead uses exact finite zero-addition; the base-2 absolute-order and
normal-range hypotheses are required only for the tail steps. -/
theorem KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (horder :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        |(finiteKahanTrace fmt v idx).y| <
          |(finiteKahanTrace fmt v idx).temp|)
    (hrange :
      ∀ i : Fin k, i.val ≠ 0 →
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v idx).temp +
            (finiteKahanTrace fmt v idx).y)) :
    KahanPrefixFastTwoSumFiniteCertificates fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  by_cases hi0 : i.val = 0
  · have hy :
        fmt.finiteSystem (finiteKahanTrace fmt v idx).y :=
      finiteKahanTrace_y_finiteSystem fmt v idx
    have htemp : (finiteKahanTrace fmt v idx).temp = 0 := by
      simp [finiteKahanTrace, finiteKahanStepTrace,
        finiteKahanPrefixState, KahanState.zero, idx, hi0]
    have hadd :
        fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v idx).temp
            (finiteKahanTrace fmt v idx).y =
          (finiteKahanTrace fmt v idx).temp +
            (finiteKahanTrace fmt v idx).y := by
      rw [htemp]
      simpa using fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem hy
    exact
      FastTwoSumFiniteCertificate.of_exact_add
        fmt (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).y hy hadd
  · exact
      FastTwoSumFiniteCertificate.of_base2_abs_gt
        fmt hbeta ht
        (finiteKahanTrace_temp_finiteSystem fmt v idx)
        (finiteKahanTrace_y_finiteSystem fmt v idx)
        (by simpa [idx] using horder i hi0)
        (by simpa [idx] using hrange i hi0)

/-- A FastTwoSum finite certificate supplies the finite representability
needed by the Kahan displayed correction subtraction. -/
theorem FiniteKahanPrefixCorrectionSubFinite.of_fastTwoSumCertificates
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hcerts : KahanPrefixFastTwoSumFiniteCertificates fmt v k hk) :
    FiniteKahanPrefixCorrectionSubFinite fmt v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have hcert :
      FastTwoSumFiniteCertificate fmt
        (finiteKahanTrace fmt v idx).temp
        (finiteKahanTrace fmt v idx).y := by
    simpa [KahanPrefixFastTwoSumFiniteCertificates, idx] using hcerts i
  have hs :
      (finiteKahanTrace fmt v idx).s =
        fmt.finiteRoundToEvenOp BasicOp.add
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).y := by
    simp [finiteKahanTrace, finiteKahanStepTrace]
  simpa [FiniteKahanPrefixCorrectionSubFinite, idx, hs] using
    hcert.finite_a_sub_s

/-- Concrete finite-format representability of every correction subtraction
implies the abstract prefix exact-subtraction surface for Algorithm 4.2. -/
theorem KahanPrefixCorrectionSubExact.of_finiteRoundToEven_sub_finite
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hfinite : FiniteKahanPrefixCorrectionSubFinite fmt v k hk) :
    KahanPrefixCorrectionSubExact fp v k hk := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have htrace :
      kahanTrace fp v idx = finiteKahanTrace fmt v idx :=
    kahanTrace_eq_finiteKahanTrace_of_addSubFiniteRoundToEven
      fp fmt hround v idx
  have hfin :
      fmt.finiteSystem
        ((finiteKahanTrace fmt v idx).temp -
          (finiteKahanTrace fmt v idx).s) := by
    simpa [FiniteKahanPrefixCorrectionSubFinite, idx] using hfinite i
  have hsubFinite :
      fmt.finiteRoundToEvenOp BasicOp.sub
          (finiteKahanTrace fmt v idx).temp
          (finiteKahanTrace fmt v idx).s =
        (finiteKahanTrace fmt v idx).temp -
          (finiteKahanTrace fmt v idx).s := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub)
        (x := (finiteKahanTrace fmt v idx).temp)
        (y := (finiteKahanTrace fmt v idx).s) hfin)
  have htarget :
      fp.fl_sub (kahanTrace fp v idx).temp (kahanTrace fp v idx).s =
        (kahanTrace fp v idx).temp - (kahanTrace fp v idx).s := by
    simpa [htrace, hround.sub] using hsubFinite
  simpa [KahanPrefixCorrectionSubExact, idx] using htarget

/-- FastTwoSum finite certificates imply the abstract prefix exact-subtraction
surface for the Kahan returned-sum theorem. -/
theorem KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hcerts : KahanPrefixFastTwoSumFiniteCertificates fmt v k hk) :
    KahanPrefixCorrectionSubExact fp v k hk :=
  KahanPrefixCorrectionSubExact.of_finiteRoundToEven_sub_finite
    fp fmt hround v k hk
    (FiniteKahanPrefixCorrectionSubFinite.of_fastTwoSumCertificates
      fmt v k hk hcerts)

end NumStability
