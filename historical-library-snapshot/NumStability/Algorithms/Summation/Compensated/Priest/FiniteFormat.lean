import Mathlib.Tactic.Linarith
import NumStability.Algorithms.PriestAccuracy
import NumStability.Algorithms.PriestDefectBounded
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.DoublyCompensated
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.FloatingPoint.Model






namespace NumStability

open scoped BigOperators

/-!
# Priest Algorithm 4.3 in genuine finite operations

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §4.3,
Algorithm 4.3, p. 88, attributes the doubly compensated summation bound to
Priest, thesis §4.1.  This file separates the literal finite binary executor
from the safe-completion model used by the existing algebraic analysis.
-/

/-- The no-exception condition under which a safe-completion addition is the
genuine finite round-to-even addition. -/
def priestFinite_addCondition
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop :=
  fmt.finiteSystem b ∧
    (fmt.finiteNormalRange (a + b) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b)

/-- The no-exception condition under which a safe-completion subtraction is
the genuine finite round-to-even subtraction. -/
def priestFinite_subCondition
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop :=
  fmt.finiteNormalRange (a - b) ∨
    fmt.finiteRoundToEvenOp BasicOp.sub a b = a - b

theorem priestFinite_add_agrees_safe
    (fmt : FloatingPointFormat) {a b : ℝ}
    (h : priestFinite_addCondition fmt a b) :
    fmt.finiteRoundToEvenOp BasicOp.add a b =
      (kahanFF_model fmt).fl_add a b := by
  exact (kahanFF_fl_add_eq_finiteRoundToEvenOp fmt h.1 h.2).symm

theorem priestFinite_sub_agrees_safe
    (fmt : FloatingPointFormat) {a b : ℝ}
    (h : priestFinite_subCondition fmt a b) :
    fmt.finiteRoundToEvenOp BasicOp.sub a b =
      (kahanFF_model fmt).fl_sub a b := by
  rw [kahanFF_model_fl_sub]
  split_ifs with hr
  · rfl
  · rcases h with hrange | hexact
    · exact absurd hrange hr
    · exact hexact

/-- The ten genuine finite operations in one displayed Priest step. -/
noncomputable def priestFinite_stepTrace
    (fmt : FloatingPointFormat) (x : ℝ)
    (state : PriestState) : PriestStepTrace :=
  let y := fmt.finiteRoundToEvenOp BasicOp.add state.c x
  let ySubC := fmt.finiteRoundToEvenOp BasicOp.sub y state.c
  let u := fmt.finiteRoundToEvenOp BasicOp.sub x ySubC
  let t := fmt.finiteRoundToEvenOp BasicOp.add y state.s
  let tSubS := fmt.finiteRoundToEvenOp BasicOp.sub t state.s
  let upsilon := fmt.finiteRoundToEvenOp BasicOp.sub y tSubS
  let z := fmt.finiteRoundToEvenOp BasicOp.add u upsilon
  let s := fmt.finiteRoundToEvenOp BasicOp.add t z
  let sSubT := fmt.finiteRoundToEvenOp BasicOp.sub s t
  let c := fmt.finiteRoundToEvenOp BasicOp.sub z sSubT
  { y := y, u := u, t := t, upsilon := upsilon,
    z := z, s := s, c := c }

/-- Every operation-level no-exception obligation for a literal Priest step.
The operands are the actual values produced by the preceding finite
operations, so this is an executable trace condition rather than an abstract
roundoff budget. -/
structure PriestFiniteStepCondition
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState) : Prop where
  y : priestFinite_addCondition fmt state.c x
  ySubC : priestFinite_subCondition fmt
    (priestFinite_stepTrace fmt x state).y state.c
  u : priestFinite_subCondition fmt x
    (fmt.finiteRoundToEvenOp BasicOp.sub
      (priestFinite_stepTrace fmt x state).y state.c)
  t : priestFinite_addCondition fmt
    (priestFinite_stepTrace fmt x state).y state.s
  tSubS : priestFinite_subCondition fmt
    (priestFinite_stepTrace fmt x state).t state.s
  upsilon : priestFinite_subCondition fmt
    (priestFinite_stepTrace fmt x state).y
    (fmt.finiteRoundToEvenOp BasicOp.sub
      (priestFinite_stepTrace fmt x state).t state.s)
  z : priestFinite_addCondition fmt
    (priestFinite_stepTrace fmt x state).u
    (priestFinite_stepTrace fmt x state).upsilon
  s : priestFinite_addCondition fmt
    (priestFinite_stepTrace fmt x state).t
    (priestFinite_stepTrace fmt x state).z
  sSubT : priestFinite_subCondition fmt
    (priestFinite_stepTrace fmt x state).s
    (priestFinite_stepTrace fmt x state).t
  c : priestFinite_subCondition fmt
    (priestFinite_stepTrace fmt x state).z
    (fmt.finiteRoundToEvenOp BasicOp.sub
      (priestFinite_stepTrace fmt x state).s
      (priestFinite_stepTrace fmt x state).t)

/-- A genuine finite Priest step agrees field-by-field with the corresponding
safe-completion step whenever all ten primitive operations are in scope. -/
theorem priestFinite_stepTrace_eq_priestStepTrace
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState)
    (h : PriestFiniteStepCondition fmt x state) :
    priestFinite_stepTrace fmt x state =
      priestStepTrace (kahanFF_model fmt) x state := by
  let T := priestFinite_stepTrace fmt x state
  have hy : T.y = (kahanFF_model fmt).fl_add state.c x :=
    priestFinite_add_agrees_safe fmt h.y
  have hySubC :
      fmt.finiteRoundToEvenOp BasicOp.sub T.y state.c =
        (kahanFF_model fmt).fl_sub T.y state.c :=
    priestFinite_sub_agrees_safe fmt h.ySubC
  have hu : T.u = (kahanFF_model fmt).fl_sub x
      ((kahanFF_model fmt).fl_sub
        ((kahanFF_model fmt).fl_add state.c x) state.c) := by
    change fmt.finiteRoundToEvenOp BasicOp.sub x
        (fmt.finiteRoundToEvenOp BasicOp.sub T.y state.c) = _
    rw [priestFinite_sub_agrees_safe fmt h.u, hySubC, hy]
  have ht : T.t = (kahanFF_model fmt).fl_add
      ((kahanFF_model fmt).fl_add state.c x) state.s := by
    change fmt.finiteRoundToEvenOp BasicOp.add T.y state.s = _
    rw [priestFinite_add_agrees_safe fmt h.t, hy]
  have htSubS :
      fmt.finiteRoundToEvenOp BasicOp.sub T.t state.s =
        (kahanFF_model fmt).fl_sub T.t state.s :=
    priestFinite_sub_agrees_safe fmt h.tSubS
  have hups : T.upsilon = (kahanFF_model fmt).fl_sub
      ((kahanFF_model fmt).fl_add state.c x)
      ((kahanFF_model fmt).fl_sub
        ((kahanFF_model fmt).fl_add
          ((kahanFF_model fmt).fl_add state.c x) state.s) state.s) := by
    change fmt.finiteRoundToEvenOp BasicOp.sub T.y
        (fmt.finiteRoundToEvenOp BasicOp.sub T.t state.s) = _
    rw [priestFinite_sub_agrees_safe fmt h.upsilon, htSubS, hy, ht]
  have hz : T.z = (kahanFF_model fmt).fl_add
      ((kahanFF_model fmt).fl_sub x
        ((kahanFF_model fmt).fl_sub
          ((kahanFF_model fmt).fl_add state.c x) state.c))
      ((kahanFF_model fmt).fl_sub
        ((kahanFF_model fmt).fl_add state.c x)
        ((kahanFF_model fmt).fl_sub
          ((kahanFF_model fmt).fl_add
            ((kahanFF_model fmt).fl_add state.c x) state.s) state.s)) := by
    change fmt.finiteRoundToEvenOp BasicOp.add T.u T.upsilon = _
    rw [priestFinite_add_agrees_safe fmt h.z, hu, hups]
  have hs : T.s = (kahanFF_model fmt).fl_add
      ((kahanFF_model fmt).fl_add
        ((kahanFF_model fmt).fl_add state.c x) state.s)
      ((kahanFF_model fmt).fl_add
        ((kahanFF_model fmt).fl_sub x
          ((kahanFF_model fmt).fl_sub
            ((kahanFF_model fmt).fl_add state.c x) state.c))
        ((kahanFF_model fmt).fl_sub
          ((kahanFF_model fmt).fl_add state.c x)
          ((kahanFF_model fmt).fl_sub
            ((kahanFF_model fmt).fl_add
              ((kahanFF_model fmt).fl_add state.c x) state.s) state.s))) := by
    change fmt.finiteRoundToEvenOp BasicOp.add T.t T.z = _
    rw [priestFinite_add_agrees_safe fmt h.s, ht, hz]
  have hsSubT :
      fmt.finiteRoundToEvenOp BasicOp.sub T.s T.t =
        (kahanFF_model fmt).fl_sub T.s T.t :=
    priestFinite_sub_agrees_safe fmt h.sSubT
  have hc : T.c = (kahanFF_model fmt).fl_sub
      ((kahanFF_model fmt).fl_add
        ((kahanFF_model fmt).fl_sub x
          ((kahanFF_model fmt).fl_sub
            ((kahanFF_model fmt).fl_add state.c x) state.c))
        ((kahanFF_model fmt).fl_sub
          ((kahanFF_model fmt).fl_add state.c x)
          ((kahanFF_model fmt).fl_sub
            ((kahanFF_model fmt).fl_add
              ((kahanFF_model fmt).fl_add state.c x) state.s) state.s)))
      ((kahanFF_model fmt).fl_sub
        ((kahanFF_model fmt).fl_add
          ((kahanFF_model fmt).fl_add
            ((kahanFF_model fmt).fl_add state.c x) state.s)
          ((kahanFF_model fmt).fl_add
            ((kahanFF_model fmt).fl_sub x
              ((kahanFF_model fmt).fl_sub
                ((kahanFF_model fmt).fl_add state.c x) state.c))
            ((kahanFF_model fmt).fl_sub
              ((kahanFF_model fmt).fl_add state.c x)
              ((kahanFF_model fmt).fl_sub
                ((kahanFF_model fmt).fl_add
                  ((kahanFF_model fmt).fl_add state.c x) state.s)
                state.s))))
        ((kahanFF_model fmt).fl_add
          ((kahanFF_model fmt).fl_add state.c x) state.s)) := by
    change fmt.finiteRoundToEvenOp BasicOp.sub T.z
        (fmt.finiteRoundToEvenOp BasicOp.sub T.s T.t) = _
    rw [priestFinite_sub_agrees_safe fmt h.c, hsSubT, hz, hs, ht]
  change T = priestStepTrace (kahanFF_model fmt) x state
  cases hT : T with
  | mk yT uT tT upsT zT sT cT =>
      simp only [priestStepTrace, PriestStepTrace.mk.injEq]
      exact ⟨by simpa [hT] using hy,
        by simpa [hT] using hu,
        by simpa [hT] using ht,
        by simpa [hT] using hups,
        by simpa [hT] using hz,
        by simpa [hT] using hs,
        by simpa [hT] using hc⟩

/-- Persistent-state update of the genuine finite executor. -/
noncomputable def priestFinite_step
    (fmt : FloatingPointFormat) (x : ℝ)
    (state : PriestState) : PriestState :=
  (priestFinite_stepTrace fmt x state).nextState

theorem priestFinite_step_eq_priestStep
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState)
    (h : PriestFiniteStepCondition fmt x state) :
    priestFinite_step fmt x state =
      priestStep (kahanFF_model fmt) x state := by
  unfold priestFinite_step priestStep
  rw [priestFinite_stepTrace_eq_priestStepTrace fmt x state h]

/-- State after the first `k` tail iterations of the literal finite program. -/
noncomputable def priestFinite_prefixState
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) : PriestState :=
  Fin.foldl k
    (fun state i =>
      priestFinite_step fmt
        (x ⟨i.val + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩)
        state)
    (priestInitialState x)

/-- All operation-level no-exception obligations along the actual finite run. -/
def PriestFiniteAllOperations
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i : Fin n,
    PriestFiniteStepCondition fmt
      (x ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (priestFinite_prefixState fmt x i.val (Nat.le_of_lt i.isLt))

/-- Every literal finite prefix agrees with the corresponding analytic
safe-completion prefix. -/
theorem priestFinite_prefixState_eq_priestPrefixState
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hall : PriestFiniteAllOperations fmt x) :
    ∀ (k : ℕ) (hk : k ≤ n),
      priestFinite_prefixState fmt x k hk =
        priestPrefixState (kahanFF_model fmt) x k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [priestFinite_prefixState, priestPrefixState]
  | succ k ih =>
      intro hk
      have hactual :
          priestFinite_prefixState fmt x (k + 1) hk =
            priestFinite_step fmt (x ⟨k + 1, by omega⟩)
              (priestFinite_prefixState fmt x k (by omega)) := by
        unfold priestFinite_prefixState
        rw [Fin.foldl_succ_last]
        congr 1
      have hsafe :
          priestPrefixState (kahanFF_model fmt) x (k + 1) hk =
            priestStep (kahanFF_model fmt) (x ⟨k + 1, by omega⟩)
              (priestPrefixState (kahanFF_model fmt) x k (by omega)) :=
        priestPrefixState_succ (kahanFF_model fmt) x k hk
      have hcond : PriestFiniteStepCondition fmt
          (x ⟨k + 1, by omega⟩)
          (priestFinite_prefixState fmt x k (by omega)) := by
        simpa using hall ⟨k, by omega⟩
      rw [hactual, hsafe,
        priestFinite_step_eq_priestStep fmt _ _ hcond,
        ih (by omega)]

/-- Final state and returned value of the literal finite Algorithm 4.3. -/
noncomputable def priestFinite_state
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : PriestState :=
  priestFinite_prefixState fmt x n (Nat.le_refl n)

noncomputable def priestFinite_sum
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (priestFinite_state fmt x).s

theorem priestFinite_state_eq_fl_priestState
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hall : PriestFiniteAllOperations fmt x) :
    priestFinite_state fmt x =
      fl_priestState (kahanFF_model fmt) x := by
  exact priestFinite_prefixState_eq_priestPrefixState
    fmt x hall n (Nat.le_refl n)

theorem priestFinite_sum_eq_fl_priestSum
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hall : PriestFiniteAllOperations fmt x) :
    priestFinite_sum fmt x = fl_priestSum (kahanFF_model fmt) x := by
  exact congrArg PriestState.s
    (priestFinite_state_eq_fl_priestState fmt x hall)

/-! ## Priest's literal source assumptions

Priest's thesis, §2.3 and §4.1, does not assume that all four local operations
in a doubly compensated step are exact.  It assumes faithful arithmetic and
the following three independent arithmetic properties.  We record them here
against the actual finite round-to-even operation, without replacing them by
an accumulated error budget.
-/

/-- A value is an integer multiple of the ulp belonging to a supplied
normalized representation of `b`.  This is the literal divisibility relation
used in Priest's properties S4 and Lemma 1. -/
def priestSourceUlpMultiple
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop :=
  ∃ e : ℤ, fmt.normalizedExponentRepresentation b e ∧
    ∃ k : ℤ, a = (k : ℝ) * fmt.ulpAtExponent e
























































































































/-! ## Priest's three exact local correction pairs

The thesis proof does not make the rounded combine `z = fl(u+υ)` exact.  It
proves only the three surrounding sum-and-roundoff pairs exact.  The following
finite-format lemma realizes Priest's displayed subtraction orientation
`b - (s-a)` from the same representability certificate used by FastTwoSum.
-/
































































































































































end NumStability
