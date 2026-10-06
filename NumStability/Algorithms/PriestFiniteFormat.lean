import NumStability.Algorithms.PriestDefectBounded
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import Mathlib.Tactic.Linarith

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

/-- Priest property A1: the true roundoff error of a sum of floating-point
numbers is itself a floating-point number. -/
def PriestSourceA1 (fmt : FloatingPointFormat) : Prop :=
  ∀ ⦃a b : ℝ⦄, fmt.finiteSystem a → fmt.finiteSystem b →
    fmt.finiteSystem
      ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b)

/-- Priest property A2: if `|b| ≤ |a|`, then `|fl(a+b)| ≤ 2|a|`. -/
def PriestSourceA2 (fmt : FloatingPointFormat) : Prop :=
  ∀ ⦃a b : ℝ⦄, fmt.finiteSystem a → fmt.finiteSystem b →
    |b| ≤ |a| →
    |fmt.finiteRoundToEvenOp BasicOp.add a b| ≤ 2 * |a|

/-- Priest property S4: if `|a| ≤ |b|` and `a` lies on the ulp lattice of
`b`, then the displayed inner subtraction in the sum-and-error formula is
exact. -/
def PriestSourceS4 (fmt : FloatingPointFormat) : Prop :=
  ∀ ⦃a b : ℝ⦄, fmt.finiteSystem a → fmt.finiteSystem b →
    |a| ≤ |b| → priestSourceUlpMultiple fmt a b →
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.finiteRoundToEvenOp BasicOp.add a b) a =
      fmt.finiteRoundToEvenOp BasicOp.add a b - a

/-- The bounded-format scope corresponding to one source arithmetic
operation: its exact result is either zero or lies in the finite normal
range.  This is the precise place where the literal bounded executor rules
out overflow, saturation, and nonzero underflow. -/
def priestSourceOperationRange
    (fmt : FloatingPointFormat) (op : BasicOp) (a b : ℝ) : Prop :=
  op.exact a b = 0 ∨ fmt.finiteNormalRange (op.exact a b)

/-- Priest faithfulness for one literal finite operation, stated with the
source's actual adjacent-neighbour semantics.  An exact zero is returned
exactly; every nonzero result carries `sourceRoundToEvenEvidence`, which says
that it is the exact value or one of the two adjacent normalized
floating-point neighbours enclosing that value.

Unlike a universal assertion about a bounded selector, this predicate is
meaningful on a real finite execution and cannot be discharged through the
saturation branch. -/
def PriestSourceFaithfulAt
    (fmt : FloatingPointFormat) (op : BasicOp) (a b : ℝ) : Prop :=
  let exact := op.exact a b
  let rounded := fmt.finiteRoundToEvenOp op a b
  (exact = 0 ∧ rounded = exact) ∨
    fmt.sourceRoundToEvenEvidence exact rounded

/-- Source-faithful addition/subtraction throughout the no-exception part of
the literal bounded format.  Multiplication and division are irrelevant to
Algorithm 4.3 and are intentionally not included. -/
def PriestSourceFaithful (fmt : FloatingPointFormat) : Prop :=
  ∀ ⦃op : BasicOp⦄, (op = BasicOp.add ∨ op = BasicOp.sub) →
    ∀ ⦃a b : ℝ⦄, priestSourceOperationRange fmt op a b →
      PriestSourceFaithfulAt fmt op a b

/-- Concrete finite round-to-even realizes Priest's adjacent-neighbour
faithfulness on every zero-or-normal addition/subtraction.  Thus
faithfulness is a proved semantic fact of the literal executor in scope, not
an impossible global hypothesis on a saturating bounded selector. -/
theorem priestFinite_sourceFaithful
    (fmt : FloatingPointFormat) :
    PriestSourceFaithful fmt := by
  intro op hop a b hrange
  rcases hrange with hzero | hnormal
  · left
    refine ⟨hzero, ?_⟩
    change fmt.finiteRoundToEven (op.exact a b) = op.exact a b
    exact fmt.finiteRoundToEven_eq_self_of_finiteSystem
      (by simpa [hzero] using fmt.finiteSystem_zero)
  · right
    change fmt.sourceRoundToEvenEvidence (op.exact a b)
      (fmt.finiteRoundToEven (op.exact a b))
    exact fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hnormal

/-- The exact source-side input hypotheses for Priest's proposition.  The
array has `n+1` entries in the repository indexing convention, hence the size
cap is `(n+1) ≤ β^(t-3)`. -/
structure PriestSourceInputAssumptions
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Prop where
  finite : ∀ i, fmt.finiteSystem (x i)
  sorted : priestSortedByDecreasingAbs x
  nonzero : ∀ i, x i ≠ 0
  sizeCap : n + 1 ≤ fmt.beta ^ (fmt.t - 3)

/-- The small-first branch of Priest's Lemma 1, proved directly from the
literal A1 and S4 assumptions.  No exact-step or target-scale error premise is
used: S4 makes the inner subtraction exact, A1 makes the true sum roundoff
representable, and the finite selector is exact on representable values. -/
theorem priestSource_smallFirst_pair_exact
    (fmt : FloatingPointFormat) (hA1 : PriestSourceA1 fmt)
    (hS4 : PriestSourceS4 fmt) {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |a| ≤ |b|) (hmul : priestSourceUlpMultiple fmt a b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    let e := fmt.finiteRoundToEvenOp BasicOp.sub b
      (fmt.finiteRoundToEvenOp BasicOp.sub s a)
    s + e = a + b := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hinner : fmt.finiteRoundToEvenOp BasicOp.sub s a = s - a := by
    simpa [s] using hS4 ha hb hab hmul
  have herr : fmt.finiteSystem ((a + b) - s) := by
    simpa [s] using hA1 ha hb
  have hres : b - (s - a) = (a + b) - s := by ring
  have houter :
      fmt.finiteRoundToEvenOp BasicOp.sub b (s - a) = b - (s - a) := by
    have hfin : fmt.finiteSystem (b - (s - a)) := by
      rw [hres]
      exact herr
    simpa [BasicOp.exact] using
      fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := b) (y := s - a) hfin
  dsimp
  change s + fmt.finiteRoundToEvenOp BasicOp.sub b
      (fmt.finiteRoundToEvenOp BasicOp.sub s a) = a + b
  rw [hinner, houter]
  ring

/-! ## Priest's three exact local correction pairs

The thesis proof does not make the rounded combine `z = fl(u+υ)` exact.  It
proves only the three surrounding sum-and-roundoff pairs exact.  The following
finite-format lemma realizes Priest's displayed subtraction orientation
`b - (s-a)` from the same representability certificate used by FastTwoSum.
-/

/-- Priest's `s = fl(a+b); e = fl(b-fl(s-a))` orientation is exact whenever
the finite FastTwoSum representability certificate holds. -/
theorem priestFinite_twoSum_exact_of_certificate
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hcert : FastTwoSumFiniteCertificate fmt a b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    let e := fmt.finiteRoundToEvenOp BasicOp.sub b
      (fmt.finiteRoundToEvenOp BasicOp.sub s a)
    s + e = a + b := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hsa : fmt.finiteSystem (s - a) := by
    have hneg : -(a - s) = s - a := by ring
    rw [← hneg]
    exact fmt.finiteSystem_neg (by simpa [s] using hcert.finite_a_sub_s)
  have hinner : fmt.finiteRoundToEvenOp BasicOp.sub s a = s - a := by
    simpa [BasicOp.exact] using
      fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := s) (y := a) hsa
  have herror : fmt.finiteSystem (b - (s - a)) := by
    have hrw : b - (s - a) = (a + b) - s := by ring
    rw [hrw]
    simpa [s] using hcert.finite_error
  have houter :
      fmt.finiteRoundToEvenOp BasicOp.sub b (s - a) = b - (s - a) := by
    simpa [BasicOp.exact] using
      fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := b) (y := s - a) herror
  dsimp
  change s + fmt.finiteRoundToEvenOp BasicOp.sub b
      (fmt.finiteRoundToEvenOp BasicOp.sub s a) = a + b
  rw [hinner, houter]
  ring

/-- Priest's full Lemma 1 for concrete finite binary round-to-even arithmetic.
The usual large-first branch is the finite FastTwoSum theorem; the small-first
branch is exactly A1+S4 above.  A2 is recorded separately because it is used by
Priest to establish the loop's ulp/order invariants, not by this final case
split once the magnitude order is known. -/
theorem priestSource_pair_exact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (hA1 : PriestSourceA1 fmt) (hS4 : PriestSourceS4 fmt)
    {a b : ℝ} (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hrange : fmt.finiteNormalRange (a + b))
    (hsmallMul : |a| ≤ |b| → priestSourceUlpMultiple fmt a b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    let e := fmt.finiteRoundToEvenOp BasicOp.sub b
      (fmt.finiteRoundToEvenOp BasicOp.sub s a)
    s + e = a + b := by
  by_cases hab : |a| ≤ |b|
  · exact priestSource_smallFirst_pair_exact fmt hA1 hS4 ha hb hab
      (hsmallMul hab)
  · have hba : |b| < |a| := lt_of_not_ge hab
    exact priestFinite_twoSum_exact_of_certificate fmt a b
      (FastTwoSumFiniteCertificate.of_base2_abs_gt
        fmt hbeta ht ha hb hba hrange)

/-- The three source-local representability certificates used in one Priest
step.  They concern `(c,x)`, `(s,y)`, and `(t,z)`; no certificate is imposed on
the rounded combine `(u,υ)`. -/
structure PriestFiniteThreePairCertificates
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState) : Prop where
  first : FastTwoSumFiniteCertificate fmt state.c x
  second : FastTwoSumFiniteCertificate fmt state.s
    (priestFinite_stepTrace fmt x state).y
  third : FastTwoSumFiniteCertificate fmt
    (priestFinite_stepTrace fmt x state).t
    (priestFinite_stepTrace fmt x state).z

/-- Source-faithful per-step expansion facts: the first, second, and final
correction pairs are exact, while `z = fl(u+υ)` remains rounded. -/
structure PriestFiniteExpansionStep
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState) : Prop where
  addOne :
    (priestFinite_stepTrace fmt x state).y +
      (priestFinite_stepTrace fmt x state).u = state.c + x
  addThree :
    (priestFinite_stepTrace fmt x state).t +
      (priestFinite_stepTrace fmt x state).upsilon =
        (priestFinite_stepTrace fmt x state).y + state.s
  addSix :
    (priestFinite_stepTrace fmt x state).s +
      (priestFinite_stepTrace fmt x state).c =
        (priestFinite_stepTrace fmt x state).t +
          (priestFinite_stepTrace fmt x state).z

/-- The three finite representability certificates produce exactly the local
expansion facts proved in Priest's §4.1 argument. -/
theorem priestFinite_expansionStep_of_threePairCertificates
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState)
    (h : PriestFiniteThreePairCertificates fmt x state) :
    PriestFiniteExpansionStep fmt x state := by
  let T := priestFinite_stepTrace fmt x state
  have hfirst := priestFinite_twoSum_exact_of_certificate
    fmt state.c x h.first
  have hsecond := priestFinite_twoSum_exact_of_certificate
    fmt state.s T.y h.second
  have hthird := priestFinite_twoSum_exact_of_certificate
    fmt T.t T.z h.third
  have haddComm (a b : ℝ) :
      fmt.finiteRoundToEvenOp BasicOp.add a b =
        fmt.finiteRoundToEvenOp BasicOp.add b a := by
    simp [FloatingPointFormat.finiteRoundToEvenOp,
      BasicOp.exact, add_comm]
  refine ⟨?_, ?_, ?_⟩
  · simpa [T, priestFinite_stepTrace] using hfirst
  · have hsecond' :
        fmt.finiteRoundToEvenOp BasicOp.add T.y state.s +
            fmt.finiteRoundToEvenOp BasicOp.sub T.y
              (fmt.finiteRoundToEvenOp BasicOp.sub
                (fmt.finiteRoundToEvenOp BasicOp.add T.y state.s)
                state.s) =
          state.s + T.y := by
      simpa [haddComm state.s T.y] using hsecond
    simpa [T, priestFinite_stepTrace, add_comm] using hsecond'
  · simpa [T, priestFinite_stepTrace] using hthird

/-- Algebraic local-defect identity matching Priest's proof: once the three
correction pairs are exact, the entire step defect is precisely the rounding
defect in `z = fl(u+υ)`. -/
theorem priestFinite_stepDefect_eq_combineDefect
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState)
    (hops : PriestFiniteStepCondition fmt x state)
    (hexp : PriestFiniteExpansionStep fmt x state) :
    priestDB_stepDefect (kahanFF_model fmt) x state =
      (priestFinite_stepTrace fmt x state).z -
        (priestFinite_stepTrace fmt x state).u -
        (priestFinite_stepTrace fmt x state).upsilon := by
  have htrace := priestFinite_stepTrace_eq_priestStepTrace
    fmt x state hops
  unfold priestDB_stepDefect priestStep
  rw [← htrace]
  dsimp [PriestStepTrace.nextState]
  linarith [hexp.addOne, hexp.addThree, hexp.addSix]

/-- Consequently one source-faithful step defect has only the ordinary rounded
combine error, with no spurious first-order defects from the correction pairs. -/
theorem priestFinite_stepDefect_abs_le_combine
    (fmt : FloatingPointFormat) (x : ℝ) (state : PriestState)
    (hops : PriestFiniteStepCondition fmt x state)
    (hexp : PriestFiniteExpansionStep fmt x state) :
    |priestDB_stepDefect (kahanFF_model fmt) x state| ≤
      fmt.unitRoundoff *
        |(priestFinite_stepTrace fmt x state).u +
          (priestFinite_stepTrace fmt x state).upsilon| := by
  rw [priestFinite_stepDefect_eq_combineDefect fmt x state hops hexp]
  have hz : (priestFinite_stepTrace fmt x state).z =
      (kahanFF_model fmt).fl_add
        (priestFinite_stepTrace fmt x state).u
        (priestFinite_stepTrace fmt x state).upsilon := by
    change fmt.finiteRoundToEvenOp BasicOp.add
        (priestFinite_stepTrace fmt x state).u
        (priestFinite_stepTrace fmt x state).upsilon = _
    exact priestFinite_add_agrees_safe fmt hops.z
  rw [hz]
  simpa [sub_sub] using priestDB_add_defect_bound
    (kahanFF_model fmt)
    (priestFinite_stepTrace fmt x state).u
    (priestFinite_stepTrace fmt x state).upsilon

end NumStability
