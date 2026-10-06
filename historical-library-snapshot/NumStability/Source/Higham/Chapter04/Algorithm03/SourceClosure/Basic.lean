import NumStability.Algorithms.Summation.Compensated.Priest.FiniteFormat
import NumStability.Source.Higham.Chapter04.Algorithm03.Priest.SourceAssumptions
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter04 Algorithm03 SourceClosure Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- The source arithmetic package used by Priest's proof of doubly compensated
summation.  `A2` and faithfulness are included because they are used to
establish the loop-order and ulp invariants; once those invariants have been
made explicit, the local correction-pair proof itself uses `A1` and `S4`. -/
structure PriestSourceArithmeticAssumptions
    (fmt : FloatingPointFormat) : Prop where
  baseTwo : fmt.beta = 2
  precision : 1 < fmt.t
  A1 : PriestSourceA1 fmt
  A2 : PriestSourceA2 fmt
  S4 : PriestSourceS4 fmt
  faithful : PriestSourceFaithful fmt

/-- Primitive source facts for one sum-and-error pair.  These are finite-format
membership, no-exception, and ulp-lattice facts, rather than an assertion that
the pair is exact. -/
structure PriestSourcePairLoopFacts
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop where
  finiteLeft : fmt.finiteSystem a
  finiteRight : fmt.finiteSystem b
  normalSum : fmt.finiteNormalRange (a + b)
  smallFirstUlp : |a| ≤ |b| → priestSourceUlpMultiple fmt a b

/-- The three primitive pair facts maintained at one literal Priest step.
They concern `(c,x)`, `(s,y)`, and `(t,z)`; the rounded combine `(u,υ)` is
intentionally absent. -/
structure PriestSourceStepLoopFacts
    (fmt : FloatingPointFormat) (xk : ℝ) (state : PriestState) : Prop where
  first : PriestSourcePairLoopFacts fmt state.c xk
  second : PriestSourcePairLoopFacts fmt state.s
    (priestFinite_stepTrace fmt xk state).y
  third : PriestSourcePairLoopFacts fmt
    (priestFinite_stepTrace fmt xk state).t
    (priestFinite_stepTrace fmt xk state).z

/-- Priest's source assumptions turn the primitive three-pair loop facts into
the exact local expansion facts.  The combine remains rounded. -/
theorem priestSource_expansionStep_of_stepLoopFacts
    (fmt : FloatingPointFormat) (hsrc : PriestSourceArithmeticAssumptions fmt)
    (xk : ℝ) (state : PriestState)
    (h : PriestSourceStepLoopFacts fmt xk state) :
    PriestFiniteExpansionStep fmt xk state := by
  let T := priestFinite_stepTrace fmt xk state
  have hfirst := priestSource_pair_exact fmt hsrc.baseTwo hsrc.precision
    hsrc.A1 hsrc.S4 h.first.finiteLeft h.first.finiteRight
    h.first.normalSum h.first.smallFirstUlp
  have hsecond := priestSource_pair_exact fmt hsrc.baseTwo hsrc.precision
    hsrc.A1 hsrc.S4 h.second.finiteLeft h.second.finiteRight
    h.second.normalSum h.second.smallFirstUlp
  have hthird := priestSource_pair_exact fmt hsrc.baseTwo hsrc.precision
    hsrc.A1 hsrc.S4 h.third.finiteLeft h.third.finiteRight
    h.third.normalSum h.third.smallFirstUlp
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
      simpa [T, haddComm state.s T.y] using hsecond
    simpa [T, priestFinite_stepTrace, add_comm] using hsecond'
  · simpa [T, priestFinite_stepTrace] using hthird

/-- Sum of the exact magnitudes presented to the one deliberately rounded
combine in every tail iteration. -/
noncomputable def priestSourceCombineInputMagnitude
    (fmt : FloatingPointFormat) {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j : Fin n,
    |(priestFinite_stepTrace fmt
        (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (priestPrefixState (kahanFF_model fmt) x j.val
          (Nat.le_of_lt j.isLt))).u +
      (priestFinite_stepTrace fmt
        (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (priestPrefixState (kahanFF_model fmt) x j.val
          (Nat.le_of_lt j.isLt))).upsilon|

/-- Explicit, non-target loop invariants for the finite Priest executor.

* `operations` keeps all ten primitive operations of every step in the region
  where the literal executor agrees with the analytic safe completion;
* `stepPairs` supplies only finite/normal/ulp facts for the three correction
  pairs;
* `retainedCorrection` and `combineInputs` are the two independent magnitude
  estimates used in the source accumulation.  They mention neither the
  per-step defect nor `priestDB_defectBudget`.
-/
structure PriestSourceOperationalLoopInvariants
    (fmt : FloatingPointFormat) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Prop where
  operations : PriestFiniteAllOperations fmt x
  stepPairs : ∀ j : Fin n,
    PriestSourceStepLoopFacts fmt
      (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      (priestPrefixState (kahanFF_model fmt) x j.val
        (Nat.le_of_lt j.isLt))
  retainedCorrection :
    |(fl_priestState (kahanFF_model fmt) x).c| ≤
      fmt.unitRoundoff * |∑ i, x i|
  combineInputs :
    priestSourceCombineInputMagnitude fmt x ≤ |∑ i, x i|

/-- Explicit conditional executor closure for Priest's Algorithm 4.3.

The source input assumptions are displayed, but are not claimed to imply the
operational loop invariant: proving that implication is precisely the global
faithful-rounding induction omitted by Higham's phrase ``certain reasonable
assumptions''.  Given the non-target invariant, `A1`/`S4` make the three
correction pairs exact, ordinary rounding bounds the combine defect, and the
two magnitude estimates yield `priestDB_defectBudget`. -/
theorem priestFinite_defectBudget_of_sourceOperationalLoopInvariants
    (fmt : FloatingPointFormat) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hsrc : PriestSourceArithmeticAssumptions fmt)
    (_hinput : PriestSourceInputAssumptions fmt x)
    (hloop : PriestSourceOperationalLoopInvariants fmt x) :
    priestDB_defectBudget (kahanFF_model fmt) x := by
  have hstep : ∀ j : Fin n,
      |priestDB_stepDefect (kahanFF_model fmt)
          (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
          (priestPrefixState (kahanFF_model fmt) x j.val
            (Nat.le_of_lt j.isLt))| ≤
        fmt.unitRoundoff *
          |(priestFinite_stepTrace fmt
              (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (priestPrefixState (kahanFF_model fmt) x j.val
                (Nat.le_of_lt j.isLt))).u +
            (priestFinite_stepTrace fmt
              (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (priestPrefixState (kahanFF_model fmt) x j.val
                (Nat.le_of_lt j.isLt))).upsilon| := by
    intro j
    have hpfx := priestFinite_prefixState_eq_priestPrefixState
      fmt x hloop.operations j.val (Nat.le_of_lt j.isLt)
    have hops := hloop.operations j
    rw [hpfx] at hops
    exact priestFinite_stepDefect_abs_le_combine fmt _ _ hops
      (priestSource_expansionStep_of_stepLoopFacts
        fmt hsrc _ _ (hloop.stepPairs j))
  unfold priestDB_defectBudget
  have hsum :
      (∑ j : Fin n,
          |priestDB_stepDefect (kahanFF_model fmt)
            (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
            (priestPrefixState (kahanFF_model fmt) x j.val
              (Nat.le_of_lt j.isLt))|) ≤
        fmt.unitRoundoff * priestSourceCombineInputMagnitude fmt x := by
    calc
      (∑ j : Fin n,
          |priestDB_stepDefect (kahanFF_model fmt)
            (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
            (priestPrefixState (kahanFF_model fmt) x j.val
              (Nat.le_of_lt j.isLt))|) ≤
          ∑ j : Fin n, fmt.unitRoundoff *
            |(priestFinite_stepTrace fmt
                (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                (priestPrefixState (kahanFF_model fmt) x j.val
                  (Nat.le_of_lt j.isLt))).u +
              (priestFinite_stepTrace fmt
                (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                (priestPrefixState (kahanFF_model fmt) x j.val
                  (Nat.le_of_lt j.isLt))).upsilon| := by
            exact Finset.sum_le_sum (fun j _ => hstep j)
      _ = fmt.unitRoundoff * priestSourceCombineInputMagnitude fmt x := by
        rw [priestSourceCombineInputMagnitude, Finset.mul_sum]
  calc
    |(fl_priestState (kahanFF_model fmt) x).c| +
          ∑ j : Fin n,
            |priestDB_stepDefect (kahanFF_model fmt)
              (x ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              (priestPrefixState (kahanFF_model fmt) x j.val
                (Nat.le_of_lt j.isLt))| ≤
        |(fl_priestState (kahanFF_model fmt) x).c| +
          fmt.unitRoundoff * priestSourceCombineInputMagnitude fmt x := by
            exact add_le_add_right hsum _
    _ ≤ fmt.unitRoundoff * |∑ i, x i| +
          fmt.unitRoundoff * |∑ i, x i| := by
      exact add_le_add hloop.retainedCorrection
        (mul_le_mul_of_nonneg_left hloop.combineInputs
          fmt.unitRoundoff_nonneg)
    _ = 2 * (kahanFF_model fmt).u * |∑ i, x i| := by
      change fmt.unitRoundoff * |∑ i, x i| +
          fmt.unitRoundoff * |∑ i, x i| =
        2 * fmt.unitRoundoff * |∑ i, x i|
      ring

/-- Returned-value form of the conditional finite-executor theorem. -/
theorem priestFinite_doublyCompensated_accuracy_of_sourceOperationalLoopInvariants
    (fmt : FloatingPointFormat) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hsrc : PriestSourceArithmeticAssumptions fmt)
    (hinput : PriestSourceInputAssumptions fmt x)
    (hloop : PriestSourceOperationalLoopInvariants fmt x) :
    |(∑ i, x i) - priestFinite_sum fmt x| ≤
      2 * fmt.unitRoundoff * |∑ i, x i| := by
  rw [priestFinite_sum_eq_fl_priestSum fmt x hloop.operations]
  exact priestDB_doublyCompensated_accuracy (kahanFF_model fmt) x
    (priestFinite_defectBudget_of_sourceOperationalLoopInvariants
      fmt x hsrc hinput hloop)

end NumStability
