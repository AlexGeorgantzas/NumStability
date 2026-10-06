import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.Compensated.Neumaier.ExactResidual
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.FloatingPoint.Model








namespace NumStability

open scoped BigOperators

/-!
# The magnitude-adaptive separately accumulated correction (Higham (4.10))

Higham's prose before (4.10) refers to the Kielbasiński--Neumaier variant:
the main recursive sum is unchanged, but each local rounding correction is
stored, the corrections are recursively summed, and that global correction is
added once at the end.  The error-free local correction must be evaluated in
the magnitude order required by (4.7).  This file makes that branch explicit
and connects the genuine finite binary round-to-even trace to the printed
`2u + n²u²` backward-error radius.
-/

/-! ## Canonical exact residuals of recursive summation -/
















































































































































































































































































































































































































































/-! ## The exact-residual separately accumulated executor -/










































































































/-! ## Magnitude-adaptive finite-format producer -/

/-- Source/no-exception condition for one main addition of the adaptive
Neumaier trace.  Both operands are stored finite values and the exact sum is
either in finite normal range or already returned exactly. -/
def neumaierFF_stepCondition
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop :=
  fmt.finiteSystem a ∧ fmt.finiteSystem b ∧
    (fmt.finiteNormalRange (a + b) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b)

/-- On the source/no-exception region, the safe-completion addition is
commutative because both operand orders are the same genuine finite
round-to-even addition. -/
theorem kahanFF_fl_add_comm_of_neumaierCondition
    (fmt : FloatingPointFormat) {a b : ℝ}
    (h : neumaierFF_stepCondition fmt a b) :
    (kahanFF_model fmt).fl_add a b =
      (kahanFF_model fmt).fl_add b a := by
  rcases h with ⟨ha, hb, hmain⟩
  have hmain' : fmt.finiteNormalRange (b + a) ∨
      fmt.finiteRoundToEvenOp BasicOp.add b a = b + a := by
    rcases hmain with hr | he
    · left
      simpa [add_comm] using hr
    · right
      simpa [FloatingPointFormat.finiteRoundToEvenOp,
        BasicOp.exact, add_comm] using he
  rw [kahanFF_fl_add_eq_finiteRoundToEvenOp fmt hb hmain,
    kahanFF_fl_add_eq_finiteRoundToEvenOp fmt ha hmain']
  simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact, add_comm]

/-- One literal magnitude-adaptive step: the main addition keeps the source
order; the correction is evaluated with the larger-magnitude operand first. -/
structure NeumaierFFStepTrace where
  temp : ℝ
  s : ℝ
  e : ℝ

noncomputable def neumaierFF_stepTrace
    (fmt : FloatingPointFormat) (a b : ℝ) : NeumaierFFStepTrace :=
  let fp := kahanFF_model fmt
  let s := fp.fl_add a b
  let e := if |b| ≤ |a| then
      fp.fl_add (fp.fl_sub a s) b
    else
      fp.fl_add (fp.fl_sub b s) a
  { temp := a, s := s, e := e }

/-- The adaptive branch produces the (4.7) order instead of assuming it. -/
theorem neumaierFF_step_exact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (a b : ℝ) (hstep : neumaierFF_stepCondition fmt a b) :
    (neumaierFF_stepTrace fmt a b).s +
        (neumaierFF_stepTrace fmt a b).e = a + b := by
  rcases hstep with ⟨ha, hb, hmain⟩
  by_cases hab : |b| ≤ |a|
  · have hcond : kahanFF_stepCondition fmt a b := by
      refine ⟨hb, ?_⟩
      rcases hmain with hr | he
      · exact Or.inl ⟨ha, hab, hr⟩
      · exact Or.inr he
    have hexact := kahanFF_step_exact fmt hbeta ht a b hcond
    simpa [neumaierFF_stepTrace, hab] using hexact.symm
  · have hba : |a| ≤ |b| := le_of_lt (lt_of_not_ge hab)
    have hmain' : fmt.finiteNormalRange (b + a) ∨
        fmt.finiteRoundToEvenOp BasicOp.add b a = b + a := by
      rcases hmain with hr | he
      · left
        simpa [add_comm] using hr
      · right
        simpa [FloatingPointFormat.finiteRoundToEvenOp,
          BasicOp.exact, add_comm] using he
    have hcond : kahanFF_stepCondition fmt b a := by
      refine ⟨ha, ?_⟩
      rcases hmain' with hr | he
      · exact Or.inl ⟨hb, hba, hr⟩
      · exact Or.inr he
    have hexact := kahanFF_step_exact fmt hbeta ht b a hcond
    have hcomm : (kahanFF_model fmt).fl_add a b =
        (kahanFF_model fmt).fl_add b a :=
      kahanFF_fl_add_comm_of_neumaierCondition fmt ⟨ha, hb, hmain⟩
    simpa [neumaierFF_stepTrace, hab, hcomm, add_comm] using hexact.symm

/-- Main sum before index `i` of the finite adaptive trace. -/
noncomputable def neumaierFF_prefix
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  fl_recursiveSum (kahanFF_model fmt) i.val
    (fun j : Fin i.val => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)

/-- Stored adaptive correction at each source index. -/
noncomputable def neumaierFF_corrections
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) : Fin n → ℝ := fun i =>
  (neumaierFF_stepTrace fmt (neumaierFF_prefix fmt v i) (v i)).e

/-- Literal finite-format separately accumulated Neumaier executor. -/
noncomputable def neumaierFF_sum
    (fmt : FloatingPointFormat) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (kahanFF_model fmt).fl_add
    (fl_recursiveSum (kahanFF_model fmt) n v)
    (fl_recursiveSum (kahanFF_model fmt) n
      (neumaierFF_corrections fmt v))

/-- Each produced adaptive correction is the canonical exact local residual. -/
theorem neumaierFF_correction_eq_recursiveSumLocalCorrection
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hstep : neumaierFF_stepCondition fmt (neumaierFF_prefix fmt v i) (v i)) :
    neumaierFF_corrections fmt v i =
      recursiveSumLocalCorrection (kahanFF_model fmt) v i := by
  let prev := fl_recursiveSum (kahanFF_model fmt) i.val
    (fun j : Fin i.val => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)
  have hexact := neumaierFF_step_exact fmt hbeta ht
    (neumaierFF_prefix fmt v i) (v i) hstep
  have hexact' :
      (kahanFF_model fmt).fl_add prev (v i) +
          (neumaierFF_stepTrace fmt prev (v i)).e = prev + v i := by
    simpa [neumaierFF_prefix, prev, neumaierFF_stepTrace] using hexact
  change (neumaierFF_stepTrace fmt prev (v i)).e =
    (prev + v i) - (kahanFF_model fmt).fl_add prev (v i)
  linarith

/-- The literal adaptive trace equals the canonical exact-residual executor. -/
theorem neumaierFF_sum_eq_recursiveResidualCorrectedSum
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hstep : ∀ i : Fin n,
      neumaierFF_stepCondition fmt (neumaierFF_prefix fmt v i) (v i)) :
    neumaierFF_sum fmt n v =
      fl_recursiveResidualCorrectedSum (kahanFF_model fmt) n v := by
  have hcorr : neumaierFF_corrections fmt v =
      recursiveSumLocalCorrection (kahanFF_model fmt) v := by
    funext i
    exact neumaierFF_correction_eq_recursiveSumLocalCorrection
      fmt hbeta ht v i (hstep i)
  simp [neumaierFF_sum, fl_recursiveResidualCorrectedSum, hcorr]























/-! ## Genuine finite-operation executor

The preceding safe-completion executor is convenient for error analysis.  The
definitions below contain only `finiteRoundToEvenOp` operations.  We prove a
trace equality, under explicit no-exception conditions, so the analytic result
above applies to the literal finite-format program rather than merely to its
completion.
-/












































































































































































































































































end NumStability
