import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.Compensated.Neumaier.AdaptiveFiniteFormat
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
































































































































































/-! ## Genuine finite-operation executor

The preceding safe-completion executor is convenient for error analysis.  The
definitions below contain only `finiteRoundToEvenOp` operations.  We prove a
trace equality, under explicit no-exception conditions, so the analytic result
above applies to the literal finite-format program rather than merely to its
completion.
-/

/-- One genuine finite-operation magnitude-adaptive Neumaier step. -/
structure NeumaierFiniteStepTrace where
  temp : ℝ
  s : ℝ
  e : ℝ

noncomputable def neumaierFinite_stepTrace
    (fmt : FloatingPointFormat) (a b : ℝ) : NeumaierFiniteStepTrace :=
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  let e := if |b| ≤ |a| then
      (finiteCorrectionFormulaTrace fmt a b).e
    else
      (finiteCorrectionFormulaTrace fmt b a).e
  { temp := a, s := s, e := e }

/-- The literal finite-operation adaptive step recovers its exact local
residual.  The magnitude branch supplies the order required by FastTwoSum. -/
theorem neumaierFinite_step_exact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (a b : ℝ) (hstep : neumaierFF_stepCondition fmt a b) :
    (neumaierFinite_stepTrace fmt a b).s +
        (neumaierFinite_stepTrace fmt a b).e = a + b := by
  rcases hstep with ⟨ha, hb, hmain⟩
  by_cases hab : |b| ≤ |a|
  · have hcert : FastTwoSumFiniteCertificate fmt a b := by
      rcases hmain with hr | he
      · exact FastTwoSumFiniteCertificate.of_base2_abs_le
          fmt hbeta ht ha hb hab hr
      · exact FastTwoSumFiniteCertificate.of_exact_add fmt a b hb he
    have hexact :=
      finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate
        fmt a b hcert
    simpa [neumaierFinite_stepTrace, hab,
      CorrectionFormulaTrace.exact] using hexact.symm
  · have hba : |a| ≤ |b| := le_of_lt (lt_of_not_ge hab)
    have hmain' : fmt.finiteNormalRange (b + a) ∨
        fmt.finiteRoundToEvenOp BasicOp.add b a = b + a := by
      rcases hmain with hr | he
      · exact Or.inl (by simpa [add_comm] using hr)
      · exact Or.inr (by
          simpa [FloatingPointFormat.finiteRoundToEvenOp,
            BasicOp.exact, add_comm] using he)
    have hcert : FastTwoSumFiniteCertificate fmt b a := by
      rcases hmain' with hr | he
      · exact FastTwoSumFiniteCertificate.of_base2_abs_le
          fmt hbeta ht hb ha hba hr
      · exact FastTwoSumFiniteCertificate.of_exact_add fmt b a ha he
    have hexact :=
      finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate
        fmt b a hcert
    have hscomm :
        fmt.finiteRoundToEvenOp BasicOp.add a b =
          fmt.finiteRoundToEvenOp BasicOp.add b a := by
      simp [FloatingPointFormat.finiteRoundToEvenOp,
        BasicOp.exact, add_comm]
    have hexact' :
        fmt.finiteRoundToEvenOp BasicOp.add b a +
            (finiteCorrectionFormulaTrace fmt b a).e = b + a := by
      simpa [CorrectionFormulaTrace.exact] using hexact.symm
    simp only [neumaierFinite_stepTrace, hab, if_false]
    calc
      _ = fmt.finiteRoundToEvenOp BasicOp.add b a +
          (finiteCorrectionFormulaTrace fmt b a).e := by rw [hscomm]
      _ = b + a := hexact'
      _ = a + b := add_comm b a

/-- Literal left-to-right recursive summation using only the finite format's
round-to-even addition. -/
noncomputable def neumaierFinite_recursiveSum
    (fmt : FloatingPointFormat) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n
    (fun acc i => fmt.finiteRoundToEvenOp BasicOp.add acc (v i)) 0

/-- Under the explicit source/no-exception condition at every main addition,
the genuine finite recursive sum agrees with the analytic safe completion. -/
theorem neumaierFinite_recursiveSum_eq_fl_recursiveSum
    (fmt : FloatingPointFormat) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      (∀ i : Fin n,
        neumaierFF_stepCondition fmt (neumaierFF_prefix fmt v i) (v i)) →
      neumaierFinite_recursiveSum fmt n v =
        fl_recursiveSum (kahanFF_model fmt) n v
  | 0, _v, _hstep => by
      simp [neumaierFinite_recursiveSum, fl_recursiveSum]
  | n + 1, v, hstep => by
      let old : Fin n → ℝ := fun i => v i.castSucc
      have hstepOld : ∀ i : Fin n,
          neumaierFF_stepCondition fmt
            (neumaierFF_prefix fmt old i) (old i) := by
        intro i
        simpa [neumaierFF_prefix, old] using hstep i.castSucc
      have ih := neumaierFinite_recursiveSum_eq_fl_recursiveSum
        fmt n old hstepOld
      have hactual :
          neumaierFinite_recursiveSum fmt (n + 1) v =
            fmt.finiteRoundToEvenOp BasicOp.add
              (neumaierFinite_recursiveSum fmt n old) (v (Fin.last n)) := by
        exact Fin.foldl_succ_last _ _
      have hsafe :
          fl_recursiveSum (kahanFF_model fmt) (n + 1) v =
            (kahanFF_model fmt).fl_add
              (fl_recursiveSum (kahanFF_model fmt) n old)
              (v (Fin.last n)) := by
        exact Fin.foldl_succ_last _ _
      have hlast := hstep (Fin.last n)
      have hprefix :
          neumaierFF_prefix fmt v (Fin.last n) =
            fl_recursiveSum (kahanFF_model fmt) n old := by
        rfl
      have hbridge :
          (kahanFF_model fmt).fl_add
              (fl_recursiveSum (kahanFF_model fmt) n old)
              (v (Fin.last n)) =
            fmt.finiteRoundToEvenOp BasicOp.add
              (fl_recursiveSum (kahanFF_model fmt) n old)
              (v (Fin.last n)) := by
        apply kahanFF_fl_add_eq_finiteRoundToEvenOp
        · exact hlast.2.1
        · simpa [hprefix] using hlast.2.2
      rw [hactual, hsafe, ih]
      exact hbridge.symm

/-- Genuine finite recursive-sum value before source index `i`. -/
noncomputable def neumaierFinite_prefix
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  neumaierFinite_recursiveSum fmt i.val
    (fun j : Fin i.val => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)

/-- Every genuine finite main prefix agrees with the corresponding
safe-completion prefix. -/
theorem neumaierFinite_prefix_eq_neumaierFF_prefix
    (fmt : FloatingPointFormat) {n : ℕ} (v : Fin n → ℝ)
    (hstep : ∀ i : Fin n,
      neumaierFF_stepCondition fmt (neumaierFF_prefix fmt v i) (v i))
    (i : Fin n) :
    neumaierFinite_prefix fmt v i = neumaierFF_prefix fmt v i := by
  let pref : Fin i.val → ℝ := fun j =>
    v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  have hpref : ∀ j : Fin i.val,
      neumaierFF_stepCondition fmt
        (neumaierFF_prefix fmt pref j) (pref j) := by
    intro j
    let emb : Fin n := ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
    simpa [neumaierFF_prefix, pref, emb] using hstep emb
  simpa [neumaierFinite_prefix, neumaierFF_prefix, pref] using
    neumaierFinite_recursiveSum_eq_fl_recursiveSum
      fmt i.val pref hpref

/-- Correction emitted by each genuine finite-operation adaptive step. -/
noncomputable def neumaierFinite_corrections
    (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) : Fin n → ℝ := fun i =>
  (neumaierFinite_stepTrace fmt
    (neumaierFinite_prefix fmt v i) (v i)).e

/-- The finite-operation correction list agrees pointwise with the analytic
safe-completion correction list. -/
theorem neumaierFinite_correction_eq_neumaierFF_correction
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {n : ℕ} (v : Fin n → ℝ)
    (hstep : ∀ i : Fin n,
      neumaierFF_stepCondition fmt (neumaierFF_prefix fmt v i) (v i))
    (i : Fin n) :
    neumaierFinite_corrections fmt v i =
      neumaierFF_corrections fmt v i := by
  have hprefix :=
    neumaierFinite_prefix_eq_neumaierFF_prefix fmt v hstep i
  let a := neumaierFF_prefix fmt v i
  have hlocal := hstep i
  have hactual := neumaierFinite_step_exact fmt hbeta ht a (v i) hlocal
  have hsafe := neumaierFF_step_exact fmt hbeta ht a (v i) hlocal
  have hmain :
      (kahanFF_model fmt).fl_add a (v i) =
        fmt.finiteRoundToEvenOp BasicOp.add a (v i) :=
    kahanFF_fl_add_eq_finiteRoundToEvenOp fmt hlocal.2.1 hlocal.2.2
  have hs :
      (neumaierFinite_stepTrace fmt a (v i)).s =
        (neumaierFF_stepTrace fmt a (v i)).s := by
    simpa [neumaierFinite_stepTrace, neumaierFF_stepTrace] using hmain.symm
  change (neumaierFinite_stepTrace fmt
      (neumaierFinite_prefix fmt v i) (v i)).e =
    (neumaierFF_stepTrace fmt a (v i)).e
  rw [hprefix]
  change (neumaierFinite_stepTrace fmt a (v i)).e =
    (neumaierFF_stepTrace fmt a (v i)).e
  linarith

/-- Full literal Neumaier program: a genuine finite recursive main sum, a
genuine finite recursive sum of the emitted corrections, and one genuine
finite final addition. -/
noncomputable def neumaierFinite_sum
    (fmt : FloatingPointFormat) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.add
    (neumaierFinite_recursiveSum fmt n v)
    (neumaierFinite_recursiveSum fmt n
      (neumaierFinite_corrections fmt v))

/-- Under no-exception conditions for the main additions, correction
accumulation additions, and final addition, the literal finite program agrees
with the safe-completion executor used by the error analysis. -/
theorem neumaierFinite_sum_eq_neumaierFF_sum
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hmain : ∀ i : Fin n,
      neumaierFF_stepCondition fmt (neumaierFF_prefix fmt v i) (v i))
    (hcorr : ∀ i : Fin n,
      neumaierFF_stepCondition fmt
        (neumaierFF_prefix fmt (neumaierFinite_corrections fmt v) i)
        (neumaierFinite_corrections fmt v i))
    (hfinal : neumaierFF_stepCondition fmt
      (fl_recursiveSum (kahanFF_model fmt) n v)
      (fl_recursiveSum (kahanFF_model fmt) n
        (neumaierFinite_corrections fmt v))) :
    neumaierFinite_sum fmt n v = neumaierFF_sum fmt n v := by
  have hmainEq := neumaierFinite_recursiveSum_eq_fl_recursiveSum
    fmt n v hmain
  have hcorrEq := neumaierFinite_recursiveSum_eq_fl_recursiveSum
    fmt n (neumaierFinite_corrections fmt v) hcorr
  have hcorrInputs : neumaierFinite_corrections fmt v =
      neumaierFF_corrections fmt v := by
    funext i
    exact neumaierFinite_correction_eq_neumaierFF_correction
      fmt hbeta ht v hmain i
  have hfinalBridge :
      (kahanFF_model fmt).fl_add
          (fl_recursiveSum (kahanFF_model fmt) n v)
          (fl_recursiveSum (kahanFF_model fmt) n
            (neumaierFinite_corrections fmt v)) =
        fmt.finiteRoundToEvenOp BasicOp.add
          (fl_recursiveSum (kahanFF_model fmt) n v)
          (fl_recursiveSum (kahanFF_model fmt) n
            (neumaierFinite_corrections fmt v)) :=
    kahanFF_fl_add_eq_finiteRoundToEvenOp fmt hfinal.2.1 hfinal.2.2
  unfold neumaierFinite_sum neumaierFF_sum
  rw [hmainEq, hcorrEq]
  simpa [hcorrInputs] using hfinalBridge.symm






























end NumStability
