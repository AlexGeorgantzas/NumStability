import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Analysis.Rounding
import NumStability.Analysis.Summation.ErrorBounds
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

/-- The exact local residual of one rounded recursive-summation addition.
It is the correction that a magnitude-adaptive FastTwoSum step recovers. -/
noncomputable def recursiveSumLocalCorrection
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  let prev := fl_recursiveSum fp i.val
    (fun j : Fin i.val => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)
  (prev + v i) - fp.fl_add prev (v i)

/-- Prefix form of the canonical correction list. -/
noncomputable def recursiveSumPrefixCorrection
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (i : Fin k) : ℝ :=
  recursiveSumLocalCorrection fp
    (fun j : Fin k => v ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) i

/-- Adding the canonical exact residual to one rounded addition recovers its
exact pre-rounding sum. -/
theorem recursiveSumLocalCorrection_add_rounded
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    fp.fl_add
        (fl_recursiveSum fp i.val
          (fun j : Fin i.val => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩))
        (v i) +
      recursiveSumLocalCorrection fp v i =
    fl_recursiveSum fp i.val
        (fun j : Fin i.val => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) +
      v i := by
  simp [recursiveSumLocalCorrection]

/-- The main recursive prefix plus all its exact local residuals is the exact
source prefix. -/
theorem fl_recursiveSum_add_prefixCorrections_eq_sum
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      fl_recursiveSum fp k
          (fun i : Fin k => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) +
        ∑ i : Fin k, recursiveSumPrefixCorrection fp v k hk i =
      ∑ i : Fin k, v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  | 0, _ => by simp [fl_recursiveSum, recursiveSumPrefixCorrection]
  | k + 1, hk => by
      let pref : Fin (k + 1) → ℝ :=
        fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      let old : Fin k → ℝ := fun i => pref i.castSucc
      have hfold :
          fl_recursiveSum fp (k + 1) pref =
            fp.fl_add (fl_recursiveSum fp k old) (pref (Fin.last k)) :=
        Fin.foldl_succ_last _ _
      have ih := fl_recursiveSum_add_prefixCorrections_eq_sum fp v k
        (Nat.le_trans (Nat.le_succ k) hk)
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      rw [hfold]
      have hcorrLast :
          recursiveSumPrefixCorrection fp v (k + 1) hk (Fin.last k) =
            (fl_recursiveSum fp k old + pref (Fin.last k)) -
              fp.fl_add (fl_recursiveSum fp k old) (pref (Fin.last k)) := by
        simp [recursiveSumPrefixCorrection, recursiveSumLocalCorrection, pref, old]
      have hcorrCast :
          ∀ i : Fin k,
            recursiveSumPrefixCorrection fp v (k + 1) hk i.castSucc =
              recursiveSumPrefixCorrection fp v k
                (Nat.le_trans (Nat.le_succ k) hk) i := by
        intro i
        simp [recursiveSumPrefixCorrection, recursiveSumLocalCorrection]
      rw [hcorrLast]
      simp_rw [hcorrCast]
      dsimp [pref, old] at ih ⊢
      linarith

/-- Full-input form of the exact residual invariant. -/
theorem fl_recursiveSum_add_localCorrections_eq_sum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_recursiveSum fp n v +
        ∑ i : Fin n, recursiveSumLocalCorrection fp v i =
      ∑ i : Fin n, v i := by
  simpa [recursiveSumPrefixCorrection] using
    fl_recursiveSum_add_prefixCorrections_eq_sum fp v n (Nat.le_refl n)

/-- The exact sum of the local residuals in a prefix is the negative forward
error of ordinary recursive summation on that prefix. -/
theorem recursiveSumPrefixCorrections_abs_le_forward
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hgamma : gammaValid fp (k - 1)) :
    |∑ i : Fin k, recursiveSumPrefixCorrection fp v k hk i| ≤
      gamma fp (k - 1) *
        ∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| := by
  let pref : Fin k → ℝ :=
    fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  let main := fl_recursiveSum fp k pref
  let corr := ∑ i : Fin k, recursiveSumPrefixCorrection fp v k hk i
  have hinv : main + corr = ∑ i : Fin k, pref i := by
    simpa [main, corr, pref] using
      fl_recursiveSum_add_prefixCorrections_eq_sum fp v k hk
  have hcorr : |corr| = |main - ∑ i : Fin k, pref i| := by
    have : corr = (∑ i : Fin k, pref i) - main := by linarith
    rw [this, abs_sub_comm]
  calc
    |∑ i : Fin k, recursiveSumPrefixCorrection fp v k hk i| = |corr| := rfl
    _ = |main - ∑ i : Fin k, pref i| := hcorr
    _ ≤ gamma fp (k - 1) * ∑ i : Fin k, |pref i| := by
      simpa [main] using recursiveSum_forward_error_bound fp k pref hgamma
    _ = gamma fp (k - 1) *
        ∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| := rfl

































































































































































/-- A pre-rounding partial sum of the recursively accumulated residual list is
the corresponding exact residual prefix plus the earlier accumulation error. -/
theorem fl_partialSums_localCorrections_abs_le_exactPrefix_add_runningError
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |fl_partialSums fp (recursiveSumLocalCorrection fp v) i| ≤
      |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| +
        fp.u *
          ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val =>
                recursiveSumLocalCorrection fp v
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| := by
  let corr : Fin n → ℝ := recursiveSumLocalCorrection fp v
  let prevCorr : Fin i.val → ℝ := fun t =>
    corr ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩
  let prevComp := fl_recursiveSum fp i.val prevCorr
  let prevExact := ∑ t : Fin i.val, prevCorr t
  let exactPrefix :=
    ∑ j : Fin (i.val + 1),
      recursiveSumPrefixCorrection fp v (i.val + 1)
        (Nat.succ_le_of_lt i.isLt) j
  have hpartial : fl_partialSums fp corr i = prevComp + corr i := by
    simp [fl_partialSums, corr, prevCorr, prevComp]
  have hprefix : exactPrefix = prevExact + corr i := by
    dsimp [exactPrefix, prevExact, prevCorr, corr]
    rw [Fin.sum_univ_castSucc]
    simp [recursiveSumPrefixCorrection, recursiveSumLocalCorrection]
  have hdecomp : fl_partialSums fp corr i =
      exactPrefix + (prevComp - prevExact) := by
    rw [hpartial, hprefix]
    ring
  have hrun : |prevComp - prevExact| ≤
      fp.u * ∑ j : Fin i.val, |fl_partialSums fp prevCorr j| := by
    simpa [prevComp, prevExact, prevCorr] using
      recursiveSum_running_error_bound fp i.val prevCorr
  calc
    |fl_partialSums fp (recursiveSumLocalCorrection fp v) i|
        = |exactPrefix + (prevComp - prevExact)| := by
            simpa [corr] using congrArg abs hdecomp
    _ ≤ |exactPrefix| + |prevComp - prevExact| := abs_add_le _ _
    _ ≤ |exactPrefix| +
        fp.u * ∑ j : Fin i.val, |fl_partialSums fp prevCorr j| :=
      add_le_add (le_refl _) hrun
    _ = |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| +
        fp.u *
          ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val =>
                recursiveSumLocalCorrection fp v
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| := rfl


















































































































/-! ## The exact-residual separately accumulated executor -/

/-- Recursive main sum, recursively accumulated exact local residuals, and one
final rounded correction add. -/
noncomputable def fl_recursiveResidualCorrectedSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  fp.fl_add (fl_recursiveSum fp n v)
    (fl_recursiveSum fp n (recursiveSumLocalCorrection fp v))

/-- Generic backward-error transfer from a running-error budget on the
separately accumulated exact residuals. -/
theorem fl_recursiveResidualCorrectedSum_backward_error_of_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbudget :
      fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (recursiveSumLocalCorrection fp v) i| ≤
        C * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ fp.u + C + C * fp.u) ∧
      fl_recursiveResidualCorrectedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let corr : Fin n → ℝ := recursiveSumLocalCorrection fp v
  let main := fl_recursiveSum fp n v
  let global := fl_recursiveSum fp n corr
  let source := ∑ i : Fin n, v i
  let exactCorr := ∑ i : Fin n, corr i
  have hinv : main + exactCorr = source := by
    simpa [main, exactCorr, source, corr] using
      fl_recursiveSum_add_localCorrections_eq_sum fp n v
  have hglobal : |global - exactCorr| ≤ C * ∑ i : Fin n, |v i| := by
    have hrun : |global - exactCorr| ≤
        fp.u * ∑ i : Fin n, |fl_partialSums fp corr i| := by
      simpa [global, exactCorr, corr] using
        recursiveSum_running_error_bound fp n corr
    exact hrun.trans (by simpa [corr] using hbudget)
  obtain ⟨η, hη, htransfer⟩ :=
    exists_summation_source_coefficients_of_abs_le_mul_sum_abs
      v hC hglobal
  obtain ⟨δ, hδ, hfinal⟩ := fp.model_add main global
  have hglobalSource :
      global = exactCorr + ∑ i : Fin n, v i * η i := by
    calc
      global = exactCorr + (global - exactCorr) := by ring
      _ = exactCorr + ∑ i : Fin n, v i * η i := by rw [htransfer]
  have hmainGlobal :
      main + global = ∑ i : Fin n, v i * (1 + η i) := by
    calc
      main + global = source + ∑ i : Fin n, v i * η i := by
        rw [hglobalSource]
        linarith
      _ = ∑ i : Fin n, v i * (1 + η i) := by
        dsimp [source]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  refine ⟨fun i => η i + δ + η i * δ, ?_, ?_⟩
  · intro i
    have hmul : |η i * δ| ≤ C * fp.u := by
      rw [abs_mul]
      exact mul_le_mul (hη i) hδ (abs_nonneg δ) hC
    calc
      |η i + δ + η i * δ|
          ≤ |η i + δ| + |η i * δ| := abs_add_le _ _
      _ ≤ |η i| + |δ| + |η i * δ| := by
        nlinarith [abs_add_le (η i) δ]
      _ ≤ C + fp.u + C * fp.u := by
        nlinarith [hη i, hδ, hmul]
      _ = fp.u + C + C * fp.u := by ring
  · unfold fl_recursiveResidualCorrectedSum
    change fp.fl_add main global = _
    rw [hfinal, hmainGlobal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring






























/-! ## Magnitude-adaptive finite-format producer -/
































































































































































/-! ## Genuine finite-operation executor

The preceding safe-completion executor is convenient for error analysis.  The
definitions below contain only `finiteRoundToEvenOp` operations.  We prove a
trace equality, under explicit no-exception conditions, so the analytic result
above applies to the literal finite-format program rather than merely to its
completion.
-/












































































































































































































































































end NumStability
