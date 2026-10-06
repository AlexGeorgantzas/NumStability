import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Recursive.Core

namespace NumStability

/-!
# Alternative compensated summation: execution

Reusable execution trace and prefix API for the compensated-summation variant
that accumulates local corrections separately before applying one global
correction.
-/

/-- One step of the printed p. 85 alternative compensated-summation variant.  The main
sum is updated without immediately feeding the correction back into the next
input; the local correction is stored separately. -/
structure AlternativeCompensatedStepTrace where
  temp : ℝ
  s : ℝ
  e : ℝ

namespace AlternativeCompensatedStepTrace

/-- The main running sum after an alternative compensated-summation step. -/
def nextSum (t : AlternativeCompensatedStepTrace) : ℝ :=
  t.s

end AlternativeCompensatedStepTrace

/-- One rounded step of the alternative compensated-summation variant:
`temp = s; s = temp + x_i; e_i = (temp - s) + x_i`. -/
noncomputable def alternativeCompensatedStepTrace
    (fp : FPModel) (x : ℝ) (sum : ℝ) : AlternativeCompensatedStepTrace :=
  let temp := sum
  let s := fp.fl_add temp x
  let e := fp.fl_add (fp.fl_sub temp s) x
  { temp := temp, s := s, e := e }

/-- The `temp` assignment in the alternative compensated-summation variant. -/
theorem alternativeCompensatedStepTrace_temp
    (fp : FPModel) (x sum : ℝ) :
    (alternativeCompensatedStepTrace fp x sum).temp = sum := by
  rfl

/-- The main `s = temp + x_i` assignment in the alternative variant. -/
theorem alternativeCompensatedStepTrace_s
    (fp : FPModel) (x sum : ℝ) :
    (alternativeCompensatedStepTrace fp x sum).s =
      fp.fl_add (alternativeCompensatedStepTrace fp x sum).temp x := by
  rfl

/-- The stored correction `e_i = (temp - s) + x_i`, in the displayed Kahan
correction evaluation order but without immediate feedback into the main sum. -/
theorem alternativeCompensatedStepTrace_e
    (fp : FPModel) (x sum : ℝ) :
    (alternativeCompensatedStepTrace fp x sum).e =
      fp.fl_add
        (fp.fl_sub (alternativeCompensatedStepTrace fp x sum).temp
          (alternativeCompensatedStepTrace fp x sum).s)
        x := by
  rfl

/-- The local correction pair in one step of the printed p. 85 alternative variant is
exactly the Chapter 4 equation-(4.7) correction-formula trace applied to
`temp` and the current input. -/
theorem alternativeCompensatedStepTrace_correctionFormulaTrace
    (fp : FPModel) (x sum : ℝ) :
    ({ s := (alternativeCompensatedStepTrace fp x sum).s,
       e := (alternativeCompensatedStepTrace fp x sum).e } :
        CorrectionFormulaTrace) =
      correctionFormulaTrace fp
        (alternativeCompensatedStepTrace fp x sum).temp x := by
  simp [alternativeCompensatedStepTrace, correctionFormulaTrace]

/-- If the local correction formula is exact for one step of the printed p. 85
alternative variant, then that step's main sum plus stored correction equals
the previous main sum plus the current input. -/
theorem alternativeCompensatedStepTrace_main_plus_correction_eq_of_correction
    (fp : FPModel) (x sum : ℝ)
    (hcorr :
      CorrectionFormulaTrace.exact sum x
        ({ s := (alternativeCompensatedStepTrace fp x sum).s,
           e := (alternativeCompensatedStepTrace fp x sum).e } :
          CorrectionFormulaTrace)) :
    (alternativeCompensatedStepTrace fp x sum).s +
        (alternativeCompensatedStepTrace fp x sum).e =
      sum + x := by
  exact hcorr.symm

/-- Main running sum after the first `k` alternative compensated-summation
steps over a length-`n` input.  Corrections are not fed back into this prefix
state. -/
noncomputable def alternativeCompensatedPrefixSum (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  Fin.foldl k
    (fun sum i =>
      (alternativeCompensatedStepTrace fp
        (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) sum).nextSum)
    0

/-- The per-index alternative compensated-summation trace, using the main
prefix sum before index `i`. -/
noncomputable def alternativeCompensatedTrace (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : AlternativeCompensatedStepTrace :=
  alternativeCompensatedStepTrace fp (v i)
    (alternativeCompensatedPrefixSum fp v i.val (Nat.le_of_lt i.isLt))

/-- The correction sequence `e_i` that is accumulated separately. -/
noncomputable def alternativeCompensatedCorrections (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (alternativeCompensatedTrace fp v i).e

/-- The main prefix in the printed p. 85 alternative compensated-summation variant is
ordinary left-to-right recursive summation on the processed prefix. -/
theorem alternativeCompensatedPrefixSum_eq_fl_recursiveSum_prefix
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) :
    alternativeCompensatedPrefixSum fp v k hk =
      fl_recursiveSum fp k
        (fun i : Fin k => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) := by
  simp [alternativeCompensatedPrefixSum, fl_recursiveSum,
    alternativeCompensatedStepTrace, AlternativeCompensatedStepTrace.nextSum]

/-- The local pre-rounding main-add input in the printed p. 85 alternative variant is
the same `fl_partialSums` quantity used in Higham §4.2's running-error bound
for ordinary recursive summation. -/
theorem alternativeCompensatedTrace_main_add_input_eq_fl_partialSums
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (alternativeCompensatedTrace fp v i).temp + v i =
      fl_partialSums fp v i := by
  simp [alternativeCompensatedTrace, alternativeCompensatedStepTrace,
    fl_partialSums, alternativeCompensatedPrefixSum_eq_fl_recursiveSum_prefix]

/-- The stored correction generated at index `i` during a `k`-step prefix of
the alternative compensated-summation trace. -/
noncomputable def alternativeCompensatedPrefixCorrection
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (i : Fin k) : ℝ :=
  (alternativeCompensatedStepTrace fp
      (v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
      (alternativeCompensatedPrefixSum fp v i.val
        (Nat.le_trans (Nat.le_of_lt i.isLt) hk))).e

/-- Prefix invariant for the printed p. 85 alternative compensated-summation trace.

If every local correction formula is exact, then the main prefix sum plus the
exact sum of the stored local corrections equals the exact source prefix sum. -/
theorem alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        let sum :=
          alternativeCompensatedPrefixSum fp v i.val
            (Nat.le_trans (Nat.le_of_lt i.isLt) hk)
        let trace := alternativeCompensatedStepTrace fp (v idx) sum
        CorrectionFormulaTrace.exact sum (v idx)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) →
      alternativeCompensatedPrefixSum fp v k hk +
          ∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i =
        ∑ i : Fin k, v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  | 0, _hk, _hexact => by
      simp [alternativeCompensatedPrefixSum,
        alternativeCompensatedPrefixCorrection]
  | k + 1, hk, hexact => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let prev := alternativeCompensatedPrefixSum fp v k hprev_le
      let idx : Fin n :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let trace := alternativeCompensatedStepTrace fp (v idx) prev
      have hfold :
          alternativeCompensatedPrefixSum fp v (k + 1) hk =
            trace.s := by
        unfold alternativeCompensatedPrefixSum
        rw [Fin.foldl_succ_last]
        rfl
      have hprev :
          prev +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i =
            ∑ i : Fin k,
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩ := by
        apply
          alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
            fp v
        intro i
        simpa [alternativeCompensatedPrefixCorrection, prev, idx, trace]
          using hexact i.castSucc
      have hlocal := hexact (Fin.last k)
      have hstep :
          trace.s + trace.e = prev + v idx := by
        exact
          alternativeCompensatedStepTrace_main_plus_correction_eq_of_correction
            fp (v idx) prev hlocal
      rw [hfold]
      rw [Fin.sum_univ_castSucc]
      rw [Fin.sum_univ_castSucc]
      calc
        trace.s +
            (∑ x : Fin k,
                alternativeCompensatedPrefixCorrection fp v (k + 1) hk
                  x.castSucc +
              alternativeCompensatedPrefixCorrection fp v (k + 1) hk
                (Fin.last k)) =
          (trace.s + trace.e) +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i := by
            simp [alternativeCompensatedPrefixCorrection, trace, prev, idx]
            ring
        _ = (prev + v idx) +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i := by
            rw [hstep]
        _ = (prev +
              ∑ i : Fin k,
                alternativeCompensatedPrefixCorrection fp v k hprev_le i) +
              v idx := by
            ring
        _ = (∑ i : Fin k,
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hprev_le⟩) + v idx := by
            rw [hprev]

/-- The main computed sum before applying the global correction. -/
noncomputable def fl_alternativeCompensatedMainSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  alternativeCompensatedPrefixSum fp v n (Nat.le_refl n)

/-- The global correction obtained by recursive summation of the stored local
corrections. -/
noncomputable def fl_alternativeCompensatedGlobalCorrection
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  fl_recursiveSum fp n (alternativeCompensatedCorrections fp v)

/-- Final value of the printed p. 85 alternative compensated-summation variant: add
the recursively accumulated global correction to the computed main sum. -/
noncomputable def fl_alternativeCompensatedSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  fp.fl_add (fl_alternativeCompensatedMainSum fp n v)
    (fl_alternativeCompensatedGlobalCorrection fp n v)

/-- The main sum is the explicit `n`-step alternative prefix sum. -/
theorem fl_alternativeCompensatedMainSum_eq_prefixSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedMainSum fp n v =
      alternativeCompensatedPrefixSum fp v n (Nat.le_refl n) := by
  rfl

/-- The global correction is recursive summation of the stored local
corrections. -/
theorem fl_alternativeCompensatedGlobalCorrection_eq_recursiveSum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedGlobalCorrection fp n v =
      fl_recursiveSum fp n (alternativeCompensatedCorrections fp v) := by
  rfl

/-- The final alternative compensated sum is the rounded add of the main
computed sum and global correction. -/
theorem fl_alternativeCompensatedSum_eq_add_globalCorrection
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedSum fp n v =
      fp.fl_add (fl_alternativeCompensatedMainSum fp n v)
        (fl_alternativeCompensatedGlobalCorrection fp n v) := by
  rfl

end NumStability
