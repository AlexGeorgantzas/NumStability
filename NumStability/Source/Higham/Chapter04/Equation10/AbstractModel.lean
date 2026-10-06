import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Error
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Analysis.Summation.Signs
import NumStability.Algorithms.Summation.Compensated.Alternative.Core
import NumStability.Algorithms.Summation.Compensated.Alternative.ErrorBounds
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Compensated.Kahan.ErrorBounds
import NumStability.Algorithms.Summation.Recursive.Core

namespace NumStability

/-!
# Higham Chapter 4, equation (4.10): abstract-model route

Source correspondence for the equation-(4.10) backward-error transfer chain,
its printed-cap closures and failed global-gamma route, and the resulting
forward and one-signed relative-error consequences.
-/

/-- Higham, 2nd ed., Chapter 4, Section 4.3, equation (4.10) transfer layer.

For the printed p. 85 alternative compensated-summation variant, the local exact
correction invariant reduces the source-shaped backward-error theorem to one
remaining correction-transfer obligation.  If the recursive summation error on
the stored correction list can be rewritten as source perturbations bounded by
`C`, then the final rounded add gives source perturbations bounded by
`fp.u + C + C*fp.u`.

This is intentionally an intermediate theorem: the source-strength row still
requires a proof of the displayed correction-transfer bound with
`C = O(n^2*u^2)`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (htransfer :
      ∀ θ : Fin n → ℝ,
        (∀ i, |θ i| ≤ gamma fp (n - 1)) →
        ∃ η : Fin n → ℝ,
          (∀ i, |η i| ≤ C) ∧
          (∑ i : Fin n,
              alternativeCompensatedCorrections fp v i * θ i) =
            ∑ i : Fin n, v i * η i) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ fp.u + C + C * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let main := fl_alternativeCompensatedMainSum fp n v
  let global := fl_alternativeCompensatedGlobalCorrection fp n v
  let source := ∑ i : Fin n, v i
  let exactCorr := ∑ i : Fin n, corr i
  obtain ⟨θ, hθ, hglobalBack⟩ :=
    recursiveSum_backward_error fp n corr hgamma
  obtain ⟨η, hη, hcorrTransfer⟩ := htransfer θ hθ
  obtain ⟨δ, hδ, hfinal⟩ := fp.model_add main global
  have hmain :
      main + exactCorr = source := by
    simpa [main, exactCorr, source, corr] using
      fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
        fp n v hexact
  have hglobalErr :
      global - exactCorr = ∑ i : Fin n, corr i * θ i := by
    simpa [global, exactCorr, corr, fl_alternativeCompensatedGlobalCorrection]
      using recursiveSum_error_decomp fp n corr θ hglobalBack
  have hglobalSource :
      global = exactCorr + ∑ i : Fin n, v i * η i := by
    have hglobal_eq :
        global = exactCorr + ∑ i : Fin n, corr i * θ i := by
      linarith
    calc
      global = exactCorr + ∑ i : Fin n, corr i * θ i := hglobal_eq
      _ = exactCorr + ∑ i : Fin n, v i * η i := by
        rw [hcorrTransfer]
  have hmainGlobalSource :
      main + global = ∑ i : Fin n, v i * (1 + η i) := by
    calc
      main + global = source + ∑ i : Fin n, v i * η i := by
        rw [hglobalSource]
        linarith
      _ = ∑ i : Fin n, v i * (1 + η i) := by
        dsimp [source]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  refine ⟨fun i => η i + δ + η i * δ, ?_, ?_⟩
  · intro i
    have hmul : |η i * δ| ≤ C * fp.u := by
      rw [abs_mul]
      exact mul_le_mul (hη i) hδ (abs_nonneg δ) hC_nonneg
    calc
      |η i + δ + η i * δ|
          ≤ |η i + δ| + |η i * δ| := abs_add_le _ _
      _ ≤ (|η i| + |δ|) + |η i * δ| := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (abs_add_le (η i) δ) |η i * δ|
      _ ≤ (C + fp.u) + C * fp.u := by
        exact add_le_add (add_le_add (hη i) hδ) hmul
      _ = fp.u + C + C * fp.u := by ring
  · calc
      fl_alternativeCompensatedSum fp n v = fp.fl_add main global := by
        simpa [main, global] using
          fl_alternativeCompensatedSum_eq_add_globalCorrection fp n v
      _ = (main + global) * (1 + δ) := hfinal
      _ = (∑ i : Fin n, v i * (1 + η i)) * (1 + δ) := by
        rw [hmainGlobalSource]
      _ = ∑ i : Fin n, v i * (1 + (η i + δ + η i * δ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        ring

/-- Capped form of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer`.

This is the equation-(4.10) handoff shape: once a source proof supplies a
correction-transfer radius `C` and an arithmetic budget `fp.u + C + C*fp.u ≤ B`,
the alternative compensated-summation value has a source-shaped backward-error
witness bounded by `B`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer_le
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {B C : ℝ} (hC_nonneg : 0 ≤ C)
    (htransfer :
      ∀ θ : Fin n → ℝ,
        (∀ i, |θ i| ≤ gamma fp (n - 1)) →
        ∃ η : Fin n → ℝ,
          (∀ i, |η i| ≤ C) ∧
          (∑ i : Fin n,
              alternativeCompensatedCorrections fp v i * θ i) =
            ∑ i : Fin n, v i * η i)
    (hbudget : fp.u + C + C * fp.u ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer
      fp n v hexact hgamma hC_nonneg htransfer
  exact ⟨μ, fun i => le_trans (hμ i) hbudget, hsum⟩

/-- Absolute correction-list bound implies the correction-transfer obligation
used by equation-(4.10)'s alternative compensated-summation bridge.

If the stored local corrections have absolute sum at most
`D * sum_i |x_i|`, then the recursive-summation error on those corrections is
source-representable with radius `gamma (n-1) * D`. -/
theorem alternativeCompensatedCorrectionTransfer_of_correction_abs_sum_le
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hgamma : gammaValid fp (n - 1))
    {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hcorrAbs :
      ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∀ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp (n - 1)) →
      ∃ η : Fin n → ℝ,
        (∀ i, |η i| ≤ gamma fp (n - 1) * D) ∧
        (∑ i : Fin n,
            alternativeCompensatedCorrections fp v i * θ i) =
          ∑ i : Fin n, v i * η i := by
  intro θ hθ
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  have hgamma_nonneg : 0 ≤ gamma fp (n - 1) :=
    gamma_nonneg fp hgamma
  have hC_nonneg : 0 ≤ gamma fp (n - 1) * D :=
    mul_nonneg hgamma_nonneg hD_nonneg
  have habs :
      |∑ i : Fin n, corr i * θ i| ≤
        (gamma fp (n - 1) * D) * ∑ i : Fin n, |v i| := by
    calc
      |∑ i : Fin n, corr i * θ i|
          ≤ ∑ i : Fin n, |corr i * θ i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |corr i| * |θ i| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul]
      _ ≤ ∑ i : Fin n, |corr i| * gamma fp (n - 1) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg (corr i))
      _ = gamma fp (n - 1) * ∑ i : Fin n, |corr i| := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ gamma fp (n - 1) *
            (D * ∑ i : Fin n, |v i|) := by
        exact mul_le_mul_of_nonneg_left (by simpa [corr] using hcorrAbs)
          hgamma_nonneg
      _ = (gamma fp (n - 1) * D) *
            ∑ i : Fin n, |v i| := by ring
  simpa [corr] using
    exists_summation_source_coefficients_of_abs_le_mul_sum_abs
      v hC_nonneg habs

/-- Equation-(4.10) composition from an absolute bound on the stored correction
list.

The remaining source proof obligation is now the interpretable inequality
`sum_i |e_i| <= D * sum_i |x_i|`; recursive summation of the correction list
then contributes the radius `gamma (n-1) * D`, and the final rounded add
contributes the outer `fp.u` term. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hcorrAbs :
      ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          fp.u + gamma fp (n - 1) * D +
            (gamma fp (n - 1) * D) * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_transfer
      fp n v hexact hgamma
      (mul_nonneg (gamma_nonneg fp hgamma) hD_nonneg)
      (alternativeCompensatedCorrectionTransfer_of_correction_abs_sum_le
        fp n v hgamma hD_nonneg hcorrAbs)

/-- Capped version of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le`.

This is the natural finite-budget handoff for the printed equation-(4.10)
constant: prove a correction-list absolute-sum bound with radius `D`, prove the
displayed arithmetic cap `fp.u + gamma(n-1)*D + gamma(n-1)*D*fp.u <= B`, and
this theorem supplies the final source-shaped backward-error witness. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {B D : ℝ} (hD_nonneg : 0 ≤ D)
    (hcorrAbs :
      ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
        D * ∑ i : Fin n, |v i|)
    (hbudget :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
      fp n v hexact hgamma hD_nonneg hcorrAbs
  exact ⟨μ, fun i => le_trans (hμ i) hbudget, hsum⟩

/-- Pointwise local-budget form for the stored corrections in the printed p. 85
alternative compensated-summation variant.

When the local correction formula is exact, the stored correction `e_i` is
exactly the residual of the main rounded add `s_i = fl(temp_i + x_i)`, up to
sign.  Thus any absolute budget for that main-add residual is also a budget for
`|e_i|`. -/
theorem alternativeCompensatedCorrection_abs_le_of_exact_step_and_main_add_residual
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hexact_i :
      let sum := alternativeCompensatedPrefixSum fp v i.val
        (Nat.le_of_lt i.isLt)
      let trace := alternativeCompensatedStepTrace fp (v i) sum
      CorrectionFormulaTrace.exact sum (v i)
        ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {B : ℝ}
    (hmain :
      |(alternativeCompensatedTrace fp v i).s -
          ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B) :
    |alternativeCompensatedCorrections fp v i| ≤ B := by
  let sum := alternativeCompensatedPrefixSum fp v i.val
    (Nat.le_of_lt i.isLt)
  let trace := alternativeCompensatedStepTrace fp (v i) sum
  have hcorr :
      sum + v i = trace.s + trace.e := by
    simpa [CorrectionFormulaTrace.exact, sum, trace] using hexact_i
  have he :
      trace.e = sum + v i - trace.s := by
    linarith
  calc
    |alternativeCompensatedCorrections fp v i| = |trace.e| := by
      simp [alternativeCompensatedCorrections, alternativeCompensatedTrace,
        trace, sum]
    _ = |sum + v i - trace.s| := by rw [he]
    _ = |trace.s - (sum + v i)| := by rw [abs_sub_comm]
    _ =
        |(alternativeCompensatedTrace fp v i).s -
          ((alternativeCompensatedTrace fp v i).temp + v i)| := by
      simp [alternativeCompensatedTrace, alternativeCompensatedStepTrace,
        trace, sum]
    _ ≤ B := hmain

/-- The primitive `FPModel` add model gives the local main-add residual budget
used by the alternative compensated-summation correction analysis. -/
theorem alternativeCompensatedTrace_main_add_residual_le_unit_roundoff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(alternativeCompensatedTrace fp v i).s -
        ((alternativeCompensatedTrace fp v i).temp + v i)| ≤
      fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| := by
  let trace := alternativeCompensatedTrace fp v i
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add trace.temp (v i)
  have hs : trace.s = fp.fl_add trace.temp (v i) := by
    simp [trace, alternativeCompensatedTrace, alternativeCompensatedStepTrace]
  have hres :
      |trace.s - (trace.temp + v i)| ≤ fp.u * |trace.temp + v i| := by
    calc
      |trace.s - (trace.temp + v i)|
          = |(trace.temp + v i) * δ| := by
            rw [hs, hfl]
            ring_nf
      _ = |trace.temp + v i| * |δ| := by
        rw [abs_mul]
      _ ≤ |trace.temp + v i| * fp.u := by
        exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
      _ = fp.u * |trace.temp + v i| := by ring
  simpa [trace] using hres

/-- Local main-add residual budgets imply an absolute bound on the stored
correction list for the printed p. 85 alternative compensated-summation variant. -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {B : Fin n → ℝ}
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      ∑ i : Fin n, B i := by
  apply Finset.sum_le_sum
  intro i _hi
  exact
    alternativeCompensatedCorrection_abs_le_of_exact_step_and_main_add_residual
      fp v i (hexact i) (hmain i)

/-- Exact local correction formulas plus the primitive `FPModel` add model give
an absolute-sum correction bound in terms of the rounded main-add inputs. -/
theorem alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_main_add_inputs
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      ∑ i : Fin n,
        fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| := by
  exact
    alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget
      fp v hexact
      (fun i => alternativeCompensatedTrace_main_add_residual_le_unit_roundoff
        fp v i)

/-- Higham §4.2 running-sum form of the correction-list absolute bound:
under exact local correction formulas, the sum of stored correction magnitudes
is bounded by `u` times the sum of ordinary recursive-summation pre-rounding
partial sums. -/
theorem alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_partialSums
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| := by
  calc
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i|
        ≤ ∑ i : Fin n,
            fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| :=
          alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_main_add_inputs
            fp v hexact
    _ = fp.u * ∑ i : Fin n, |fl_partialSums fp v i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [alternativeCompensatedTrace_main_add_input_eq_fl_partialSums]

/-- Local residual budgets plus an aggregate source-weighted cap close the
correction-list absolute-sum obligation used by the equation-(4.10) bridge. -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget_cap
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {B : Fin n → ℝ} {D : ℝ}
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i)
    (hbudget :
      ∑ i : Fin n, B i ≤ D * ∑ i : Fin n, |v i|) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      D * ∑ i : Fin n, |v i| := by
  exact le_trans
    (alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget
      fp v hexact hmain)
    hbudget

/-- Unit-roundoff local residuals plus an aggregate source-weighted cap close
the correction-list absolute-sum obligation used by the equation-(4.10)
bridge.  The remaining cap is a prefix-growth/source-weighted estimate for the
rounded main-add inputs. -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_unit_roundoff_main_add_inputs_cap
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {D : ℝ}
    (hbudget :
      ∑ i : Fin n,
          fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      D * ∑ i : Fin n, |v i| := by
  exact le_trans
    (alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_main_add_inputs
      fp v hexact)
    hbudget

/-- A source-weighted cap on the recursive-summation partial sums closes the
correction-list absolute-sum obligation for equation (4.10). -/
theorem alternativeCompensatedCorrections_abs_sum_le_of_partialSums_cap
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {D : ℝ}
    (hbudget :
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| ≤
        D * ∑ i : Fin n, |v i|) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      D * ∑ i : Fin n, |v i| := by
  exact le_trans
    (alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_partialSums
      fp v hexact)
    hbudget

/-- Fully instantiated correction-list absolute-sum bound using the ordinary
recursive-summation partial-sum cap. -/
theorem alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_global_gamma
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1)) :
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i| ≤
      (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) *
        ∑ i : Fin n, |v i| := by
  have hpartial :=
    fl_partialSums_abs_sum_le_n_mul_one_add_gamma_mul_sum_abs fp n v hgamma
  calc
    ∑ i : Fin n, |alternativeCompensatedCorrections fp v i|
        ≤ fp.u * ∑ i : Fin n, |fl_partialSums fp v i| :=
          alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_partialSums
            fp v hexact
    _ ≤ fp.u *
          (((n : ℝ) * (1 + gamma fp (n - 1))) *
            ∑ i : Fin n, |v i|) := by
      exact mul_le_mul_of_nonneg_left hpartial fp.u_nonneg
    _ = (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) *
          ∑ i : Fin n, |v i| := by ring

/-- Equation-(4.10) bridge from local main-add residual budgets.

This theorem replaces the correction-list absolute-sum hypothesis by the next
local obligation: bound each main rounded add residual and show that the sum of
those local budgets is at most `D * sum_i |x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_local_main_add_residual_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {B : Fin n → ℝ} {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i)
    (hbudget :
      ∑ i : Fin n, B i ≤ D * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          fp.u + gamma fp (n - 1) * D +
            (gamma fp (n - 1) * D) * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_of_local_main_add_residual_budget_cap
        fp v hexact hmain hbudget)

/-- Capped source-shaped backward-error theorem from local main-add residual
budgets for the printed p. 85 alternative compensated-summation variant. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_local_main_add_residual_budget_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A : ℝ} {B : Fin n → ℝ} {D : ℝ} (hD_nonneg : 0 ≤ D)
    (hmain :
      ∀ i : Fin n,
        |(alternativeCompensatedTrace fp v i).s -
            ((alternativeCompensatedTrace fp v i).temp + v i)| ≤ B i)
    (hbudget :
      ∑ i : Fin n, B i ≤ D * ∑ i : Fin n, |v i|)
    (hcap :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_local_main_add_residual_budget
      fp n v hexact hgamma hD_nonneg hmain hbudget
  exact ⟨μ, fun i => le_trans (hμ i) hcap, hsum⟩

/-- Equation-(4.10) bridge with the primitive `FPModel` local add residual
instantiated.  The remaining source-specific obligation is the aggregate cap
on `sum_i fp.u * |temp_i + x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_unit_roundoff_main_add_inputs_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A D : ℝ} (hD_nonneg : 0 ≤ D)
    (hbudget :
      ∑ i : Fin n,
          fp.u * |(alternativeCompensatedTrace fp v i).temp + v i| ≤
        D * ∑ i : Fin n, |v i|)
    (hcap :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le_budget
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_of_unit_roundoff_main_add_inputs_cap
        fp v hexact hbudget)
      hcap

/-- Equation-(4.10) bridge with the correction-list budget reduced to the
ordinary recursive-summation partial-sum cap from Higham §4.2. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_partialSums_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A D : ℝ} (hD_nonneg : 0 ≤ D)
    (hbudget :
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| ≤
        D * ∑ i : Fin n, |v i|)
    (hcap :
      fp.u + gamma fp (n - 1) * D +
          (gamma fp (n - 1) * D) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le_budget
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_of_partialSums_cap
        fp v hexact hbudget)
      hcap

/-- Equation-(4.10) bridge using the running-error bound for the recursively
summed correction list.

This avoids the `gamma * sum_i |e_i|` transfer used by
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le`.
Instead, it asks for the sharper source-weighted bound on the recursive
summation running-error budget of the stored corrections:
`u * sum_i |partial_corrections_i| <= C * sum_i |x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hbudget :
      fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        C * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ fp.u + C + C * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let main := fl_alternativeCompensatedMainSum fp n v
  let global := fl_alternativeCompensatedGlobalCorrection fp n v
  let source := ∑ i : Fin n, v i
  let exactCorr := ∑ i : Fin n, corr i
  have hmain :
      main + exactCorr = source := by
    simpa [main, exactCorr, source, corr] using
      fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
        fp n v hexact
  have hglobalErrAbs :
      |global - exactCorr| ≤ C * ∑ i : Fin n, |v i| := by
    have hrun :
        |global - exactCorr| ≤
          fp.u * ∑ i : Fin n, |fl_partialSums fp corr i| := by
      simpa [global, exactCorr, corr,
        fl_alternativeCompensatedGlobalCorrection] using
        recursiveSum_running_error_bound fp n corr
    exact le_trans hrun (by simpa [corr] using hbudget)
  obtain ⟨η, hη, hcorrTransfer⟩ :=
    exists_summation_source_coefficients_of_abs_le_mul_sum_abs
      v hC_nonneg hglobalErrAbs
  obtain ⟨δ, hδ, hfinal⟩ := fp.model_add main global
  have hglobalSource :
      global = exactCorr + ∑ i : Fin n, v i * η i := by
    have hglobal_eq :
        global = exactCorr + (global - exactCorr) := by ring
    rw [hglobal_eq, hcorrTransfer]
  have hmainGlobalSource :
      main + global = ∑ i : Fin n, v i * (1 + η i) := by
    calc
      main + global = source + ∑ i : Fin n, v i * η i := by
        rw [hglobalSource]
        linarith
      _ = ∑ i : Fin n, v i * (1 + η i) := by
        dsimp [source]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  refine ⟨fun i => η i + δ + η i * δ, ?_, ?_⟩
  · intro i
    have hmul : |η i * δ| ≤ C * fp.u := by
      rw [abs_mul]
      exact mul_le_mul (hη i) hδ (abs_nonneg δ) hC_nonneg
    calc
      |η i + δ + η i * δ|
          ≤ |η i + δ| + |η i * δ| := abs_add_le _ _
      _ ≤ |η i| + |δ| + |η i * δ| := by
        nlinarith [abs_add_le (η i) δ]
      _ ≤ C + fp.u + C * fp.u := by
        nlinarith [hη i, hδ, hmul]
      _ = fp.u + C + C * fp.u := by ring
  · rw [fl_alternativeCompensatedSum_eq_add_globalCorrection]
    have hadd :
        fp.fl_add main global =
          (main + global) * (1 + δ) := hfinal
    rw [hadd, hmainGlobalSource]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- Capped version of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    {A C : ℝ} (hC_nonneg : 0 ≤ C)
    (hbudget :
      fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        C * ∑ i : Fin n, |v i|)
    (hcap : fp.u + C + C * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget
      fp n v hexact hC_nonneg hbudget
  exact ⟨μ, fun i => le_trans (hμ i) hcap, hsum⟩

/-- Equation-(4.10) printed-cap bridge from a source-weighted running-error
budget for the recursively summed correction list.

The remaining mathematical obligation is the displayed `hbudget`, whose shape
matches the running-error route: the sum of correction-summation partial sums
must be second order, bounded by `n^2*u^2 * sum_i |x_i|`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10)
    (hbudget :
      fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i|) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  have hC_nonneg : 0 ≤ (n : ℝ) ^ 2 * fp.u ^ 2 := by
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC_le_one : (n : ℝ) ^ 2 * fp.u ^ 2 ≤ 1 := by
    have ha_nonneg : 0 ≤ (n : ℝ) * fp.u := by
      exact mul_nonneg (by exact_mod_cast Nat.zero_le n) fp.u_nonneg
    have hsq : ((n : ℝ) * fp.u) ^ 2 ≤ (1 / 10 : ℝ) ^ 2 :=
      sq_le_sq' (by nlinarith [ha_nonneg]) hsmall
    have hCeq : (n : ℝ) ^ 2 * fp.u ^ 2 = ((n : ℝ) * fp.u) ^ 2 := by
      ring
    rw [hCeq]
    nlinarith
  have hcap :
      fp.u + (n : ℝ) ^ 2 * fp.u ^ 2 +
          ((n : ℝ) ^ 2 * fp.u ^ 2) * fp.u ≤
        2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2 := by
    have hmul :
        ((n : ℝ) ^ 2 * fp.u ^ 2) * fp.u ≤ fp.u :=
      by
        simpa [one_mul] using
          mul_le_mul_of_nonneg_right hC_le_one fp.u_nonneg
    nlinarith
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_budget_cap
      fp n v hexact hC_nonneg hbudget hcap

/-- Higham Chapter 4 equation (4.10) for the printed p. 85 alternative compensated
summation variant, with the correction-list running-error budget discharged
from the exact local correction formulas and `n*u <= 0.1`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap
      fp n v hexact hsmall
      (alternativeCompensatedCorrectionRunningErrorBudget_of_exact_steps
        fp n v hexact hsmall)

/-- Pointwise correction-partial form of the remaining equation-(4.10)
running-error budget.

If every pre-rounding partial sum formed while recursively summing the stored
corrections is bounded by `n*u*sum_i |x_i|`, then the aggregate running-error
budget required by
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap`
has exactly the printed second-order size `n^2*u^2*sum_i |x_i|`. -/
theorem alternativeCompensatedCorrectionRunningErrorBudget_of_pointwise_partialSums
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hpartial :
      ∀ i : Fin n,
        |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
          ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j|) :
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ j : Fin n, |v j| := by
  have hsum :
      ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
        ∑ i : Fin n, ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j| := by
    apply Finset.sum_le_sum
    intro i _hi
    exact hpartial i
  calc
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i|
        ≤ fp.u *
            ∑ i : Fin n, ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j| := by
          exact mul_le_mul_of_nonneg_left hsum fp.u_nonneg
    _ = ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ j : Fin n, |v j| := by
          rw [Finset.sum_const]
          simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-- Equation-(4.10) printed-cap bridge from a pointwise bound on the computed
partial sums of the stored correction list.

This is the next dependency-reduction form after the running-error bridge: the
remaining mathematical task is to prove the displayed `hpartial` bound from
the exact local correction formulas and recursive-summation prefix analysis. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_pointwise_correction_partial_higham_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10)
    (hpartial :
      ∀ i : Fin n,
        |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
          ((n : ℝ) * fp.u) * ∑ j : Fin n, |v j|) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_running_error_higham_cap
      fp n v hexact hsmall
      (alternativeCompensatedCorrectionRunningErrorBudget_of_pointwise_partialSums
        fp n v hpartial)

/-- Equation-(4.10) source-shaped backward-error theorem with the correction
budget instantiated by the recursive-summation global partial-sum cap.

This leaves no correction-list or partial-sum hypothesis; the displayed radius
is the exact bound produced by the current local infrastructure. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1)) :
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          fp.u +
            gamma fp (n - 1) *
              (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) +
            (gamma fp (n - 1) *
              (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))))) * fp.u) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  have hD_nonneg :
      0 ≤ fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))) := by
    have hfactor : 0 ≤ (n : ℝ) * (1 + gamma fp (n - 1)) := by
      exact mul_nonneg (by exact_mod_cast Nat.zero_le n)
        (by nlinarith [gamma_nonneg fp hgamma])
    exact mul_nonneg fp.u_nonneg hfactor
  exact
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_correction_abs_sum_le
      fp n v hexact hgamma hD_nonneg
      (alternativeCompensatedCorrections_abs_sum_le_unit_roundoff_global_gamma
        fp n v hexact hgamma)

/-- Capped version of
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma`. -/
theorem fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma_cap
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (n - 1))
    {A : ℝ}
    (hcap :
      fp.u +
          gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) +
          (gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))))) * fp.u ≤ A) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ A) ∧
      fl_alternativeCompensatedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_global_gamma
      fp n v hexact hgamma
  exact ⟨μ, fun i => le_trans (hμ i) hcap, hsum⟩

/-- The instantiated global-gamma route for equation (4.10) is not by itself
strong enough to imply the printed `2*u + n^2*u^2` cap from only
`n*u <= 0.1`.

This is a route audit, not a counterexample to Higham's theorem: it shows that
the current partial-sum majorization has to be sharpened before the exact
printed constant can be obtained from this proof path. -/
theorem not_forall_alternativeCompensated_globalGammaRadius_le_two_u_add_n_sq_u_sq_of_nu_le_tenth :
    ¬ ∀ (fp : FPModel) (n : ℕ),
      gammaValid fp (n - 1) →
      (n : ℝ) * fp.u ≤ 1 / 10 →
      fp.u +
          gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1)))) +
          (gamma fp (n - 1) *
            (fp.u * ((n : ℝ) * (1 + gamma fp (n - 1))))) * fp.u ≤
        2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2 := by
  intro h
  let fp : FPModel := FPModel.exactWithUnitRoundoff (1 / 1000) (by norm_num)
  have hvalid : gammaValid fp (100 - 1) := by
    norm_num [fp, FPModel.exactWithUnitRoundoff, gammaValid]
  have hsmall : (100 : ℝ) * fp.u ≤ 1 / 10 := by
    norm_num [fp, FPModel.exactWithUnitRoundoff]
  have hineq := h fp 100 hvalid hsmall
  norm_num [fp, FPModel.exactWithUnitRoundoff, gamma] at hineq

/-- If the final printed p. 85 alternative compensated-summation value satisfies a
backward-error representation with componentwise perturbation bound `B`, then
it satisfies the corresponding absolute forward-error bound.  This is the
algebraic part of turning an equation-(4.10)-style witness into a forward
error statement. -/
theorem fl_alternativeCompensatedSum_forward_error_bound_of_backward
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_alternativeCompensatedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i)) :
    |fl_alternativeCompensatedSum fp n v - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| :=
  kahan_backward_error_forward_bound_core v hback

/-- One-signed relative-error consequence of a supplied printed p. 85 alternative
compensated-summation backward-error representation. -/
theorem fl_alternativeCompensatedSum_relError_le_of_backward_oneSigned
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_alternativeCompensatedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i))
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_alternativeCompensatedSum fp n v)
        (∑ i : Fin n, v i) ≤ B := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound :=
    fl_alternativeCompensatedSum_forward_error_bound_of_backward
      fp n v hback
  have hbound_one :
      |fl_alternativeCompensatedSum fp n v - ∑ i : Fin n, v i| ≤
        B * |∑ i : Fin n, v i| := by
    simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound_one

end NumStability
