import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Algorithms.Summation.Compensated.Alternative.Core
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Recursive.Core

namespace NumStability

/-!
# Alternative compensated summation: reusable error bounds

Source-independent exact-step invariants, prefix correction budgets, recursive
summation bounds, and exact-arithmetic checks for the separately accumulated
correction algorithm.
-/

/-- Full-length form of the exact-step invariant for the printed p. 85 alternative
compensated-summation trace.  If each local correction formula is exact, then
the final main sum plus the exact sum of stored corrections is the exact
source sum. -/
theorem fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace)) :
    fl_alternativeCompensatedMainSum fp n v +
        ∑ i : Fin n, alternativeCompensatedCorrections fp v i =
      ∑ i : Fin n, v i := by
  simpa [fl_alternativeCompensatedMainSum,
    alternativeCompensatedCorrections, alternativeCompensatedTrace,
    alternativeCompensatedPrefixCorrection] using
    alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
      fp v n (Nat.le_refl n) hexact

/-- Prefix correction sums in the printed p. 85 alternative compensated-summation
variant are controlled by the ordinary recursive-summation forward-error bound.

For a `k`-step prefix, exact local correction formulas imply
`main_prefix + exact_corrections = exact_prefix`.  Since the main prefix is
ordinary recursive summation on the same prefix, the exact sum of stored
corrections is exactly the negative main recursive-summation error. -/
theorem alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n)
    (hexact :
      ∀ i : Fin k,
        let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
        let sum :=
          alternativeCompensatedPrefixSum fp v i.val
            (Nat.le_trans (Nat.le_of_lt i.isLt) hk)
        let trace := alternativeCompensatedStepTrace fp (v idx) sum
        CorrectionFormulaTrace.exact sum (v idx)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hgamma : gammaValid fp (k - 1)) :
    |∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i| ≤
      gamma fp (k - 1) *
        ∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| := by
  let pref : Fin k → ℝ :=
    fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  let main := alternativeCompensatedPrefixSum fp v k hk
  let corr :=
    ∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i
  have hmain_eq :
      main = fl_recursiveSum fp k pref := by
    simpa [main, pref] using
      alternativeCompensatedPrefixSum_eq_fl_recursiveSum_prefix fp v k hk
  have hcorr_eq :
      main + corr = ∑ i : Fin k, pref i := by
    simpa [main, corr, pref] using
      alternativeCompensatedPrefixSum_add_corrections_eq_sum_of_exact_steps
        fp v k hk hexact
  have hcorr_abs :
      |corr| = |main - ∑ i : Fin k, pref i| := by
    have hcorr_sub : corr = ∑ i : Fin k, pref i - main := by
      linarith
    rw [hcorr_sub, abs_sub_comm]
  calc
    |∑ i : Fin k, alternativeCompensatedPrefixCorrection fp v k hk i|
        = |corr| := by rfl
    _ = |main - ∑ i : Fin k, pref i| := hcorr_abs
    _ = |fl_recursiveSum fp k pref - ∑ i : Fin k, pref i| := by
      rw [hmain_eq]
    _ ≤ gamma fp (k - 1) * ∑ i : Fin k, |pref i| :=
      recursiveSum_forward_error_bound fp k pref hgamma
    _ = gamma fp (k - 1) *
        ∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| := by
      rfl

/-- Full-input specialization of
`alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward` for the
prefix ending at index `i`. -/
theorem alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward_of_full_exact
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (i : Fin n) (hgamma : gammaValid fp i.val) :
    |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j| ≤
      gamma fp i.val *
        ∑ j : Fin (i.val + 1),
          |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt i.isLt)⟩| := by
  have hprefixExact :
      ∀ j : Fin (i.val + 1),
        let idx : Fin n :=
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt i.isLt)⟩
        let sum :=
          alternativeCompensatedPrefixSum fp v j.val
            (Nat.le_trans (Nat.le_of_lt j.isLt)
              (Nat.succ_le_of_lt i.isLt))
        let trace := alternativeCompensatedStepTrace fp (v idx) sum
        CorrectionFormulaTrace.exact sum (v idx)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace) := by
    intro j
    let idx : Fin n :=
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.succ_le_of_lt i.isLt)⟩
    simpa [idx] using hexact idx
  simpa [Nat.add_sub_cancel] using
    alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward
      fp v (i.val + 1) (Nat.succ_le_of_lt i.isLt) hprefixExact hgamma

/-- A computed correction partial sum is bounded by the corresponding exact
correction prefix plus the running error from recursively summing the earlier
stored corrections.

This is the pointwise algebraic split needed for the aggregate equation-(4.10)
running-error budget: the exact-prefix term is controlled by
`alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward_of_full_exact`,
while the second term is the recursive-summation error of the correction list
itself. -/
theorem fl_partialSums_alternativeCompensatedCorrections_abs_le_exact_prefix_add_running_error
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| +
        fp.u *
          ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val =>
                alternativeCompensatedCorrections fp v
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let prevCorr : Fin i.val → ℝ :=
    fun t => corr ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩
  let prevComp := fl_recursiveSum fp i.val prevCorr
  let prevExact := ∑ t : Fin i.val, prevCorr t
  let exactPrefix :=
    ∑ j : Fin (i.val + 1),
      alternativeCompensatedPrefixCorrection fp v (i.val + 1)
        (Nat.succ_le_of_lt i.isLt) j
  have hpartial :
      fl_partialSums fp corr i = prevComp + corr i := by
    simp [fl_partialSums, corr, prevCorr, prevComp]
  have hprefix :
      exactPrefix = prevExact + corr i := by
    dsimp [exactPrefix, prevExact, prevCorr, corr]
    rw [Fin.sum_univ_castSucc]
    simp [alternativeCompensatedPrefixCorrection,
      alternativeCompensatedCorrections, alternativeCompensatedTrace]
  have hdecomp :
      fl_partialSums fp corr i =
        exactPrefix + (prevComp - prevExact) := by
    rw [hpartial, hprefix]
    ring
  have hrun :
      |prevComp - prevExact| ≤
        fp.u * ∑ j : Fin i.val, |fl_partialSums fp prevCorr j| := by
    simpa [prevComp, prevExact, prevCorr] using
      recursiveSum_running_error_bound fp i.val prevCorr
  calc
    |fl_partialSums fp corr i|
        = |exactPrefix + (prevComp - prevExact)| := by rw [hdecomp]
    _ ≤ |exactPrefix| + |prevComp - prevExact| := abs_add_le _ _
    _ ≤ |exactPrefix| +
        fp.u * ∑ j : Fin i.val, |fl_partialSums fp prevCorr j| := by
          exact add_le_add_right hrun _
    _ =
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| +
        fp.u *
          ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val =>
                alternativeCompensatedCorrections fp v
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| := by
      rfl

/-- Reindex a prefix over `Fin k` as the corresponding filtered sum over
`Fin n`.  Local copy for the compensated-summation prefix bookkeeping. -/
private lemma compensated_sum_fin_eq_sum_filter_lt {n k : ℕ} (hk : k ≤ n)
    (f : Fin n → ℝ) :
    (∑ t : Fin k, f ⟨t.val, by omega⟩) =
      Finset.sum (Finset.filter (fun j : Fin n => j.val < k) Finset.univ) f := by
  classical
  have hinj : ∀ a : Fin k, a ∈ Finset.univ →
      ∀ b : Fin k, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; exact hab)
  have himg : Finset.image (fun (t : Fin k) => (⟨t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => j.val < k) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  rw [← himg, Finset.sum_image hinj]

/-- Recursive-summation pre-rounding partial sums are compatible with taking a
prefix of the input list. -/
private lemma fl_partialSums_prefix_restrict_eq
    (fp : FPModel) {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (j : Fin i.val) :
    fl_partialSums fp
        (fun t : Fin i.val =>
          w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j =
      fl_partialSums fp w
        ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ := by
  simp [fl_partialSums]

/-- A prefix sum of absolute values of computed pre-rounding partial sums is
bounded by the full absolute sum. -/
private lemma fl_partialSums_prefix_abs_sum_le_total
    (fp : FPModel) {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin i.val,
        |fl_partialSums fp
          (fun t : Fin i.val =>
            w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
      ∑ j : Fin n, |fl_partialSums fp w j| := by
  classical
  have hprefix_eq :
      (∑ j : Fin i.val,
          |fl_partialSums fp
            (fun t : Fin i.val =>
              w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j|) =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
          (fun j => |fl_partialSums fp w j|) := by
    calc
      (∑ j : Fin i.val,
          |fl_partialSums fp
            (fun t : Fin i.val =>
              w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j|)
          =
            ∑ j : Fin i.val,
              |fl_partialSums fp w
                ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩| := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [fl_partialSums_prefix_restrict_eq]
      _ =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
          (fun j => |fl_partialSums fp w j|) := by
        simpa using
          (compensated_sum_fin_eq_sum_filter_lt (n := n) (k := i.val)
            (Nat.le_of_lt i.isLt) (fun j : Fin n => |fl_partialSums fp w j|))
  rw [hprefix_eq]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun j : Fin n => j.val < i.val) Finset.univ)
      (by
        intro j _hj _hnot
        exact abs_nonneg (fl_partialSums fp w j))

/-- Aggregate form of
`fl_partialSums_alternativeCompensatedCorrections_abs_le_exact_prefix_add_running_error`.

The sum of computed correction-list partials is bounded by the sum of exact
correction prefixes plus a self term coming from the recursive summation of
previous stored corrections. -/
theorem alternativeCompensatedCorrections_partialSums_abs_sum_le_exact_prefixes_plus_self
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∑ i : Fin n,
        |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| +
        (n : ℝ) * fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let total : ℝ := ∑ i : Fin n, |fl_partialSums fp corr i|
  let exactBudget : ℝ :=
    ∑ i : Fin n,
      |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j|
  have hpoint :
      ∀ i : Fin n,
        |fl_partialSums fp corr i| ≤
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| +
            fp.u * total := by
    intro i
    have hsplit :=
      fl_partialSums_alternativeCompensatedCorrections_abs_le_exact_prefix_add_running_error
        fp v i
    have hprefix :
        ∑ j : Fin i.val,
            |fl_partialSums fp
              (fun t : Fin i.val => corr
                ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
          total := by
      simpa [total, corr] using
        fl_partialSums_prefix_abs_sum_le_total fp corr i
    have hrun :
        fp.u *
            ∑ j : Fin i.val,
              |fl_partialSums fp
                (fun t : Fin i.val => corr
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
              fp.u * total :=
      mul_le_mul_of_nonneg_left hprefix fp.u_nonneg
    exact le_trans (by simpa [corr] using hsplit) (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hrun
          (|∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j|))
  calc
    ∑ i : Fin n, |fl_partialSums fp corr i|
        ≤ ∑ i : Fin n,
            (|∑ j : Fin (i.val + 1),
              alternativeCompensatedPrefixCorrection fp v (i.val + 1)
                (Nat.succ_le_of_lt i.isLt) j| + fp.u * total) := by
          exact Finset.sum_le_sum (fun i _hi => hpoint i)
    _ =
        exactBudget + (n : ℝ) * fp.u * total := by
          simp [exactBudget, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    _ =
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| +
        (n : ℝ) * fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| := by
      rfl

/-- Absorb the self term in
`alternativeCompensatedCorrections_partialSums_abs_sum_le_exact_prefixes_plus_self`.

Under the source smallness condition `n*u <= 1/10`, it suffices to bound the
exact correction-prefix aggregate by `0.9 * n^2*u*sum_i |x_i|` in order to
obtain the running-error budget required by the equation-(4.10) bridge. -/
theorem alternativeCompensatedCorrectionRunningErrorBudget_of_exact_prefix_budget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10)
    (hprefixBudget :
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| ≤
        (9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
          ∑ i : Fin n, |v i|) :
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := by
  let corr : Fin n → ℝ := alternativeCompensatedCorrections fp v
  let P : ℝ := ∑ i : Fin n, |fl_partialSums fp corr i|
  let E : ℝ :=
    ∑ i : Fin n,
      |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j|
  let S : ℝ := ∑ i : Fin n, |v i|
  have hP_nonneg : 0 ≤ P := by
    exact Finset.sum_nonneg fun i _hi => abs_nonneg (fl_partialSums fp corr i)
  have hsplit : P ≤ E + ((n : ℝ) * fp.u) * P := by
    simpa [P, E, corr, mul_assoc] using
      alternativeCompensatedCorrections_partialSums_abs_sum_le_exact_prefixes_plus_self
        fp v
  have hself_le : ((n : ℝ) * fp.u) * P ≤ (1 / 10 : ℝ) * P := by
    exact mul_le_mul_of_nonneg_right hsmall hP_nonneg
  have hE_lower : (9 / 10 : ℝ) * P ≤ E := by
    nlinarith
  have hP_le : P ≤ (10 / 9 : ℝ) * E := by
    nlinarith
  have hprefixBudget' :
      E ≤ (9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S := by
    simpa [E, S] using hprefixBudget
  have hscale :
      (10 / 9 : ℝ) * E ≤
        (10 / 9 : ℝ) *
          ((9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S) := by
    exact mul_le_mul_of_nonneg_left hprefixBudget' (by norm_num)
  calc
    fp.u * ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i|
        = fp.u * P := by rfl
    _ ≤ fp.u * ((10 / 9 : ℝ) * E) := by
      exact mul_le_mul_of_nonneg_left hP_le fp.u_nonneg
    _ ≤ fp.u *
          ((10 / 9 : ℝ) *
            ((9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S)) := by
      exact mul_le_mul_of_nonneg_left hscale fp.u_nonneg
    _ = ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := by
      simp [S]
      ring

/-- Under `k*u <= 0.1`, Higham's `gamma_k` is bounded by
`(10/9) * k*u`. -/
private lemma gamma_le_ten_ninth_mul_of_nu_le_tenth
    (fp : FPModel) (k : ℕ)
    (hsmall : (k : ℝ) * fp.u ≤ 1 / 10) :
    gamma fp k ≤ (10 / 9 : ℝ) * ((k : ℝ) * fp.u) := by
  set a : ℝ := (k : ℝ) * fp.u
  have ha_nonneg : 0 ≤ a := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le k) fp.u_nonneg
  have hden_pos : 0 < 1 - a := by
    nlinarith
  unfold gamma
  change a / (1 - a) ≤ (10 / 9 : ℝ) * a
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- Twice the sum of the zero-based `Fin n` indices is at most `n^2`. -/
private lemma two_mul_sum_fin_val_cast_le_sq (n : ℕ) :
    2 * (∑ i : Fin n, (i.val : ℝ)) ≤ (n : ℝ) ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp
      nlinarith

/-- The absolute source mass in a prefix is bounded by the full absolute source
mass. -/
private lemma alternativeCompensatedPrefix_input_abs_sum_le_total
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin (i.val + 1),
        |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
          (Nat.succ_le_of_lt i.isLt)⟩| ≤
      ∑ j : Fin n, |v j| := by
  classical
  have hprefix_eq :
      (∑ j : Fin (i.val + 1),
          |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt i.isLt)⟩|) =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val + 1) Finset.univ)
          (fun j => |v j|) := by
    simpa using
      (compensated_sum_fin_eq_sum_filter_lt (n := n) (k := i.val + 1)
        (Nat.succ_le_of_lt i.isLt) (fun j : Fin n => |v j|))
  rw [hprefix_eq]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun j : Fin n => j.val < i.val + 1) Finset.univ)
      (by
        intro j _hj _hnot
        exact abs_nonneg (v j))

/-- The exact correction-prefix aggregate is controlled by the usual
recursive-summation forward-error bound for each prefix.  Under `n*u <= 0.1`,
the aggregate is at most `(5/9) * n^2*u*sum_i |x_i|`. -/
theorem alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_five_ninth_n_sq_u
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
      (5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
        ∑ i : Fin n, |v i| := by
  let S : ℝ := ∑ i : Fin n, |v i|
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun i _hi => abs_nonneg (v i)
  have hpoint :
      ∀ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
          (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := by
    intro i
    have hi_le_n : (i.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt i.isLt
    have hi_small : (i.val : ℝ) * fp.u ≤ 1 / 10 := by
      exact le_trans (mul_le_mul_of_nonneg_right hi_le_n fp.u_nonneg) hsmall
    have hvalid_i : gammaValid fp i.val := by
      unfold gammaValid
      nlinarith
    have hprefix :=
      alternativeCompensatedPrefixCorrections_abs_le_recursiveSum_forward_of_full_exact
        fp v hexact i hvalid_i
    have hgamma_le :
        gamma fp i.val ≤ (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) :=
      gamma_le_ten_ninth_mul_of_nu_le_tenth fp i.val hi_small
    have hprefix_abs :
        ∑ j : Fin (i.val + 1),
            |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
              (Nat.succ_le_of_lt i.isLt)⟩| ≤ S := by
      simpa [S] using alternativeCompensatedPrefix_input_abs_sum_le_total v i
    have hprefix_abs_nonneg :
        0 ≤ ∑ j : Fin (i.val + 1),
            |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
              (Nat.succ_le_of_lt i.isLt)⟩| := by
      exact Finset.sum_nonneg fun j _hj => abs_nonneg _
    have hcoef_nonneg :
        0 ≤ (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg (by exact_mod_cast Nat.zero_le i.val) fp.u_nonneg)
    calc
      |∑ j : Fin (i.val + 1),
        alternativeCompensatedPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j|
          ≤ gamma fp i.val *
              ∑ j : Fin (i.val + 1),
                |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                  (Nat.succ_le_of_lt i.isLt)⟩| := hprefix
      _ ≤ ((10 / 9 : ℝ) * ((i.val : ℝ) * fp.u)) *
              ∑ j : Fin (i.val + 1),
                |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                  (Nat.succ_le_of_lt i.isLt)⟩| := by
            exact mul_le_mul_of_nonneg_right hgamma_le hprefix_abs_nonneg
      _ ≤ ((10 / 9 : ℝ) * ((i.val : ℝ) * fp.u)) * S := by
            exact mul_le_mul_of_nonneg_left hprefix_abs hcoef_nonneg
      _ = (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := by
            ring
  have hsum :
      ∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            alternativeCompensatedPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| ≤
        ∑ i : Fin n, (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := by
    exact Finset.sum_le_sum (fun i _hi => hpoint i)
  have hsum_simplified :
      ∑ i : Fin n, (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S =
        (10 / 9 : ℝ) * fp.u * S *
          ∑ i : Fin n, (i.val : ℝ) := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hidx_le : ∑ i : Fin n, (i.val : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    have htwo := two_mul_sum_fin_val_cast_le_sq n
    nlinarith
  have hcoef_nonneg : 0 ≤ (10 / 9 : ℝ) * fp.u * S := by
    exact mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hS_nonneg
  have hweighted :
      (10 / 9 : ℝ) * fp.u * S *
          ∑ i : Fin n, (i.val : ℝ) ≤
        (10 / 9 : ℝ) * fp.u * S * ((n : ℝ) ^ 2 / 2) := by
    exact mul_le_mul_of_nonneg_left hidx_le hcoef_nonneg
  calc
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j|
        ≤ ∑ i : Fin n, (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := hsum
    _ = (10 / 9 : ℝ) * fp.u * S *
          ∑ i : Fin n, (i.val : ℝ) := hsum_simplified
    _ ≤ (10 / 9 : ℝ) * fp.u * S * ((n : ℝ) ^ 2 / 2) := hweighted
    _ = (5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
          ∑ i : Fin n, |v i| := by
      simp [S]
      ring

/-- Exact correction-prefix aggregate in the form required by the self-term
absorption lemma. -/
theorem alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_nine_tenths_n_sq_u
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          alternativeCompensatedPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
      (9 / 10 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
        ∑ i : Fin n, |v i| := by
  have hbase_nonneg :
      0 ≤ ((n : ℝ) ^ 2 * fp.u) * ∑ i : Fin n, |v i| := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg (n : ℝ)) fp.u_nonneg)
      (Finset.sum_nonneg fun i _hi => abs_nonneg (v i))
  exact le_trans
    (alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_five_ninth_n_sq_u
      fp n v hexact hsmall)
    (by nlinarith)

/-- Fully proved running-error budget for the correction list in the
alternative compensated-summation equation-(4.10) route. -/
theorem alternativeCompensatedCorrectionRunningErrorBudget_of_exact_steps
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (alternativeCompensatedCorrections fp v) i| ≤
      ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := by
  exact
    alternativeCompensatedCorrectionRunningErrorBudget_of_exact_prefix_budget
      fp n v hsmall
      (alternativeCompensatedCorrectionExactPrefixes_abs_sum_le_nine_tenths_n_sq_u
        fp n v hexact hsmall)

/-- If each local correction formula is exact, the recursive accumulation of
stored corrections is exact, and the final main-plus-correction add is exact,
then the printed p. 85 alternative compensated-summation value equals the exact source
sum. -/
theorem fl_alternativeCompensatedSum_eq_sum_of_exact_steps_and_exact_correction_sum
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hexact :
      ∀ i : Fin n,
        let sum := alternativeCompensatedPrefixSum fp v i.val
          (Nat.le_of_lt i.isLt)
        let trace := alternativeCompensatedStepTrace fp (v i) sum
        CorrectionFormulaTrace.exact sum (v i)
          ({ s := trace.s, e := trace.e } : CorrectionFormulaTrace))
    (hglobal :
      fl_alternativeCompensatedGlobalCorrection fp n v =
        ∑ i : Fin n, alternativeCompensatedCorrections fp v i)
    (hfinal :
      fp.fl_add (fl_alternativeCompensatedMainSum fp n v)
          (fl_alternativeCompensatedGlobalCorrection fp n v) =
        fl_alternativeCompensatedMainSum fp n v +
          fl_alternativeCompensatedGlobalCorrection fp n v) :
    fl_alternativeCompensatedSum fp n v = ∑ i : Fin n, v i := by
  rw [fl_alternativeCompensatedSum_eq_add_globalCorrection, hfinal, hglobal]
  exact
    fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
      fp n v hexact

/-- Under exact arithmetic, the main sum in the printed p. 85 alternative compensated
variant is the exact source sum. -/
theorem fl_alternativeCompensatedMainSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      fl_alternativeCompensatedMainSum
          (FPModel.exactWithUnitRoundoff u0 hu0) n v =
        ∑ i : Fin n, v i
  | 0, _v => by
      simp [fl_alternativeCompensatedMainSum,
        alternativeCompensatedPrefixSum]
  | n + 1, v => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_alternativeCompensatedMainSum fp (n + 1) v =
            (alternativeCompensatedStepTrace fp (v (Fin.last n))
              (fl_alternativeCompensatedMainSum fp n
                (fun i : Fin n => v i.castSucc))).nextSum := by
        unfold fl_alternativeCompensatedMainSum
          alternativeCompensatedPrefixSum
        rw [Fin.foldl_succ_last]
      rw [hfold,
        fl_alternativeCompensatedMainSum_exactWithUnitRoundoff u0 hu0 n
          (fun i : Fin n => v i.castSucc)]
      simp [fp, alternativeCompensatedStepTrace,
        AlternativeCompensatedStepTrace.nextSum,
        FPModel.exactWithUnitRoundoff, Fin.sum_univ_castSucc, add_comm]

/-- Under exact arithmetic, every stored local correction in the printed p. 85
alternative variant is zero. -/
theorem alternativeCompensatedCorrections_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) {n : ℕ} (v : Fin n → ℝ) :
    ∀ i : Fin n,
      alternativeCompensatedCorrections
          (FPModel.exactWithUnitRoundoff u0 hu0) v i = 0 := by
  intro i
  simp [alternativeCompensatedCorrections, alternativeCompensatedTrace,
    alternativeCompensatedStepTrace, FPModel.exactWithUnitRoundoff]

/-- Under exact arithmetic, the recursively accumulated global correction in
the printed p. 85 alternative variant is zero. -/
theorem fl_alternativeCompensatedGlobalCorrection_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedGlobalCorrection
        (FPModel.exactWithUnitRoundoff u0 hu0) n v = 0 := by
  rw [fl_alternativeCompensatedGlobalCorrection_eq_recursiveSum]
  rw [fl_recursiveSum_exactWithUnitRoundoff]
  simp [alternativeCompensatedCorrections_exactWithUnitRoundoff u0 hu0 v]

/-- Under exact arithmetic, the printed p. 85 alternative compensated-summation
variant returns the exact source sum. -/
theorem fl_alternativeCompensatedSum_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_alternativeCompensatedSum
        (FPModel.exactWithUnitRoundoff u0 hu0) n v =
      ∑ i : Fin n, v i := by
  rw [fl_alternativeCompensatedSum_eq_add_globalCorrection,
    fl_alternativeCompensatedMainSum_exactWithUnitRoundoff u0 hu0,
    fl_alternativeCompensatedGlobalCorrection_exactWithUnitRoundoff u0 hu0]
  simp [FPModel.exactWithUnitRoundoff]

end NumStability
