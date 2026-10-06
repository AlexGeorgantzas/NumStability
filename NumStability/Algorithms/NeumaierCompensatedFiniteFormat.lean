import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

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

private theorem neumaier_gamma_le_ten_ninth_mul_of_nu_le_tenth
    (fp : FPModel) (k : ℕ)
    (hsmall : (k : ℝ) * fp.u ≤ 1 / 10) :
    gamma fp k ≤ (10 / 9 : ℝ) * ((k : ℝ) * fp.u) := by
  set a : ℝ := (k : ℝ) * fp.u
  have ha : 0 ≤ a :=
    mul_nonneg (by exact_mod_cast Nat.zero_le k) fp.u_nonneg
  have hden : 0 < 1 - a := by nlinarith
  unfold gamma
  change a / (1 - a) ≤ (10 / 9 : ℝ) * a
  rw [div_le_iff₀ hden]
  nlinarith

private theorem neumaier_two_mul_sum_fin_val_cast_le_sq (n : ℕ) :
    2 * (∑ i : Fin n, (i.val : ℝ)) ≤ (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp
      nlinarith

private theorem neumaier_prefix_abs_le_total
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin (i.val + 1),
        |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
          (Nat.succ_le_of_lt i.isLt)⟩| ≤
      ∑ j : Fin n, |v j| := by
  classical
  let emb : Fin (i.val + 1) → Fin n := fun j =>
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩
  have hinj : Function.Injective emb := by
    intro a b hab
    apply Fin.ext
    simpa [emb] using congrArg Fin.val hab
  change (∑ j : Fin (i.val + 1), |v (emb j)|) ≤ ∑ j : Fin n, |v j|
  have himage :
      (∑ j : Fin (i.val + 1), |v (emb j)|) =
        Finset.sum (Finset.image emb Finset.univ) (fun j => |v j|) := by
    symm
    exact Finset.sum_image (fun a _ b _ hab => hinj hab)
  rw [himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _))
    (by intro j _ _; exact abs_nonneg (v j))

/-- Aggregate exact residual-prefix bound used by the correction-summation
running-error estimate. -/
theorem recursiveSumCorrectionExactPrefixes_abs_sum_le_five_ninth
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
      (5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
        ∑ i : Fin n, |v i| := by
  let S : ℝ := ∑ i : Fin n, |v i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  have hpoint : ∀ i : Fin n,
      |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| ≤
        (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := by
    intro i
    have hi : (i.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt i.isLt
    have hismall : (i.val : ℝ) * fp.u ≤ 1 / 10 :=
      le_trans (mul_le_mul_of_nonneg_right hi fp.u_nonneg) hsmall
    have hvalid : gammaValid fp i.val := by
      unfold gammaValid
      nlinarith
    have hforward := recursiveSumPrefixCorrections_abs_le_forward fp v
      (i.val + 1) (Nat.succ_le_of_lt i.isLt) hvalid
    have hgamma : gamma fp i.val ≤
        (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) :=
      neumaier_gamma_le_ten_ninth_mul_of_nu_le_tenth fp i.val hismall
    have hpref := neumaier_prefix_abs_le_total v i
    have hpref0 : 0 ≤ ∑ j : Fin (i.val + 1),
        |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
          (Nat.succ_le_of_lt i.isLt)⟩| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hcoef : 0 ≤ (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (by exact_mod_cast Nat.zero_le i.val) fp.u_nonneg)
    calc
      |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j|
          ≤ gamma fp i.val *
              ∑ j : Fin (i.val + 1),
                |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                  (Nat.succ_le_of_lt i.isLt)⟩| := by
            simpa [Nat.add_sub_cancel] using hforward
      _ ≤ ((10 / 9 : ℝ) * ((i.val : ℝ) * fp.u)) *
              ∑ j : Fin (i.val + 1),
                |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                  (Nat.succ_le_of_lt i.isLt)⟩| :=
            mul_le_mul_of_nonneg_right hgamma hpref0
      _ ≤ ((10 / 9 : ℝ) * ((i.val : ℝ) * fp.u)) * S :=
            mul_le_mul_of_nonneg_left (by simpa [S] using hpref) hcoef
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hidx := neumaier_two_mul_sum_fin_val_cast_le_sq n
  calc
    ∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j|
        ≤ ∑ i : Fin n,
            (10 / 9 : ℝ) * ((i.val : ℝ) * fp.u) * S := hsum
    _ = (10 / 9 : ℝ) * fp.u * S *
          ∑ i : Fin n, (i.val : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ (10 / 9 : ℝ) * fp.u * S * ((n : ℝ) ^ 2 / 2) := by
        exact mul_le_mul_of_nonneg_left (by nlinarith)
          (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hS)
    _ = (5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) *
          ∑ i : Fin n, |v i| := by simp [S]; ring

private theorem neumaier_fl_partialSums_restrict_eq
    (fp : FPModel) {n : ℕ} (w : Fin n → ℝ)
    (i : Fin n) (j : Fin i.val) :
    fl_partialSums fp
        (fun t : Fin i.val => w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j =
      fl_partialSums fp w
        ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ := by
  unfold fl_partialSums
  congr 1

private theorem neumaier_partialSums_prefix_abs_le_total
    (fp : FPModel) {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin i.val,
        |fl_partialSums fp
          (fun t : Fin i.val =>
            w ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
      ∑ j : Fin n, |fl_partialSums fp w j| := by
  classical
  simp_rw [neumaier_fl_partialSums_restrict_eq]
  let emb : Fin i.val → Fin n := fun j =>
    ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  have hinj : Function.Injective emb := by
    intro a b hab
    apply Fin.ext
    simpa [emb] using congrArg Fin.val hab
  change (∑ j : Fin i.val, |fl_partialSums fp w (emb j)|) ≤
    ∑ j : Fin n, |fl_partialSums fp w j|
  have himage :
      (∑ j : Fin i.val, |fl_partialSums fp w (emb j)|) =
        Finset.sum (Finset.image emb Finset.univ)
          (fun j => |fl_partialSums fp w j|) := by
    symm
    exact Finset.sum_image (fun a _ b _ hab => hinj hab)
  rw [himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _))
    (by intro j _ _; exact abs_nonneg (fl_partialSums fp w j))

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

/-- Sum of computed residual-list partial sums, with the recursive self term
left explicit. -/
theorem localCorrections_partialSums_abs_sum_le_exactPrefixes_plus_self
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    ∑ i : Fin n,
        |fl_partialSums fp (recursiveSumLocalCorrection fp v) i| ≤
      (∑ i : Fin n,
        |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j|) +
        (n : ℝ) * fp.u *
          ∑ i : Fin n,
            |fl_partialSums fp (recursiveSumLocalCorrection fp v) i| := by
  let corr : Fin n → ℝ := recursiveSumLocalCorrection fp v
  let P : ℝ := ∑ i : Fin n, |fl_partialSums fp corr i|
  have hpoint : ∀ i : Fin n,
      |fl_partialSums fp corr i| ≤
        |∑ j : Fin (i.val + 1),
          recursiveSumPrefixCorrection fp v (i.val + 1)
            (Nat.succ_le_of_lt i.isLt) j| + fp.u * P := by
    intro i
    have hsplit :=
      fl_partialSums_localCorrections_abs_le_exactPrefix_add_runningError fp v i
    have hpref := neumaier_partialSums_prefix_abs_le_total fp corr i
    have hrun := mul_le_mul_of_nonneg_left hpref fp.u_nonneg
    have hsplit' :
        |fl_partialSums fp corr i| ≤
          |∑ j : Fin (i.val + 1),
            recursiveSumPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j| +
            fp.u *
              ∑ j : Fin i.val,
                |fl_partialSums fp
                  (fun t : Fin i.val => corr
                    ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| := by
      simpa [corr] using hsplit
    have hrun' :
        fp.u *
            ∑ j : Fin i.val,
              |fl_partialSums fp
                (fun t : Fin i.val => corr
                  ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩) j| ≤
          fp.u * P := by
      simpa [P] using hrun
    exact hsplit'.trans (add_le_add (le_refl _) hrun')
  calc
    ∑ i : Fin n, |fl_partialSums fp (recursiveSumLocalCorrection fp v) i|
        ≤ ∑ i : Fin n,
            (|∑ j : Fin (i.val + 1),
              recursiveSumPrefixCorrection fp v (i.val + 1)
                (Nat.succ_le_of_lt i.isLt) j| + fp.u * P) :=
          Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i : Fin n,
          |∑ j : Fin (i.val + 1),
            recursiveSumPrefixCorrection fp v (i.val + 1)
              (Nat.succ_le_of_lt i.isLt) j|) +
          (n : ℝ) * fp.u *
            ∑ i : Fin n,
              |fl_partialSums fp (recursiveSumLocalCorrection fp v) i| := by
        simp [P, corr, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The exact `n²u²` running-error budget for recursively accumulating the
canonical exact residuals, under Higham's `nu ≤ 0.1` proviso. -/
theorem recursiveSumLocalCorrections_runningErrorBudget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (recursiveSumLocalCorrection fp v) i| ≤
      ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := by
  let P : ℝ :=
    ∑ i : Fin n, |fl_partialSums fp (recursiveSumLocalCorrection fp v) i|
  let E : ℝ :=
    ∑ i : Fin n,
      |∑ j : Fin (i.val + 1),
        recursiveSumPrefixCorrection fp v (i.val + 1)
          (Nat.succ_le_of_lt i.isLt) j|
  let S : ℝ := ∑ i : Fin n, |v i|
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hsplit : P ≤ E + ((n : ℝ) * fp.u) * P := by
    simpa [P, E] using
      localCorrections_partialSums_abs_sum_le_exactPrefixes_plus_self fp n v
  have hself : ((n : ℝ) * fp.u) * P ≤ (1 / 10 : ℝ) * P :=
    mul_le_mul_of_nonneg_right hsmall hP
  have hP_le : P ≤ (10 / 9 : ℝ) * E := by nlinarith
  have hE : E ≤ (5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S := by
    simpa [E, S] using
      recursiveSumCorrectionExactPrefixes_abs_sum_le_five_ninth fp n v hsmall
  have hscale : (10 / 9 : ℝ) * E ≤
      (10 / 9 : ℝ) *
        ((5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S) :=
    mul_le_mul_of_nonneg_left hE (by norm_num)
  have hrelax : (50 / 81 : ℝ) ≤ 1 := by norm_num
  have hbase : 0 ≤ ((n : ℝ) ^ 2 * fp.u ^ 2) * S :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  calc
    fp.u *
        ∑ i : Fin n,
          |fl_partialSums fp (recursiveSumLocalCorrection fp v) i|
        = fp.u * P := rfl
    _ ≤ fp.u * ((10 / 9 : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hP_le fp.u_nonneg
    _ ≤ fp.u * ((10 / 9 : ℝ) *
          ((5 / 9 : ℝ) * ((n : ℝ) ^ 2 * fp.u) * S)) :=
      mul_le_mul_of_nonneg_left hscale fp.u_nonneg
    _ = (50 / 81 : ℝ) * (((n : ℝ) ^ 2 * fp.u ^ 2) * S) := by ring
    _ ≤ ((n : ℝ) ^ 2 * fp.u ^ 2) * S :=
      mul_le_of_le_one_left hbase hrelax
    _ = ((n : ℝ) ^ 2 * fp.u ^ 2) * ∑ i : Fin n, |v i| := rfl

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

/-- Higham (4.10), at the canonical exact-residual level.  No local
exactness/order hypothesis remains: the corrections are the exact residuals
that the finite magnitude-adaptive executor below is proved to produce. -/
theorem fl_recursiveResidualCorrectedSum_backward_error_higham410
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (n : ℝ) ^ 2 * fp.u ^ 2) ∧
      fl_recursiveResidualCorrectedSum fp n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let C : ℝ := (n : ℝ) ^ 2 * fp.u ^ 2
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  obtain ⟨μ, hμ, hsum⟩ :=
    fl_recursiveResidualCorrectedSum_backward_error_of_budget fp n v hC
      (by
        simpa [C] using
          recursiveSumLocalCorrections_runningErrorBudget fp n v hsmall)
  have hC_le : C ≤ 1 := by
    have hnu : 0 ≤ (n : ℝ) * fp.u :=
      mul_nonneg (by exact_mod_cast Nat.zero_le n) fp.u_nonneg
    have hsquare : ((n : ℝ) * fp.u) ^ 2 ≤ (1 / 10 : ℝ) ^ 2 :=
      sq_le_sq' (by nlinarith [hnu]) hsmall
    change (n : ℝ) ^ 2 * fp.u ^ 2 ≤ 1
    nlinarith [hsquare]
  have hcap : fp.u + C + C * fp.u ≤ 2 * fp.u + C := by
    have := mul_le_mul_of_nonneg_right hC_le fp.u_nonneg
    nlinarith
  exact ⟨μ, fun i => le_trans (hμ i) (by simpa [C] using hcap), hsum⟩

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

/-- **Higham equation (4.10), closed on an actual magnitude-adaptive finite
binary trace.**  The only trace premise is the source's no-exception scope:
stored operands and normal/exact main additions.  The adaptive branch itself
produces the required FastTwoSum magnitude order. -/
theorem neumaierFF_backward_error_higham410
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hstep : ∀ i : Fin n,
      neumaierFF_stepCondition fmt (neumaierFF_prefix fmt v i) (v i))
    (hsmall : (n : ℝ) * fmt.unitRoundoff ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fmt.unitRoundoff + (n : ℝ) ^ 2 * fmt.unitRoundoff ^ 2) ∧
      neumaierFF_sum fmt n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  have hcanon :=
    fl_recursiveResidualCorrectedSum_backward_error_higham410
      (kahanFF_model fmt) n v (by simpa using hsmall)
  rw [neumaierFF_sum_eq_recursiveResidualCorrectedSum
    fmt hbeta ht n v hstep]
  simpa using hcanon

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

/-- **Higham (4.10) for a literal finite binary executor.**  All arithmetic in
`neumaierFinite_sum` is `finiteRoundToEvenOp`; the hypotheses state precisely
that its main, correction-accumulation, and final additions stay in the
source/no-exception region. -/
theorem neumaierFinite_backward_error_higham410
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
        (neumaierFinite_corrections fmt v)))
    (hsmall : (n : ℝ) * fmt.unitRoundoff ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fmt.unitRoundoff + (n : ℝ) ^ 2 * fmt.unitRoundoff ^ 2) ∧
      neumaierFinite_sum fmt n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  have hsafe := neumaierFF_backward_error_higham410
    fmt hbeta ht n v hmain hsmall
  rw [neumaierFinite_sum_eq_neumaierFF_sum
    fmt hbeta ht n v hmain hcorr hfinal]
  exact hsafe

end NumStability
