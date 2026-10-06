import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.Compensated.Neumaier.AdaptiveFiniteFormat
import NumStability.Algorithms.Summation.Compensated.Neumaier.ExactResidual
import NumStability.Algorithms.Summation.Compensated.Neumaier.FiniteExecutor
import NumStability.Algorithms.Summation.Recursive.Core








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
