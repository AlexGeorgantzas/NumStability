-- Algorithms/DotProduct.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.Rounding
import NumStability.Analysis.RoundingProductBounds
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Analysis.Stability

namespace NumStability

open scoped BigOperators

/-- Floating-point dot product of two n-dimensional vectors.

    Models Higham's sequential accumulation in §3.1:
      ŝ₁    = fl_mul (x 0) (y 0)
      ŝᵢ₊₁ = fl_add ŝᵢ (fl_mul (x i) (y i)),  i = 1, …, n-1

    Starting from the first rounded product (rather than 0) avoids the
    spurious extra rounding error that would arise from fl_add(0, fl_mul …),
    allowing the tight γₙ bound of Higham §3.1. -/
noncomputable def fl_dotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0      => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

/-- Combined local factor attached to each term in a positive-length
left-to-right dot product.

Term `0` carries its multiplication factor and all addition factors.  Term
`i.succ` carries its multiplication factor and the suffix of addition factors
from the accumulation step where it enters. -/
noncomputable def dotProductLocalFactor (n : ℕ)
    (mulDelta : Fin (n + 1) → ℝ) (addDelta : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.cases ((1 + mulDelta 0) * (∏ i : Fin n, (1 + addDelta i)))
    (fun i => (1 + mulDelta i.succ) * sumSuffixErrorProduct n addDelta i)

/-- **Dot-product local-factor expansion** (Higham §3.1, equations
(3.1)--(3.2)).

For a positive-length left-to-right dot product, expose the actual local
multiplication factors and local addition factors instead of immediately
compressing them into `gamma` witnesses.  The first product term carries every
addition factor; term `i.succ` carries the suffix of addition factors from the
step where that term enters the accumulator.

This is the source-shaped expansion used before deriving the backward and
forward dot-product error bounds. -/
theorem dotProduct_factor_expansion_succ (fp : FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    ∃ mulDelta : Fin (n + 1) → ℝ, ∃ addDelta : Fin n → ℝ,
      (∀ i, |mulDelta i| ≤ fp.u) ∧
      (∀ i, |addDelta i| ≤ fp.u) ∧
      fl_dotProduct fp (n + 1) x y =
        x 0 * y 0 * (1 + mulDelta 0) *
            (∏ i : Fin n, (1 + addDelta i)) +
          ∑ i : Fin n,
            x i.succ * y i.succ * (1 + mulDelta i.succ) *
              sumSuffixErrorProduct n addDelta i := by
  let mulDelta : Fin (n + 1) → ℝ :=
    fun i => Classical.choose (fp.model_mul (x i) (y i))
  have hmul :
      ∀ i,
        |mulDelta i| ≤ fp.u ∧
          fp.fl_mul (x i) (y i) = x i * y i * (1 + mulDelta i) :=
    fun i => Classical.choose_spec (fp.model_mul (x i) (y i))
  obtain ⟨addDelta, hadd, hfold⟩ :=
    fl_sum_error_init_suffix_expansion fp n
      (fun i => fp.fl_mul (x i.succ) (y i.succ))
      (fp.fl_mul (x 0) (y 0))
  refine ⟨mulDelta, addDelta, (fun i => (hmul i).1), hadd, ?_⟩
  show
    Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0)) =
      x 0 * y 0 * (1 + mulDelta 0) * (∏ i : Fin n, (1 + addDelta i)) +
        ∑ i : Fin n,
          x i.succ * y i.succ * (1 + mulDelta i.succ) *
            sumSuffixErrorProduct n addDelta i
  rw [hfold, (hmul 0).2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hmul i.succ).2]

/-- Single-sum form of `dotProduct_factor_expansion_succ`. -/
theorem dotProduct_factor_expansion_sum_succ (fp : FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    ∃ mulDelta : Fin (n + 1) → ℝ, ∃ addDelta : Fin n → ℝ,
      (∀ i, |mulDelta i| ≤ fp.u) ∧
      (∀ i, |addDelta i| ≤ fp.u) ∧
      fl_dotProduct fp (n + 1) x y =
        ∑ i : Fin (n + 1),
          x i * y i * dotProductLocalFactor n mulDelta addDelta i := by
  obtain ⟨mulDelta, addDelta, hmul, hadd, hfl⟩ :=
    dotProduct_factor_expansion_succ fp n x y
  refine ⟨mulDelta, addDelta, hmul, hadd, ?_⟩
  rw [hfl, Fin.sum_univ_succ]
  simp [dotProductLocalFactor]
  ring_nf

/-- Every combined local factor in a positive-length dot product has the
Higham Lemma 3.4 small-`nu` radius.

The theorem uses the repository's non-strict primitive model surface
`|delta| <= u`, hence the explicit `0 < u` hypothesis and the non-strict
`<=` conclusion. -/
theorem dotProductLocalFactor_abs_sub_one_le_101 (n : ℕ) {u : ℝ}
    (hu_pos : 0 < u)
    (mulDelta : Fin (n + 1) → ℝ) (addDelta : Fin n → ℝ)
    (hmul : ∀ i, |mulDelta i| ≤ u)
    (hadd : ∀ i, |addDelta i| ≤ u)
    (hnu : ((n + 1 : ℕ) : ℝ) * u < (1 / 100 : ℝ)) :
    ∀ i : Fin (n + 1),
      |dotProductLocalFactor n mulDelta addDelta i - 1| ≤
        (101 / 100 : ℝ) * ((n + 1 : ℕ) : ℝ) * u := by
  intro i
  refine Fin.cases ?_ ?_ i
  · let deltaTerm : Fin (n + 1) → ℝ := Fin.cases (mulDelta 0) addDelta
    have hdelta : ∀ j : Fin (n + 1), |deltaTerm j| ≤ u := by
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa [deltaTerm] using hmul 0
      · intro k
        simpa [deltaTerm] using hadd k
    obtain ⟨eta, heta, hprod⟩ :=
      prod_one_add_delta_eq_one_add_eta_bound_101_le (n + 1)
        (Nat.succ_pos n) hu_pos deltaTerm hdelta hnu
    have hfactor :
        dotProductLocalFactor n mulDelta addDelta 0 = 1 + eta := by
      rw [← hprod]
      simp [dotProductLocalFactor, deltaTerm, Fin.prod_univ_succ]
    rw [hfactor]
    simpa using le_of_lt heta
  · intro i
    let deltaTerm : Fin (n + 1) → ℝ :=
      Fin.cases (mulDelta i.succ)
        (fun j => if i.val ≤ j.val then addDelta j else 0)
    have hdelta : ∀ j : Fin (n + 1), |deltaTerm j| ≤ u := by
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa [deltaTerm] using hmul i.succ
      · intro k
        by_cases hik : i ≤ k
        · simpa [deltaTerm, hik] using hadd k
        · have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
          simpa [deltaTerm, hik] using hu_nonneg
    obtain ⟨eta, heta, hprod⟩ :=
      prod_one_add_delta_eq_one_add_eta_bound_101_le (n + 1)
        (Nat.succ_pos n) hu_pos deltaTerm hdelta hnu
    have hfactor :
        dotProductLocalFactor n mulDelta addDelta i.succ = 1 + eta := by
      have hsuffix :
          (∏ x : Fin n, (1 + if i ≤ x then addDelta x else 0)) =
            sumSuffixErrorProduct n addDelta i := by
        rw [sumSuffixErrorProduct_eq_prod_if]
        apply Finset.prod_congr rfl
        intro x _hx
        by_cases hix : i ≤ x <;> simp [hix]
      calc
        dotProductLocalFactor n mulDelta addDelta i.succ =
            (1 + mulDelta i.succ) * sumSuffixErrorProduct n addDelta i := by
              simp [dotProductLocalFactor]
        _ =
            (1 + mulDelta i.succ) *
              (∏ x : Fin n, (1 + if i ≤ x then addDelta x else 0)) := by
              rw [hsuffix]
        _ = ∏ x : Fin (n + 1), (1 + deltaTerm x) := by
              simp [deltaTerm, Fin.prod_univ_succ]
        _ = 1 + eta := hprod
    rw [hfactor]
    simpa using le_of_lt heta

/-- **Small-`nu` dot-product forward bound** (Higham §3.4, equation (3.9)).

For the repository's non-strict `FPModel`, the result is stated with `<=`.
The source's displayed strict inequality follows in the usual nondegenerate
strict-local-error regime. -/
theorem dotProduct_error_bound_101_succ (fp : FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ)
    (hu_pos : 0 < fp.u)
    (hnu : ((n + 1 : ℕ) : ℝ) * fp.u < (1 / 100 : ℝ)) :
    |fl_dotProduct fp (n + 1) x y - ∑ i : Fin (n + 1), x i * y i| ≤
      (101 / 100 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u *
        ∑ i : Fin (n + 1), |x i| * |y i| := by
  obtain ⟨mulDelta, addDelta, hmul, hadd, hfl⟩ :=
    dotProduct_factor_expansion_sum_succ fp n x y
  let K : ℝ := (101 / 100 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u
  have hK_nonneg : 0 ≤ K := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le (n + 1)))
      (le_of_lt hu_pos)
  have hfactor :
      ∀ i : Fin (n + 1),
        |dotProductLocalFactor n mulDelta addDelta i - 1| ≤ K := by
    simpa [K] using
      dotProductLocalFactor_abs_sub_one_le_101 n hu_pos mulDelta addDelta hmul hadd hnu
  have herr :
      fl_dotProduct fp (n + 1) x y - ∑ i : Fin (n + 1), x i * y i =
        ∑ i : Fin (n + 1),
          x i * y i * (dotProductLocalFactor n mulDelta addDelta i - 1) := by
    rw [hfl, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr]
  calc
    |∑ i : Fin (n + 1),
        x i * y i * (dotProductLocalFactor n mulDelta addDelta i - 1)|
        ≤ ∑ i : Fin (n + 1),
            |x i * y i * (dotProductLocalFactor n mulDelta addDelta i - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (n + 1),
            |x i| * |y i| *
              |dotProductLocalFactor n mulDelta addDelta i - 1| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_mul]
    _ ≤ ∑ i : Fin (n + 1), |x i| * |y i| * K := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hfactor i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = K * ∑ i : Fin (n + 1), |x i| * |y i| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ =
        (101 / 100 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u *
          ∑ i : Fin (n + 1), |x i| * |y i| := by
          rfl

-- ============================================================
-- §3.3  Running error analysis core
-- ============================================================

/-- The exact accumulator used by Higham Algorithm 3.2 before the final
scaling by unit roundoff: `sum_i (|sHat_i| + |zHat_i|)`. -/
noncomputable def runningErrorMu (n : ℕ) (sHat zHat : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => acc + |sHat i| + |zHat i|) 0

/-- Rounded product stored at iteration `i` of Higham Algorithm 3.2. -/
noncomputable def fl_runningDotProductProduct (fp : FPModel) {n : ℕ}
    (x y : Fin n → ℝ) (i : Fin n) : ℝ :=
  fp.fl_mul (x i) (y i)

/-- Exact prefix dot product for the first `k` entries, written recursively so
it matches the loop invariant used in the running-error proof. -/
noncomputable def exactDotProductPrefixNat {n : ℕ} (x y : Fin n → ℝ) :
    (k : ℕ) → k ≤ n → ℝ
  | 0, _ => 0
  | k + 1, hk =>
      exactDotProductPrefixNat x y k (Nat.le_of_succ_le hk) +
        x ⟨k, Nat.lt_of_succ_le hk⟩ * y ⟨k, Nat.lt_of_succ_le hk⟩
termination_by k _ => k

/-- Computed prefix accumulator for the first `k` entries of Algorithm 3.2:
`s = 0; z = fl(x_i*y_i); s = fl(s+z)`. -/
noncomputable def fl_runningDotProductPrefixNat (fp : FPModel) {n : ℕ}
    (x y : Fin n → ℝ) : (k : ℕ) → k ≤ n → ℝ
  | 0, _ => 0
  | k + 1, hk =>
      fp.fl_add
        (fl_runningDotProductPrefixNat fp x y k (Nat.le_of_succ_le hk))
        (fl_runningDotProductProduct fp x y ⟨k, Nat.lt_of_succ_le hk⟩)
termination_by k _ => k

/-- Exact prefix state indexed by `Fin (n+1)`, where index `k` denotes the
state after `k` loop iterations. -/
noncomputable def exactDotProductPrefixState {n : ℕ} (x y : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  fun k => exactDotProductPrefixNat x y k.val (Nat.le_of_lt_succ k.isLt)

/-- Computed prefix state indexed by `Fin (n+1)`, where index `k` denotes the
stored accumulator after `k` loop iterations. -/
noncomputable def fl_runningDotProductState (fp : FPModel) {n : ℕ}
    (x y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun k => fl_runningDotProductPrefixNat fp x y k.val (Nat.le_of_lt_succ k.isLt)

/-- Higham Algorithm 3.2's computed dot product accumulator after all `n`
iterations. -/
noncomputable def fl_runningDotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  fl_runningDotProductPrefixNat fp x y n le_rfl

@[simp] theorem exactDotProductPrefixState_zero {n : ℕ}
    (x y : Fin n → ℝ) :
    exactDotProductPrefixState x y 0 = 0 := by
  simp [exactDotProductPrefixState, exactDotProductPrefixNat]

@[simp] theorem fl_runningDotProductState_zero (fp : FPModel) {n : ℕ}
    (x y : Fin n → ℝ) :
    fl_runningDotProductState fp x y 0 = 0 := by
  simp [fl_runningDotProductState, fl_runningDotProductPrefixNat]

/-- Exact prefix recurrence for the next source product. -/
theorem exactDotProductPrefixState_succ {n : ℕ} (x y : Fin n → ℝ)
    (i : Fin n) :
    exactDotProductPrefixState x y i.succ =
      exactDotProductPrefixState x y i.castSucc + x i * y i := by
  cases i with
  | mk i hi =>
      simp [exactDotProductPrefixState, exactDotProductPrefixNat]

/-- Computed prefix recurrence for the next rounded product and rounded
addition in Algorithm 3.2. -/
theorem fl_runningDotProductState_succ (fp : FPModel) {n : ℕ}
    (x y : Fin n → ℝ) (i : Fin n) :
    fl_runningDotProductState fp x y i.succ =
      fp.fl_add (fl_runningDotProductState fp x y i.castSucc)
        (fl_runningDotProductProduct fp x y i) := by
  cases i with
  | mk i hi =>
      simp [fl_runningDotProductState, fl_runningDotProductPrefixNat,
        fl_runningDotProductProduct]

/-- Recursive exact prefixes agree with the ordinary finite dot-product sum. -/
theorem exactDotProductPrefixNat_eq_sum_prefix {n : ℕ} (x y : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      exactDotProductPrefixNat x y k hk =
        ∑ i : Fin k,
          x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ *
            y ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [exactDotProductPrefixNat]
  | succ k ih =>
      intro hk
      rw [exactDotProductPrefixNat, ih (Nat.le_of_succ_le hk),
        Fin.sum_univ_castSucc]
      simp

/-- The final exact prefix state is the source dot product `x^T y`. -/
theorem exactDotProductPrefixState_last_eq_sum {n : ℕ} (x y : Fin n → ℝ) :
    exactDotProductPrefixState x y (Fin.last n) =
      ∑ i : Fin n, x i * y i := by
  simpa [exactDotProductPrefixState] using
    exactDotProductPrefixNat_eq_sum_prefix x y n le_rfl

/-- **Running error recurrence bound** (Higham §3.3, Algorithm 3.2 core).

    Suppose `e i` is the partial dot-product error after `i` steps, `sHat i`
    is the computed partial sum after step `i`, and `zHat i` is the computed
    product at step `i`.  If the local inverse-model derivation gives

      `e_{i+1} = e_i - eps_i*sHat_i - delta_i*zHat_i`

    with `|eps_i| <= u`, `|delta_i| <= u`, and `e_0 = 0`, then the final
    error is bounded by the source running accumulator:

      `|e_n| <= u * sum_i (|sHat_i| + |zHat_i|)`.

    This theorem is the checked induction behind Algorithm 3.2.  A concrete
    executable `fl_runningDotProduct` theorem still has to instantiate the
    local inverse-model hypotheses for every multiplication and addition. -/
theorem runningError_bound_from_local_errors (n : ℕ) (u : ℝ)
    (e : Fin (n + 1) → ℝ) (sHat zHat delta eps : Fin n → ℝ)
    (he0 : e 0 = 0)
    (hrec : ∀ i : Fin n,
      e i.succ = e i.castSucc - eps i * sHat i - delta i * zHat i)
    (hdelta : ∀ i, |delta i| ≤ u)
    (heps : ∀ i, |eps i| ≤ u) :
    |e (Fin.last n)| ≤ u * runningErrorMu n sHat zHat := by
  induction n with
  | zero =>
      simp [runningErrorMu, he0]
  | succ n ih =>
      let ePrefix : Fin (n + 1) → ℝ := fun i => e i.castSucc
      let sPrefix : Fin n → ℝ := fun i => sHat i.castSucc
      let zPrefix : Fin n → ℝ := fun i => zHat i.castSucc
      let deltaPrefix : Fin n → ℝ := fun i => delta i.castSucc
      let epsPrefix : Fin n → ℝ := fun i => eps i.castSucc
      have he0_prefix : ePrefix 0 = 0 := by
        simp [ePrefix, he0]
      have hrec_prefix : ∀ i : Fin n,
          ePrefix i.succ =
            ePrefix i.castSucc - epsPrefix i * sPrefix i - deltaPrefix i * zPrefix i := by
        intro i
        simpa [ePrefix, sPrefix, zPrefix, deltaPrefix, epsPrefix] using hrec i.castSucc
      have hdelta_prefix : ∀ i, |deltaPrefix i| ≤ u := by
        intro i
        simpa [deltaPrefix] using hdelta i.castSucc
      have heps_prefix : ∀ i, |epsPrefix i| ≤ u := by
        intro i
        simpa [epsPrefix] using heps i.castSucc
      have hprev :=
        ih ePrefix sPrefix zPrefix deltaPrefix epsPrefix he0_prefix
          hrec_prefix hdelta_prefix heps_prefix
      have hlast_rec :
          e (Fin.last (n + 1)) =
            e (Fin.last n).castSucc -
              eps (Fin.last n) * sHat (Fin.last n) -
              delta (Fin.last n) * zHat (Fin.last n) := by
        simpa using hrec (Fin.last n)
      have htri :
          |e (Fin.last n).castSucc -
              eps (Fin.last n) * sHat (Fin.last n) -
              delta (Fin.last n) * zHat (Fin.last n)|
            ≤ |e (Fin.last n).castSucc| +
              |eps (Fin.last n) * sHat (Fin.last n)| +
              |delta (Fin.last n) * zHat (Fin.last n)| := by
        let a := e (Fin.last n).castSucc
        let b := eps (Fin.last n) * sHat (Fin.last n)
        let c := delta (Fin.last n) * zHat (Fin.last n)
        change |a - b - c| ≤ |a| + |b| + |c|
        calc
          |a - b - c| = |a + (-b) + (-c)| := by ring_nf
          _ ≤ |a + (-b)| + |-c| := abs_add_le (a + (-b)) (-c)
          _ ≤ (|a| + |-b|) + |-c| :=
              add_le_add (abs_add_le a (-b)) le_rfl
          _ = |a| + |b| + |c| := by
              rw [abs_neg, abs_neg]
      have hprev' :
          |e (Fin.last n).castSucc| ≤
            u * runningErrorMu n
              (fun i => sHat i.castSucc) (fun i => zHat i.castSucc) := by
        simpa [ePrefix, sPrefix, zPrefix] using hprev
      have heps_mul :
          |eps (Fin.last n) * sHat (Fin.last n)| ≤
            u * |sHat (Fin.last n)| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (heps (Fin.last n)) (abs_nonneg _)
      have hdelta_mul :
          |delta (Fin.last n) * zHat (Fin.last n)| ≤
            u * |zHat (Fin.last n)| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hdelta (Fin.last n)) (abs_nonneg _)
      have hmu :
          runningErrorMu (n + 1) sHat zHat =
            runningErrorMu n
              (fun i => sHat i.castSucc) (fun i => zHat i.castSucc) +
            |sHat (Fin.last n)| + |zHat (Fin.last n)| := by
        unfold runningErrorMu
        rw [Fin.foldl_succ_last]
      rw [hlast_rec]
      calc
        |e (Fin.last n).castSucc -
              eps (Fin.last n) * sHat (Fin.last n) -
              delta (Fin.last n) * zHat (Fin.last n)|
            ≤ |e (Fin.last n).castSucc| +
              |eps (Fin.last n) * sHat (Fin.last n)| +
              |delta (Fin.last n) * zHat (Fin.last n)| := htri
        _ ≤ u * runningErrorMu n
              (fun i => sHat i.castSucc) (fun i => zHat i.castSucc) +
            u * |sHat (Fin.last n)| + u * |zHat (Fin.last n)| := by
              linarith
        _ = u * runningErrorMu (n + 1) sHat zHat := by
              rw [hmu]
              ring

/-- **Executable running dot-product error bound** (Higham §3.3, Algorithm 3.2).

This instantiates `runningError_bound_from_local_errors` with the concrete loop

`z = fl_mul x_i y_i; s = fl_add s z; mu += |s| + |z|`.

The hypotheses are exactly the modified/inverse operation model (Higham (2.5))
for each rounded multiplication and addition in this loop.  This is separate
from the repository's primitive `FPModel` standard model: a caller must supply
the computed-denominator witnesses, or derive them from a stronger concrete
rounding theorem. -/
theorem fl_runningDotProduct_error_bound_from_inverse_models (fp : FPModel)
    (n : ℕ) (x y : Fin n → ℝ)
    (hmul : ∀ i : Fin n,
      inverseRelErrorModel (fp.fl_mul (x i) (y i)) (x i * y i) fp.u)
    (hadd : ∀ i : Fin n,
      inverseRelErrorModel
        (fp.fl_add (fl_runningDotProductState fp x y i.castSucc)
          (fl_runningDotProductProduct fp x y i))
        (fl_runningDotProductState fp x y i.castSucc +
          fl_runningDotProductProduct fp x y i) fp.u) :
    |fl_runningDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      fp.u * runningErrorMu n
        (fun i => fl_runningDotProductState fp x y i.succ)
        (fun i => fl_runningDotProductProduct fp x y i) := by
  let zHat : Fin n → ℝ := fun i => fl_runningDotProductProduct fp x y i
  let sHat : Fin n → ℝ := fun i => fl_runningDotProductState fp x y i.succ
  have haddState :
      ∀ i : Fin n,
        inverseRelErrorModel (sHat i)
          (fl_runningDotProductState fp x y i.castSucc + zHat i) fp.u := by
    intro i
    simpa [sHat, zHat, fl_runningDotProductState_succ] using hadd i
  let delta : Fin n → ℝ := fun i => Classical.choose (hmul i)
  have hdeltaSpec :
      ∀ i : Fin n,
        |delta i| ≤ fp.u ∧ inverseRelErrorWitness (zHat i) (x i * y i) (delta i) := by
    intro i
    have h := Classical.choose_spec (hmul i)
    simpa [delta, zHat, fl_runningDotProductProduct] using h
  let eps : Fin n → ℝ := fun i => Classical.choose (haddState i)
  have hepsSpec :
      ∀ i : Fin n,
        |eps i| ≤ fp.u ∧
          inverseRelErrorWitness (sHat i)
            (fl_runningDotProductState fp x y i.castSucc + zHat i) (eps i) := by
    intro i
    have h := Classical.choose_spec (haddState i)
    simpa [eps] using h
  let e : Fin (n + 1) → ℝ := fun k =>
    fl_runningDotProductState fp x y k - exactDotProductPrefixState x y k
  have he0 : e 0 = 0 := by
    simp [e]
  have hrec : ∀ i : Fin n,
      e i.succ = e i.castSucc - eps i * sHat i - delta i * zHat i := by
    intro i
    have hmulSigned : x i * y i = zHat i * (1 + delta i) := by
      have h :=
        (inverseRelErrorWitness_iff_signedRelErrorWitness
          (zHat i) (x i * y i) (delta i) (hdeltaSpec i).2.1).mp
          (hdeltaSpec i).2
      simpa [signedRelErrorWitness] using h
    have haddSigned :
        fl_runningDotProductState fp x y i.castSucc + zHat i =
          sHat i * (1 + eps i) := by
      have h :=
        (inverseRelErrorWitness_iff_signedRelErrorWitness
          (sHat i) (fl_runningDotProductState fp x y i.castSucc + zHat i)
          (eps i) (hepsSpec i).2.1).mp (hepsSpec i).2
      simpa [signedRelErrorWitness] using h
    have haddRearr :
        fl_runningDotProductState fp x y i.castSucc =
          sHat i + eps i * sHat i - zHat i := by
      calc
        fl_runningDotProductState fp x y i.castSucc =
            sHat i * (1 + eps i) - zHat i := by linarith
        _ = sHat i + eps i * sHat i - zHat i := by ring
    calc
      e i.succ =
          sHat i -
            (exactDotProductPrefixState x y i.castSucc + zHat i * (1 + delta i)) := by
        simp [e, sHat, exactDotProductPrefixState_succ, hmulSigned]
      _ = e i.castSucc - eps i * sHat i - delta i * zHat i := by
        dsimp [e]
        rw [haddRearr]
        ring
  have hbound :=
    runningError_bound_from_local_errors n fp.u e sHat zHat delta eps he0 hrec
      (fun i => (hdeltaSpec i).1) (fun i => (hepsSpec i).1)
  have hfinal :
      e (Fin.last n) =
        fl_runningDotProduct fp n x y - ∑ i : Fin n, x i * y i := by
    simp [e, fl_runningDotProduct, fl_runningDotProductState,
      exactDotProductPrefixState_last_eq_sum]
  rw [hfinal] at hbound
  simpa [sHat, zHat] using hbound

/-- **Dot product rounding error bound** (Higham §3.1, equation 3.5).

    The computed floating-point dot product satisfies:
      |fl_dotProduct fp x y - ∑ i, x i * y i| ≤ γ(n) * ∑ i, |x i| * |y i|

    Proof sketch:
      1. For n = 0 the result is trivial.
      2. For n = n'+1, extract mul rounding errors: fl_mul (x i) (y i) = x i * y i * (1 + δ i)
         with |δ i| ≤ u ≤ γ(1).
      3. Apply fl_sum_error_init to the n' accumulated additions starting from
         fl_mul (x 0) (y 0) with initial-accumulator error Θ and per-term errors θ i,
         all bounded by γ(n').
      4. Combine each pair (δ i, Θ or θ i) via gamma_mul to get a single error η i
         with |η i| ≤ γ(n'+1) = γ(n).
      5. Total error is ∑ x i * y i * η i; apply triangle inequality to get the bound. -/
theorem dotProduct_error_bound (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ)
    (hn : gammaValid fp n) :
    |fl_dotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp n * ∑ i : Fin n, |x i| * |y i| := by
  cases n with
  | zero => simp [fl_dotProduct]
  | succ n' =>
    -- gammaValid helpers
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    have hn' : gammaValid fp n' := gammaValid_mono fp (Nat.le_succ n') hn
    -- mul rounding errors for all n'+1 terms
    let δ : Fin (n' + 1) → ℝ := fun i => Classical.choose (fp.model_mul (x i) (y i))
    have hδ : ∀ i, |δ i| ≤ fp.u ∧ fp.fl_mul (x i) (y i) = x i * y i * (1 + δ i) :=
      fun i => Classical.choose_spec (fp.model_mul (x i) (y i))
    have hδ_1 : ∀ i, |δ i| ≤ gamma fp 1 :=
      fun i => le_trans (hδ i).1 (u_le_gamma fp one_pos h1valid)
    -- apply fl_sum_error_init to the n' additions starting from fl_mul (x 0) (y 0)
    obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
      fl_sum_error_init fp n' (fun i => fp.fl_mul (x i.succ) (y i.succ))
        (fp.fl_mul (x 0) (y 0)) hn'
    -- expand fl_dotProduct
    have hdot : fl_dotProduct fp (n' + 1) x y =
        x 0 * y 0 * (1 + δ 0) * (1 + Θ) +
        ∑ i : Fin n', x i.succ * y i.succ * (1 + δ i.succ) * (1 + θ i) := by
      show Fin.foldl n' (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
          (fp.fl_mul (x 0) (y 0)) = _
      rw [hfold, (hδ 0).2]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [(hδ i.succ).2]
    -- combined errors: η₀ for term 0, ηs i for term i.succ
    let η₀ : ℝ := δ 0 + Θ + δ 0 * Θ
    let ηs : Fin n' → ℝ := fun i => δ i.succ + θ i + δ i.succ * θ i
    -- |η₀| ≤ γ(n'+1)
    have hη₀ : |η₀| ≤ gamma fp (n' + 1) := by
      obtain ⟨η, hη, heq⟩ := gamma_mul fp n' 1 Θ (δ 0) hΘ (hδ_1 0) hn
      have hval : η = η₀ := by
        have hring : (1 + Θ) * (1 + δ 0) = 1 + η₀ := by simp only [η₀]; ring
        linarith [heq, hring]
      rw [← hval]; exact hη
    -- |ηs i| ≤ γ(n'+1) for each i
    have hηs : ∀ i, |ηs i| ≤ gamma fp (n' + 1) := fun i => by
      obtain ⟨η, hη, heq⟩ := gamma_mul fp n' 1 (θ i) (δ i.succ) (hθ i) (hδ_1 i.succ) hn
      have hval : η = ηs i := by
        have hring : (1 + θ i) * (1 + δ i.succ) = 1 + ηs i := by simp only [ηs]; ring
        linarith [heq, hring]
      rw [← hval]; exact hη
    -- the total error equals x 0 * y 0 * η₀ + ∑ x i.succ * y i.succ * ηs i
    have herr : fl_dotProduct fp (n' + 1) x y - ∑ i : Fin (n' + 1), x i * y i =
        x 0 * y 0 * η₀ + ∑ i : Fin n', x i.succ * y i.succ * ηs i := by
      rw [hdot, Fin.sum_univ_succ]
      have hzero : x 0 * y 0 * (1 + δ 0) * (1 + Θ) - x 0 * y 0 = x 0 * y 0 * η₀ := by
        simp only [η₀]; ring
      have hsucc : ∑ i : Fin n', x i.succ * y i.succ * (1 + δ i.succ) * (1 + θ i) -
                   ∑ i : Fin n', x i.succ * y i.succ =
                   ∑ i : Fin n', x i.succ * y i.succ * ηs i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _
        show x i.succ * y i.succ * (1 + δ i.succ) * (1 + θ i) - x i.succ * y i.succ =
             x i.succ * y i.succ * ηs i
        simp only [ηs]; ring
      linarith [hzero, hsucc]
    rw [herr]
    calc |x 0 * y 0 * η₀ + ∑ i : Fin n', x i.succ * y i.succ * ηs i|
        ≤ |x 0 * y 0 * η₀| + |∑ i : Fin n', x i.succ * y i.succ * ηs i| := by
              rw [abs_le]; constructor <;>
              linarith [le_abs_self (x 0 * y 0 * η₀),
                        le_abs_self (∑ i : Fin n', x i.succ * y i.succ * ηs i),
                        neg_abs_le (x 0 * y 0 * η₀),
                        neg_abs_le (∑ i : Fin n', x i.succ * y i.succ * ηs i)]
      _ ≤ |x 0 * y 0 * η₀| + ∑ i : Fin n', |x i.succ * y i.succ * ηs i| :=
              add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ = |x 0| * |y 0| * |η₀| + ∑ i : Fin n', |x i.succ| * |y i.succ| * |ηs i| := by
              simp only [abs_mul]
      _ ≤ |x 0| * |y 0| * gamma fp (n' + 1) +
          ∑ i : Fin n', |x i.succ| * |y i.succ| * gamma fp (n' + 1) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hη₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
                (Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left (hηs i) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = gamma fp (n' + 1) * ∑ i : Fin (n' + 1), |x i| * |y i| := by
              rw [Fin.sum_univ_succ, ← Finset.sum_mul]; ring

/-- **Dot product componentwise backward error** (Higham §3.1, equation 3.3).

    The computed floating-point dot product satisfies:
      fl_dotProduct fp x y = ∑ i, x i * y i * (1 + η i)

    where each |η i| ≤ γ(n).  This is the *primary* backward error result
    from which backward stability (3.4) and the forward bound (3.5) derive. -/
theorem dotProduct_backward_error (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : gammaValid fp n) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp n) ∧
      fl_dotProduct fp n x y = ∑ i : Fin n, x i * y i * (1 + η i) := by
  cases n with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [fl_dotProduct]⟩
  | succ n' =>
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    have hn' : gammaValid fp n' := gammaValid_mono fp (Nat.le_succ n') hn
    let δ : Fin (n' + 1) → ℝ := fun i => Classical.choose (fp.model_mul (x i) (y i))
    have hδ : ∀ i, |δ i| ≤ fp.u ∧ fp.fl_mul (x i) (y i) = x i * y i * (1 + δ i) :=
      fun i => Classical.choose_spec (fp.model_mul (x i) (y i))
    have hδ_1 : ∀ i, |δ i| ≤ gamma fp 1 :=
      fun i => le_trans (hδ i).1 (u_le_gamma fp one_pos h1valid)
    obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
      fl_sum_error_init fp n' (fun i => fp.fl_mul (x i.succ) (y i.succ))
        (fp.fl_mul (x 0) (y 0)) hn'
    have hdot : fl_dotProduct fp (n' + 1) x y =
        x 0 * y 0 * (1 + δ 0) * (1 + Θ) +
        ∑ i : Fin n', x i.succ * y i.succ * (1 + δ i.succ) * (1 + θ i) := by
      show Fin.foldl n' (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
          (fp.fl_mul (x 0) (y 0)) = _
      rw [hfold, (hδ 0).2]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [(hδ i.succ).2]
    -- Build η : Fin (n'+1) → ℝ using Fin.cons
    let η₀ : ℝ := δ 0 + Θ + δ 0 * Θ
    let ηs : Fin n' → ℝ := fun i => δ i.succ + θ i + δ i.succ * θ i
    let η : Fin (n' + 1) → ℝ := Fin.cons η₀ ηs
    refine ⟨η, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · -- i = 0: |η₀| ≤ γ(n'+1)
        simp only [η, Fin.cons_zero]
        obtain ⟨e, he, heq⟩ := gamma_mul fp n' 1 Θ (δ 0) hΘ (hδ_1 0) hn
        have hval : e = η₀ := by
          have hring : (1 + Θ) * (1 + δ 0) = 1 + η₀ := by simp only [η₀]; ring
          linarith [heq, hring]
        rw [← hval]; exact he
      · -- i = j.succ: |ηs j| ≤ γ(n'+1)
        intro j
        simp only [η, Fin.cons_succ]
        obtain ⟨e, he, heq⟩ := gamma_mul fp n' 1 (θ j) (δ j.succ) (hθ j) (hδ_1 j.succ) hn
        have hval : e = ηs j := by
          have hring : (1 + θ j) * (1 + δ j.succ) = 1 + ηs j := by simp only [ηs]; ring
          linarith [heq, hring]
        rw [← hval]; exact he
    · rw [hdot, Fin.sum_univ_succ]
      simp only [η, η₀, ηs, Fin.cons_zero, Fin.cons_succ]
      congr 1
      · ring
      · apply Finset.sum_congr rfl; intro i _; ring

/-- **Dot product backward stability — y-perturbation** (Higham §3.1, equation 3.4).

    The computed floating-point dot product is the exact inner product of `x`
    with a componentwise-perturbed `y + Δy`:
      fl_dotProduct fp x y = ∑ i, x i * (y i + Δy i)

    where |Δy i| ≤ γ(n) * |y i| for all i.

    Proof: set Δyᵢ = yᵢ * ηᵢ using the witnesses from `dotProduct_backward_error`. -/
theorem dotProduct_backward_stable_y (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : gammaValid fp n) :
    ∃ Δy : Fin n → ℝ,
      (∀ i, |Δy i| ≤ gamma fp n * |y i|) ∧
      fl_dotProduct fp n x y = ∑ i : Fin n, x i * (y i + Δy i) := by
  obtain ⟨η, hη, hfl⟩ := dotProduct_backward_error fp n x y hn
  refine ⟨fun i => y i * η i, ?_, ?_⟩
  · intro i
    rw [abs_mul, mul_comm (gamma fp n)]
    exact mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
  · rw [hfl]
    apply Finset.sum_congr rfl; intro i _
    ring

/-- **Dot product backward stability** (Higham §3.1, equation 3.4).

    The computed floating-point dot product is the exact inner product of a
    componentwise-perturbed input vector `x + Δx` with `y`:
      fl_dotProduct fp x y = ∑ i, (x i + Δx i) * y i

    where |Δx i| ≤ γ(n) * |x i| for all i.

    Proof: set Δxᵢ = xᵢ * ηᵢ using the witnesses from `dotProduct_backward_error`. -/
theorem dotProduct_backward_stable_x (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : gammaValid fp n) :
    ∃ Δx : Fin n → ℝ,
      (∀ i, |Δx i| ≤ gamma fp n * |x i|) ∧
      fl_dotProduct fp n x y = ∑ i : Fin n, (x i + Δx i) * y i := by
  obtain ⟨η, hη, hfl⟩ := dotProduct_backward_error fp n x y hn
  refine ⟨fun i => x i * η i, ?_, ?_⟩
  · intro i
    rw [abs_mul, mul_comm (gamma fp n)]
    exact mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
  · rw [hfl]
    apply Finset.sum_congr rfl; intro i _
    ring

/-- **The dot product algorithm is relatively componentwise backward stable**
    (Higham §3.2).

    Formally: `fl_dotProduct fp n` satisfies `isRelComponentwiseBackwardStable`
    with bound `γ(n)`, where the exact problem is the standard inner product
    `∑ i, x i * y i`.

    This connects `dotProduct_backward_stable_x` (Higham 3.4) to the formal
    stability predicate in `Stability.lean`. -/
theorem dotProduct_isRelBackwardStable (fp : FPModel) (n : ℕ)
    (hn : gammaValid fp n) :
    isRelComponentwiseBackwardStable n
      (fun x y => ∑ i : Fin n, x i * y i)
      (fun x y => fl_dotProduct fp n x y)
      (gamma fp n) := fun x y => by
  obtain ⟨Δx, hΔx, hfl⟩ := dotProduct_backward_stable_x fp n x y hn
  exact ⟨Δx, hΔx, hfl.symm⟩

end NumStability
