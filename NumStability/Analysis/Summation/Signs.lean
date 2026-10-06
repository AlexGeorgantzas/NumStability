import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumStability

open scoped BigOperators

/-!
# Sign structure of finite real sums

Reusable definitions and absolute-value identities for one-signed finite
families. Source-specific summation condition numbers and rounding-error
theorems remain in `NumStability.Analysis.Summation`.
-/

/-- A finite family is one-signed if every entry is nonnegative or every entry
is nonpositive. -/
def OneSigned {ι : Type*} (v : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∨ (∀ i, v i ≤ 0)

/-- A finite family has cancellation amplification at least `κ` when the sum
of magnitudes is at least `κ` times the magnitude of the exact sum. -/
def HeavyCancellationAtLeast {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (κ : ℝ) : Prop :=
  κ * |∑ i, v i| ≤ ∑ i, |v i|

/-- Sign indicator used to distribute an additive summation residual across
input components. It is `+1` for nonnegative inputs and `-1` otherwise. -/
noncomputable def summationAbsSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

/-- The summation sign indicator converts multiplication into absolute value. -/
lemma summationAbsSign_mul_eq_abs (x : ℝ) :
    summationAbsSign x * x = |x| := by
  unfold summationAbsSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · push_neg at h
    simp [abs_of_neg h]

/-- Right-multiplication version of `summationAbsSign_mul_eq_abs`. -/
lemma mul_summationAbsSign_eq_abs (x : ℝ) :
    x * summationAbsSign x = |x| := by
  rw [mul_comm, summationAbsSign_mul_eq_abs]

/-- The summation sign indicator has unit absolute value. -/
lemma abs_summationAbsSign (x : ℝ) :
    |summationAbsSign x| = 1 := by
  unfold summationAbsSign
  split_ifs <;> simp

/-- For a nonnegative finite family, the sum of absolute values is the ordinary
sum. -/
lemma sum_abs_eq_sum_of_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    (∑ i, |v i|) = ∑ i, v i := by
  apply Finset.sum_congr rfl
  intro i _
  exact abs_of_nonneg (hv i)

/-- For a nonpositive finite family, the sum of absolute values is the negative
ordinary sum. -/
lemma sum_abs_eq_neg_sum_of_nonpos {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hv : ∀ i, v i ≤ 0) :
    (∑ i, |v i|) = -∑ i, v i := by
  calc
    (∑ i, |v i|) = ∑ i, -v i := by
      apply Finset.sum_congr rfl
      intro i _
      exact abs_of_nonpos (hv i)
    _ = -∑ i, v i := by
      rw [Finset.sum_neg_distrib]

/-- For a one-signed finite family, the absolute-value sum equals the absolute
value of the ordinary sum. -/
lemma sum_abs_eq_abs_sum_of_oneSigned {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hv : OneSigned v) :
    (∑ i, |v i|) = |∑ i, v i| := by
  rcases hv with hnonneg | hnonpos
  · have hsum_nonneg : 0 ≤ ∑ i, v i :=
      Finset.sum_nonneg (fun i _ => hnonneg i)
    rw [sum_abs_eq_sum_of_nonneg v hnonneg, abs_of_nonneg hsum_nonneg]
  · have hsum_nonpos : ∑ i, v i ≤ 0 :=
      Finset.sum_nonpos (fun i _ => hnonpos i)
    rw [sum_abs_eq_neg_sum_of_nonpos v hnonpos, abs_of_nonpos hsum_nonpos]

/-- A finite real family attains equality in the sum triangle inequality
exactly when all of its entries have one sign. -/
lemma sum_abs_eq_abs_sum_iff_oneSigned {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (∑ i, |v i|) = |∑ i, v i| ↔ OneSigned v := by
  constructor
  · intro h
    by_cases hsum_nonneg : 0 ≤ ∑ i, v i
    · left
      have hzero : ∑ i, (|v i| - v i) = 0 := by
        rw [Finset.sum_sub_distrib, h, abs_of_nonneg hsum_nonneg]
        ring
      have hterm_nonneg :
          ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ |v i| - v i := by
        intro i _hi
        exact sub_nonneg.mpr (le_abs_self (v i))
      have hzero_each :
          ∀ i ∈ (Finset.univ : Finset ι), |v i| - v i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 (by simpa using hzero)
      intro i
      have hi := hzero_each i (Finset.mem_univ i)
      exact abs_eq_self.mp (by linarith)
    · right
      have hsum_nonpos : ∑ i, v i ≤ 0 := le_of_not_ge hsum_nonneg
      have hzero : ∑ i, (|v i| + v i) = 0 := by
        rw [Finset.sum_add_distrib, h, abs_of_nonpos hsum_nonpos]
        ring
      have hterm_nonneg :
          ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ |v i| + v i := by
        intro i _hi
        linarith [neg_le_abs (v i)]
      have hzero_each :
          ∀ i ∈ (Finset.univ : Finset ι), |v i| + v i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 (by simpa using hzero)
      intro i
      have hi := hzero_each i (Finset.mem_univ i)
      exact abs_eq_neg_self.mp (by linarith)
  · exact sum_abs_eq_abs_sum_of_oneSigned v

end NumStability
