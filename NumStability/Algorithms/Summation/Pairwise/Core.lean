-- Algorithms/Summation/Pairwise/Core.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error
import NumStability.FloatingPoint.Model
import NumStability.Algorithms.Summation.Tree.Balanced
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.Rounding
import NumStability.Analysis.Summation.Signs

namespace NumStability

open scoped BigOperators

/-!
# Pairwise summation

Reusable definitions and error bounds for power-of-two and carry-forward
pairwise summation. The concrete six-term schedule reproduced from Higham is
kept in `NumStability.Source.Higham.Chapter04.Section01.PairwiseSixTerm`.

For `n = 2^r` inputs, pairwise (cascade/fan-in) summation halves the array
recursively and adds the two sub-sums:

```
S₄ = (x₀ + x₁) + (x₂ + x₃)
S₈ = ((x₀+x₁)+(x₂+x₃)) + ((x₄+x₅)+(x₆+x₇))
```

Each element takes part in exactly `r = log₂ n` additions, giving the error
bound  `|Ê - S| ≤ γ(r) * Σ|xᵢ|`  (Higham (4.6)).
-/

-- ============================================================
-- Index-bound helpers for the two halves of Fin (2^(r+1))
-- ============================================================

private lemma left_lt (r : ℕ) (i : Fin (2 ^ r)) : i.val < 2 ^ (r + 1) := by
  have := i.isLt; simp [pow_succ]; omega

private lemma right_lt (r : ℕ) (i : Fin (2 ^ r)) : i.val + 2 ^ r < 2 ^ (r + 1) := by
  have := i.isLt; simp [pow_succ]; omega

-- ============================================================
-- Sum-splitting lemma: Fin (2^(r+1)) = left half + right half
-- ============================================================

/-- Split a sum over `Fin (2^(r+1))` into left and right halves. -/
private lemma sum_split {M : Type*} [AddCommMonoid M] (r : ℕ)
    (v : Fin (2 ^ (r + 1)) → M) :
    ∑ i : Fin (2 ^ (r + 1)), v i =
    ∑ i : Fin (2 ^ r), v ⟨i.val, left_lt r i⟩ +
    ∑ i : Fin (2 ^ r), v ⟨i.val + 2 ^ r, right_lt r i⟩ := by
  -- Step 1: reindex over Fin (2^r + 2^r) via finCongr
  have h : (2 : ℕ) ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
  have lhs_eq : ∑ i : Fin (2 ^ (r + 1)), v i =
      ∑ i : Fin (2 ^ r + 2 ^ r), v ⟨i.val, h.symm ▸ i.isLt⟩ :=
    Fintype.sum_equiv (finCongr h) _ _ fun i => by
      -- finCongr h i has the same val as i, so the Fin elements are equal by proof irrel
      rfl
  -- Step 2: split Fin (2^r + 2^r) using Fin.sum_univ_add
  rw [lhs_eq, Fin.sum_univ_add]
  -- congr 1 closes the castAdd goal by definitional equality (val = i.val);
  -- the only remaining goal is the natAdd side (val = 2^r + i.val, need add_comm)
  congr 1
  apply Finset.sum_congr rfl; intro i _
  congr 1; apply Fin.ext; simp

-- ============================================================
-- Definition
-- ============================================================

/-- Floating-point pairwise summation of `2^r` values.

    - `r = 0`: single element, no addition.
    - `r + 1`: recursively sum left half and right half, then `fl_add`. -/
noncomputable def fl_pairwiseSum (fp : FPModel) :
    (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0,     v => v ⟨0, by norm_num⟩
  | r + 1, v => fp.fl_add
      (fl_pairwiseSum fp r (fun i => v ⟨i.val, left_lt r i⟩))
      (fl_pairwiseSum fp r (fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩))

-- ============================================================
-- Backward error
-- ============================================================

/-- **Pairwise summation backward error** (Higham §4.2).

    For `n = 2^r` inputs, pairwise summation satisfies:
      `fl_pairwiseSum fp r v = ∑ i, v i * (1 + η i)`
    where each `|η i| ≤ γ(r)`.

    Each element takes part in exactly `r` additions; the backward error
    factor per element is therefore γ(r), not γ(n-1) as in recursive summation.

    Proof sketch: induction on `r`.
    - Base: no addition, so η ≡ 0 and γ(0) = 0.
    - Step: IH gives left and right halves each with error ≤ γ(r).
      The final `fl_add` introduces δ with |δ| ≤ u ≤ γ(1).
      `gamma_mul` combines each per-element γ(r) error with δ into γ(r+1). -/
theorem pairwiseSum_backward_error (fp : FPModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hr : gammaValid fp r) :
    ∃ η : Fin (2 ^ r) → ℝ,
      (∀ i, |η i| ≤ gamma fp r) ∧
      fl_pairwiseSum fp r v = ∑ i : Fin (2 ^ r), v i * (1 + η i) := by
  induction r with
  | zero =>
    refine ⟨fun _ => 0, fun _ => by simp [gamma], ?_⟩
    simp [fl_pairwiseSum]
  | succ r ih =>
    -- gammaValid for subproblems
    have hr' : gammaValid fp r := gammaValid_mono fp (Nat.le_succ r) hr
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hr
    -- IH on left and right halves
    obtain ⟨ηL, hηL, hL⟩ := ih (fun i => v ⟨i.val, left_lt r i⟩) hr'
    obtain ⟨ηR, hηR, hR⟩ := ih (fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩) hr'
    -- rounding error from the top-level fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (fl_pairwiseSum fp r (fun i => v ⟨i.val, left_lt r i⟩))
        (fl_pairwiseSum fp r (fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩))
    have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
    -- per-element combined errors
    -- left half i : Fin (2^r)  → ηL i + δ + ηL i * δ,  bounded by γ(r+1)
    -- right half i : Fin (2^r) → ηR i + δ + ηR i * δ,  bounded by γ(r+1)
    -- extend to η : Fin (2^(r+1)) → ℝ by splitting on index
    let η : Fin (2 ^ (r + 1)) → ℝ := fun i =>
      if h : i.val < 2 ^ r then
        ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ
      else
        ηR ⟨i.val - 2 ^ r,
          (by have := i.isLt; simp [pow_succ] at this; omega)⟩ + δ +
        ηR ⟨i.val - 2 ^ r,
          (by have := i.isLt; simp [pow_succ] at this; omega)⟩ * δ
    refine ⟨η, ?_, ?_⟩
    · -- bound: ∀ i, |η i| ≤ γ(r+1)
      intro i
      simp only [η]
      split_ifs with h
      · -- left: combine ηL ⟨i.val, h⟩ with δ via gamma_mul
        obtain ⟨e, he, heq⟩ := gamma_mul fp r 1 (ηL ⟨i.val, h⟩) δ (hηL ⟨i.val, h⟩) hδ_1 hr
        have hval : e = ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ := by linarith [heq, (by ring : (1 + ηL ⟨i.val, h⟩) * (1 + δ) = 1 + (ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ))]
        rw [← hval]; exact he
      · -- right: combine ηR ⟨…⟩ with δ via gamma_mul
        push_neg at h
        set j : Fin (2 ^ r) := ⟨i.val - 2 ^ r, by have := i.isLt; simp [pow_succ] at this; omega⟩
        obtain ⟨e, he, heq⟩ := gamma_mul fp r 1 (ηR j) δ (hηR j) hδ_1 hr
        have hval : e = ηR j + δ + ηR j * δ := by linarith [heq, (by ring : (1 + ηR j) * (1 + δ) = 1 + (ηR j + δ + ηR j * δ))]
        rw [← hval]; exact he
    · -- sum equality: fl_pairwiseSum (r+1) v = ∑ v i * (1 + η i)
      show fp.fl_add
          (fl_pairwiseSum fp r fun i => v ⟨i.val, left_lt r i⟩)
          (fl_pairwiseSum fp r fun i => v ⟨i.val + 2 ^ r, right_lt r i⟩) =
          ∑ i : Fin (2 ^ (r + 1)), v i * (1 + η i)
      rw [hfl, hL, hR]
      -- split RHS into left + right halves, then distribute (1+δ) on LHS
      conv_rhs => rw [sum_split r (fun i => v i * (1 + η i))]
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · -- left half: ∑ v ⟨i.val,_⟩ * (1+ηL i) * (1+δ) = ∑ v ⟨i.val,_⟩ * (1 + η ⟨i.val,_⟩)
        apply Finset.sum_congr rfl; intro i _
        have hη_i : η ⟨i.val, left_lt r i⟩ = ηL i + δ + ηL i * δ := by
          change dite (i.val < 2 ^ r)
            (fun h => ηL ⟨i.val, h⟩ + δ + ηL ⟨i.val, h⟩ * δ)
            (fun _ => ηR ⟨i.val - 2 ^ r, _⟩ + δ + ηR ⟨i.val - 2 ^ r, _⟩ * δ) = _
          rw [dif_pos i.isLt]
        rw [hη_i]; ring
      · -- right half: ∑ v ⟨i.val+2^r,_⟩ * (1+ηR i) * (1+δ) = ∑ v ⟨i.val+2^r,_⟩ * (1 + η ⟨i.val+2^r,_⟩)
        apply Finset.sum_congr rfl; intro i _
        have hη_i : η ⟨i.val + 2 ^ r, right_lt r i⟩ = ηR i + δ + ηR i * δ := by
          change dite (i.val + 2 ^ r < 2 ^ r)
            (fun h => ηL ⟨i.val + 2 ^ r, h⟩ + δ + ηL ⟨i.val + 2 ^ r, h⟩ * δ)
            (fun _ => ηR ⟨i.val + 2 ^ r - 2 ^ r, _⟩ + δ + ηR ⟨i.val + 2 ^ r - 2 ^ r, _⟩ * δ) = _
          rw [dif_neg (by omega : ¬ (i.val + 2 ^ r < 2 ^ r))]
          have hj : (⟨i.val + 2 ^ r - 2 ^ r,
              (by have := i.isLt; simp at this; omega : i.val + 2 ^ r - 2 ^ r < 2 ^ r)⟩
              : Fin (2 ^ r)) = i := Fin.ext (Nat.add_sub_cancel_right i.val (2 ^ r))
          rw [hj]
        rw [hη_i]; ring

-- ============================================================
-- Forward error bound
-- ============================================================

/-- **Pairwise summation forward error bound** (Higham §4.2, equation 4.6).

    For `n = 2^r` inputs:
      `|fl_pairwiseSum fp r v - ∑ i, v i| ≤ γ(r) * ∑ i, |v i|`

    Since the exponent is `r = log₂ n` rather than `n - 1`, this is a
    significantly tighter bound than recursive summation for large `n`. -/
theorem pairwiseSum_forward_error_bound (fp : FPModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hr : gammaValid fp r) :
    |fl_pairwiseSum fp r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp r * ∑ i : Fin (2 ^ r), |v i| := by
  obtain ⟨η, hη, hfold⟩ := pairwiseSum_backward_error fp r v hr
  have herr : fl_pairwiseSum fp r v - ∑ i : Fin (2 ^ r), v i =
      ∑ i : Fin (2 ^ r), v i * η i := by
    rw [hfold, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [herr]
  calc |∑ i : Fin (2 ^ r), v i * η i|
      ≤ ∑ i : Fin (2 ^ r), |v i * η i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (2 ^ r), |v i| * |η i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin (2 ^ r), |v i| * gamma fp r :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
    _ = gamma fp r * ∑ i : Fin (2 ^ r), |v i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- Pairwise summation has a relative-form forward bound for one-signed data. -/
theorem pairwiseSum_forward_error_bound_oneSigned (fp : FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) (hr : gammaValid fp r) (hv : OneSigned v) :
    |fl_pairwiseSum fp r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp r * |∑ i : Fin (2 ^ r), v i| := by
  have hbound := pairwiseSum_forward_error_bound fp r v hr
  simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound

/-- Pairwise summation relative-error corollary for one-signed data. -/
theorem pairwiseSum_relError_le_gamma_of_oneSigned (fp : FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) (hr : gammaValid fp r) (hv : OneSigned v)
    (hsum : (∑ i : Fin (2 ^ r), v i) ≠ 0) :
    relError (fl_pairwiseSum fp r v) (∑ i : Fin (2 ^ r), v i) ≤
      gamma fp r := by
  have hden : 0 < |∑ i : Fin (2 ^ r), v i| := abs_pos.mpr hsum
  have hbound := pairwiseSum_forward_error_bound_oneSigned fp r v hr hv
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

-- ============================================================
-- Source-shaped arbitrary-length carry-forward pairwise summation
-- ============================================================

/-!
Higham's p. 80 pairwise method first forms adjacent pair sums
`y_i = x_{2i-1} + x_{2i}` and carries `x_n` forward unchanged when `n` is odd,
then repeats that process recursively.  Equivalently, for `n > 1`, the final
addition combines a perfectly balanced block of size
`2^(ceil(log₂ n) - 1)` with the remaining carried tail.
-/

private def pairwiseCarryTreeAux : (n : ℕ) → SumTree (n + 1)
  | 0 => SumTree.leaf
  | n + 1 =>
      let total := n + 2
      let r := Nat.clog 2 total - 1
      let p := 2 ^ r
      let q := total - p
      have hp_lt : p < total := by
        simpa [p, r, total] using
          Nat.pow_pred_clog_lt_self Nat.one_lt_two (by omega : 1 < n + 2)
      have hq_pos : 0 < q := by
        exact Nat.sub_pos_of_lt hp_lt
      have hright : SumTree q :=
        (Nat.sub_add_cancel hq_pos) ▸ pairwiseCarryTreeAux (q - 1)
      have hsum : p + q = total := by
        exact Nat.add_sub_of_le (le_of_lt hp_lt)
      have hsum' : p + q = n + 1 + 1 := by
        simpa [total, Nat.add_assoc] using hsum
      hsum' ▸ SumTree.node (SumTree.balancedTree r) hright
termination_by n => n
decreasing_by
  simp_wf
  have hp_pos : 0 < 2 ^ (Nat.clog 2 (n + 2) - 1) := by
    exact Nat.pow_pos (by omega : 0 < 2)
  omega

private lemma pairwiseCarryTreeAux_depth :
    ∀ n : ℕ, (pairwiseCarryTreeAux n).depth = Nat.clog 2 (n + 1)
  | 0 => by
      simp [pairwiseCarryTreeAux, SumTree.depth]
  | n + 1 => by
      let total := n + 2
      let r := Nat.clog 2 total - 1
      let p := 2 ^ r
      let q := total - p
      have hp_lt : p < total := by
        simpa [p, r, total] using
          Nat.pow_pred_clog_lt_self Nat.one_lt_two (by omega : 1 < n + 2)
      have hq_pos : 0 < q := by
        exact Nat.sub_pos_of_lt hp_lt
      have hright_depth :
          (((Nat.sub_add_cancel hq_pos) ▸ pairwiseCarryTreeAux (q - 1))
            : SumTree q).depth = Nat.clog 2 q := by
        rw [SumTree.depth_cast]
        simpa [Nat.sub_add_cancel hq_pos] using pairwiseCarryTreeAux_depth (q - 1)
      have hq_le_pow : q ≤ 2 ^ r := by
        have htotal_le : total ≤ 2 ^ Nat.clog 2 total := by
          exact Nat.le_pow_clog Nat.one_lt_two total
        have htwo_mul : 2 ^ Nat.clog 2 total = p + p := by
          have hclog_pos : 0 < Nat.clog 2 total :=
            Nat.clog_pos Nat.one_lt_two (by omega : 1 < total)
          have hsucc : r + 1 = Nat.clog 2 total := by
            simp [r, Nat.sub_add_cancel hclog_pos]
          calc
            2 ^ Nat.clog 2 total = 2 ^ (r + 1) := by rw [hsucc]
            _ = p + p := by rw [pow_succ, Nat.mul_two]
        have htotal_le' : total ≤ p + p := by
          simpa [htwo_mul] using htotal_le
        omega
      have hright_le : Nat.clog 2 q ≤ r := by
        exact Nat.clog_le_of_le_pow hq_le_pow
      have hclog_pos : 0 < Nat.clog 2 total :=
        Nat.clog_pos Nat.one_lt_two (by omega : 1 < total)
      have hr_succ : r + 1 = Nat.clog 2 total := by
        simp [r, Nat.sub_add_cancel hclog_pos]
      rw [pairwiseCarryTreeAux.eq_2 n]
      rw [SumTree.depth_cast]
      simp only [SumTree.depth, SumTree.balancedTree_depth]
      rw [SumTree.depth_cast]
      have hq_pos_raw : 0 < n + 2 - 2 ^ (Nat.clog 2 (n + 2) - 1) := by
        simpa [total, r, p, q] using hq_pos
      rw [SumTree.depth_cast] at hright_depth
      have hright_depth_raw :
          (pairwiseCarryTreeAux
            (n + 2 - 2 ^ (Nat.clog 2 (n + 2) - 1) - 1)).depth =
              Nat.clog 2 (n + 2 - 2 ^ (Nat.clog 2 (n + 2) - 1)) := by
        simpa [total, r, p, q, Nat.sub_add_cancel hq_pos_raw] using hright_depth
      rw [hright_depth_raw]
      have hright_le_raw :
          Nat.clog 2 (n + 2 - 2 ^ (Nat.clog 2 (n + 2) - 1)) ≤
            Nat.clog 2 (n + 2) - 1 := by
        simpa [total, r, p, q] using hright_le
      have hmax :
          max (Nat.clog 2 (n + 2) - 1)
              (Nat.clog 2 (n + 2 - 2 ^ (Nat.clog 2 (n + 2) - 1))) =
            Nat.clog 2 (n + 2) - 1 :=
        max_eq_left hright_le_raw
      rw [hmax]
      have hr_succ_raw :
          Nat.clog 2 (n + 2) - 1 + 1 = Nat.clog 2 (n + 2) := by
        simpa [total] using hr_succ
      simpa [Nat.add_assoc] using hr_succ_raw
termination_by n => n
decreasing_by
  simp_wf
  have hp_pos : 0 < 2 ^ (Nat.clog 2 (n + 2) - 1) := by
    exact Nat.pow_pos (by omega : 0 < 2)
  omega

/-- Source-shaped carry-forward pairwise summation tree for any nonempty
input length.  For odd lengths, the final unpaired entry at each stage is
carried into the next stage, matching Higham p. 80. -/
def pairwiseCarryTree (n : ℕ) (h : 0 < n) : SumTree n :=
  Nat.sub_add_cancel h ▸ pairwiseCarryTreeAux (n - 1)

/-- The source-shaped carry-forward pairwise tree has exactly
`ceil(log₂ n)` stages. -/
lemma pairwiseCarryTree_depth (n : ℕ) (h : 0 < n) :
    (pairwiseCarryTree n h).depth = Nat.clog 2 n := by
  unfold pairwiseCarryTree
  rw [SumTree.depth_cast]
  simpa [Nat.sub_add_cancel h] using pairwiseCarryTreeAux_depth (n - 1)

/-- Elementary growth fact used to compare the pairwise `ceil(log₂ n)` depth
with the generic linear `n - 1` Algorithm 4.1 depth. -/
lemma nat_le_two_pow_pred (n : ℕ) (hn : 0 < n) :
    n ≤ 2 ^ (n - 1) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          norm_num
      | succ k =>
          have hprev : k + 1 ≤ 2 ^ k := ih (by omega)
          have hdouble : 2 * (k + 1) ≤ 2 * 2 ^ k :=
            Nat.mul_le_mul_left 2 hprev
          have hstep : k + 2 ≤ 2 * (k + 1) := by omega
          have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by
            rw [pow_succ']
          rw [hpow] at hdouble
          exact hstep.trans hdouble

/-- The `ceil(log₂ n)` pairwise depth is no larger than the generic linear
`n - 1` depth for nonempty inputs. -/
lemma clog2_le_pred (n : ℕ) (hn : 0 < n) :
    Nat.clog 2 n ≤ n - 1 :=
  Nat.clog_le_of_le_pow (nat_le_two_pow_pred n hn)

/-- Pairwise carry-tree depth is bounded by the source-uniform `n - 1` depth.
This is the formal comparison behind Higham §4.6 (printed p. 89): pairwise summation
has logarithmic rather than linear worst-case error depth. -/
theorem pairwiseCarryTree_depth_le_linear (n : ℕ) (hn : 0 < n) :
    (pairwiseCarryTree n hn).depth ≤ n - 1 := by
  rw [pairwiseCarryTree_depth n hn]
  exact clog2_le_pred n hn

/-- Source-shaped input-count relative-error corollary for power-of-two
pairwise summation on one-signed data.

The sharp pairwise theorem uses the logarithmic `gamma r` radius.  Under the
displayed smallness condition `(r+1) * r * u <= 1`, this implies the coarser
same-sign advice bound by the number of inputs, `(2^r) * u`. -/
theorem pairwiseSum_relError_le_pow_two_mul_u_of_oneSigned (fp : FPModel)
    (r : ℕ) (v : Fin (2 ^ r) → ℝ) (hvalid : gammaValid fp r)
    (hsmall : (((r + 1 : ℕ) : ℝ) * ((r : ℝ) * fp.u)) ≤ 1)
    (hv : OneSigned v) (hsum : (∑ i : Fin (2 ^ r), v i) ≠ 0) :
    relError (fl_pairwiseSum fp r v) (∑ i : Fin (2 ^ r), v i) ≤
      ((2 ^ r : ℕ) : ℝ) * fp.u := by
  have hgamma :=
    pairwiseSum_relError_le_gamma_of_oneSigned fp r v hvalid hv hsum
  have hgamma_le_succ :
      gamma fp r ≤ (((r + 1 : ℕ) : ℝ) * fp.u) := by
    have hvalid' : gammaValid fp ((r + 1) - 1) := by
      simpa using hvalid
    have hsmall' :
        (((r + 1 : ℕ) : ℝ) *
            ((((r + 1) - 1 : ℕ) : ℝ) * fp.u)) ≤ 1 := by
      simpa using hsmall
    simpa using
      gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one fp
        (n := r + 1) (Nat.succ_pos r) hvalid' hsmall'
  have hsucc_le_pow :
      (((r + 1 : ℕ) : ℝ) * fp.u) ≤ ((2 ^ r : ℕ) : ℝ) * fp.u := by
    have hnat : r + 1 ≤ 2 ^ r :=
      nat_le_two_pow_pred (r + 1) (Nat.succ_pos r)
    have hcast : ((r + 1 : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_right hcast fp.u_nonneg
  exact le_trans hgamma (le_trans hgamma_le_succ hsucc_le_pow)

/-- Floating-point source-shaped carry-forward pairwise summation for any
nonempty input length. -/
noncomputable def fl_pairwiseCarrySum (fp : FPModel) (n : ℕ) (h : 0 < n)
    (v : Fin n → ℝ) : ℝ :=
  (pairwiseCarryTree n h).eval fp v

/-- Backward-error bound for source-shaped carry-forward pairwise summation. -/
theorem pairwiseCarrySum_backward_error (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (v : Fin n → ℝ) (hγ : gammaValid fp (Nat.clog 2 n)) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (Nat.clog 2 n)) ∧
      fl_pairwiseCarrySum fp n hn v =
        ∑ i : Fin n, v i * (1 + η i) := by
  have hd : (pairwiseCarryTree n hn).depth = Nat.clog 2 n :=
    pairwiseCarryTree_depth n hn
  have ht : gammaValid fp (pairwiseCarryTree n hn).depth := by
    rw [hd]
    exact hγ
  obtain ⟨η, hη, hsum⟩ := SumTree.backward_error fp (pairwiseCarryTree n hn) ht v
  rw [hd] at hη
  exact ⟨η, hη, by simpa [fl_pairwiseCarrySum] using hsum⟩

/-- Forward-error bound for source-shaped carry-forward pairwise summation. -/
theorem pairwiseCarrySum_forward_error_bound (fp : FPModel) (n : ℕ)
    (hn : 0 < n) (v : Fin n → ℝ) (hγ : gammaValid fp (Nat.clog 2 n)) :
    |fl_pairwiseCarrySum fp n hn v - ∑ i : Fin n, v i| ≤
      gamma fp (Nat.clog 2 n) * ∑ i : Fin n, |v i| := by
  have hd : (pairwiseCarryTree n hn).depth = Nat.clog 2 n :=
    pairwiseCarryTree_depth n hn
  have ht : gammaValid fp (pairwiseCarryTree n hn).depth := by
    rw [hd]
    exact hγ
  have hbound := SumTree.forward_error fp (pairwiseCarryTree n hn) ht v
  simpa [fl_pairwiseCarrySum, hd] using hbound

/-- Source-shaped carry-forward pairwise summation has a relative-form
forward bound for one-signed data. -/
theorem pairwiseCarrySum_forward_error_bound_oneSigned (fp : FPModel)
    (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ)
    (hγ : gammaValid fp (Nat.clog 2 n)) (hv : OneSigned v) :
    |fl_pairwiseCarrySum fp n hn v - ∑ i : Fin n, v i| ≤
      gamma fp (Nat.clog 2 n) * |∑ i : Fin n, v i| := by
  have hbound := pairwiseCarrySum_forward_error_bound fp n hn v hγ
  simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound

/-- Relative-error corollary for source-shaped carry-forward pairwise
summation on one-signed data. -/
theorem pairwiseCarrySum_relError_le_gamma_of_oneSigned (fp : FPModel)
    (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ)
    (hγ : gammaValid fp (Nat.clog 2 n)) (hv : OneSigned v)
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_pairwiseCarrySum fp n hn v) (∑ i : Fin n, v i) ≤
      gamma fp (Nat.clog 2 n) := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := pairwiseCarrySum_forward_error_bound_oneSigned fp n hn v hγ hv
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

/-- Source-shaped `nu` corollary for carry-forward pairwise summation on
one-signed data, using the generic Algorithm 4.1 tree surface. -/
theorem pairwiseCarrySum_relError_le_n_mul_u_of_oneSigned (fp : FPModel)
    (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ)
    (hvalid : gammaValid fp (n - 1))
    (hsmall : (n : ℝ) * (((n - 1 : ℕ) : ℝ) * fp.u) ≤ 1)
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_pairwiseCarrySum fp n hn v) (∑ i : Fin n, v i) ≤
      (n : ℝ) * fp.u := by
  simpa [fl_pairwiseCarrySum] using
    SumTree.relError_le_n_mul_u_of_oneSigned fp (pairwiseCarryTree n hn) hn
      hvalid hsmall v hv hsum

-- ============================================================
-- Arbitrary-length padded pairwise summation
-- ============================================================

/-- Pad a vector by zeros into a larger finite index type. -/
noncomputable def scalarFinZeroPad (n m : ℕ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else 0

lemma sum_scalarFinZeroPad_eq {n m : ℕ} (h : n ≤ m) (f : Fin n → ℝ) :
    (∑ i : Fin m, scalarFinZeroPad n m f i) = ∑ i : Fin n, f i := by
  have hleft :
      (∑ i : Fin m, scalarFinZeroPad n m f i) =
        ∑ k ∈ Finset.range m,
          if hi : k < m then scalarFinZeroPad n m f ⟨k, hi⟩ else 0 := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun k => if hi : k < m then scalarFinZeroPad n m f ⟨k, hi⟩ else 0) m)
  have hright :
      (∑ i : Fin n, f i) =
        ∑ k ∈ Finset.range n,
          if hi : k < n then f ⟨k, hi⟩ else 0 := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun k => if hi : k < n then f ⟨k, hi⟩ else 0) n)
  rw [hleft, hright]
  have hsplit :
      (∑ k ∈ Finset.range n,
        if hi : k < m then scalarFinZeroPad n m f ⟨k, hi⟩ else 0) =
      (∑ k ∈ Finset.range m,
        if hi : k < m then scalarFinZeroPad n m f ⟨k, hi⟩ else 0) := by
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) h)
    · intro k hkm hkn
      have hkm' : k < m := Finset.mem_range.mp hkm
      have hkn' : ¬ k < n := by simpa [Finset.mem_range] using hkn
      simp [scalarFinZeroPad, hkm', hkn']
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hkm : k < m := lt_of_lt_of_le hkn h
  simp [scalarFinZeroPad, hkm, hkn]

lemma sum_scalarFinZeroPad_abs_eq {n m : ℕ} (h : n ≤ m) (f : Fin n → ℝ) :
    (∑ i : Fin m, |scalarFinZeroPad n m f i|) = ∑ i : Fin n, |f i| := by
  have hterm :
      ∀ i : Fin m,
        |scalarFinZeroPad n m f i| = scalarFinZeroPad n m (fun j => |f j|) i := by
    intro i
    by_cases hi : i.val < n
    · simp [scalarFinZeroPad, hi]
    · simp [scalarFinZeroPad, hi]
  calc
    (∑ i : Fin m, |scalarFinZeroPad n m f i|) =
        ∑ i : Fin m, scalarFinZeroPad n m (fun j => |f j|) i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = ∑ i : Fin n, |f i| := sum_scalarFinZeroPad_eq h (fun j => |f j|)

/-- Pairwise summation for arbitrary length by zero-padding to
`2^(Nat.clog 2 n)`.

This gives the scalar analogue of the padded pairwise dot-product route: pad
the input list by exact zeros to the next power of two, then apply the balanced
pairwise summation routine. -/
noncomputable def fl_clog2PairwiseSum (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  let r := Nat.clog 2 n
  fl_pairwiseSum fp r (scalarFinZeroPad n (2 ^ r) v)

/-- Arbitrary-length padded pairwise summation backward error bound.

`Nat.clog 2 n` is mathlib's natural-number ceiling logarithm: the least `r`
with `n <= 2^r`.  The theorem is stated for the padded implementation, so it
does not charge the zero padding as additional input error. -/
theorem clog2PairwiseSum_backward_error (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hγ : gammaValid fp (Nat.clog 2 n)) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (Nat.clog 2 n)) ∧
      fl_clog2PairwiseSum fp n v = ∑ i : Fin n, v i * (1 + η i) := by
  let r := Nat.clog 2 n
  have hpad : n ≤ 2 ^ r := by
    simpa [r] using Nat.le_pow_clog Nat.one_lt_two n
  obtain ⟨ηPad, hηPad, hsum⟩ :=
    pairwiseSum_backward_error fp r (scalarFinZeroPad n (2 ^ r) v)
      (by simpa [r] using hγ)
  let η : Fin n → ℝ := fun i => ηPad ⟨i.val, lt_of_lt_of_le i.isLt hpad⟩
  refine ⟨η, ?_, ?_⟩
  · intro i
    exact hηPad ⟨i.val, lt_of_lt_of_le i.isLt hpad⟩
  · have hsum_restrict :
        (∑ i : Fin (2 ^ r), scalarFinZeroPad n (2 ^ r) v i * (1 + ηPad i)) =
          ∑ i : Fin n, v i * (1 + η i) := by
      have hterm :
          ∀ i : Fin (2 ^ r),
            scalarFinZeroPad n (2 ^ r) v i * (1 + ηPad i) =
              scalarFinZeroPad n (2 ^ r) (fun j => v j * (1 + η j)) i := by
        intro i
        by_cases hi : i.val < n
        · have hidx :
            (⟨i.val, lt_of_lt_of_le hi hpad⟩ : Fin (2 ^ r)) = i := Fin.ext rfl
          simp [scalarFinZeroPad, hi, η, hidx]
        · simp [scalarFinZeroPad, hi]
      calc
        (∑ i : Fin (2 ^ r), scalarFinZeroPad n (2 ^ r) v i * (1 + ηPad i)) =
            ∑ i : Fin (2 ^ r), scalarFinZeroPad n (2 ^ r)
              (fun j => v j * (1 + η j)) i := by
                apply Finset.sum_congr rfl
                intro i _
                exact hterm i
        _ = ∑ i : Fin n, v i * (1 + η i) :=
            sum_scalarFinZeroPad_eq hpad (fun j => v j * (1 + η j))
    simpa [fl_clog2PairwiseSum, r, hsum_restrict] using hsum

/-- Arbitrary-length padded pairwise summation forward error bound.

This is the scalar `gamma_{ceil(log2 n)}` counterpart of Higham's pairwise
summation bound, for the zero-padded balanced implementation. -/
theorem clog2PairwiseSum_forward_error_bound (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (hγ : gammaValid fp (Nat.clog 2 n)) :
    |fl_clog2PairwiseSum fp n v - ∑ i : Fin n, v i| ≤
      gamma fp (Nat.clog 2 n) * ∑ i : Fin n, |v i| := by
  let r := Nat.clog 2 n
  have hpad : n ≤ 2 ^ r := by
    simpa [r] using Nat.le_pow_clog Nat.one_lt_two n
  have hbound :=
    pairwiseSum_forward_error_bound fp r (scalarFinZeroPad n (2 ^ r) v)
      (by simpa [r] using hγ)
  have hsum :
      (∑ i : Fin (2 ^ r), scalarFinZeroPad n (2 ^ r) v i) =
        ∑ i : Fin n, v i :=
    sum_scalarFinZeroPad_eq hpad v
  have habs :
      (∑ i : Fin (2 ^ r), |scalarFinZeroPad n (2 ^ r) v i|) =
        ∑ i : Fin n, |v i| :=
    sum_scalarFinZeroPad_abs_eq hpad v
  simpa [fl_clog2PairwiseSum, r, hsum, habs] using hbound

/-- Arbitrary-length padded pairwise summation has a relative-form forward
bound for one-signed data. -/
theorem clog2PairwiseSum_forward_error_bound_oneSigned (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (hγ : gammaValid fp (Nat.clog 2 n)) (hv : OneSigned v) :
    |fl_clog2PairwiseSum fp n v - ∑ i : Fin n, v i| ≤
      gamma fp (Nat.clog 2 n) * |∑ i : Fin n, v i| := by
  have hbound := clog2PairwiseSum_forward_error_bound fp n v hγ
  simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound

/-- Relative-error corollary for arbitrary-length padded pairwise summation on
one-signed data. -/
theorem clog2PairwiseSum_relError_le_gamma_of_oneSigned (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (hγ : gammaValid fp (Nat.clog 2 n)) (hv : OneSigned v)
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_clog2PairwiseSum fp n v) (∑ i : Fin n, v i) ≤
      gamma fp (Nat.clog 2 n) := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := clog2PairwiseSum_forward_error_bound_oneSigned fp n v hγ hv
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

end NumStability
