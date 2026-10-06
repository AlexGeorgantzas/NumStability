-- Algorithms/Summation/Tree.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.Rounding
import NumStability.Analysis.StatisticalRounding
import NumStability.Analysis.Summation.Signs

namespace NumStability

open scoped BigOperators

/-!
# Summation Trees — Algorithm 4.1 (Higham §4.2)

A `SumTree n` is a binary tree whose `n` leaves are the summands and
whose internal nodes each perform one `fl_add`.  Any summation method
expressible as `n − 1` pairwise additions is an instance.

The key parameter is `depth`: the maximum number of additions any
single summand participates in.  The backward error per summand is
`γ(depth)`.  Specialisations:

- Chain tree (right-skewed): depth `n − 1` → recursive summation bound γ(n−1).
- Balanced tree: depth `r` for `n = 2ʳ` → pairwise summation bound γ(r).

This is the abstract framework behind Higham equations (4.2)–(4.6).
-/

-- ============================================================
-- Type
-- ============================================================

/-- A binary summation tree for `n` summands (Algorithm 4.1, Higham §4.2).
    `leaf` is a single summand; `node l r` computes `fl_add(sum_l, sum_r)`.
    A tree with `n` leaves performs exactly `n − 1` additions. -/
inductive SumTree : ℕ → Type where
  | leaf : SumTree 1
  | node : SumTree m → SumTree n → SumTree (m + n)

namespace SumTree

-- ============================================================
-- Structural properties
-- ============================================================

/-- Depth = max additions any single summand participates in. -/
def depth : SumTree n → ℕ
  | .leaf    => 0
  | .node l r => max l.depth r.depth + 1

/-- Number of additions performed (= number of internal nodes). -/
def numAdds : SumTree n → ℕ
  | .leaf    => 0
  | .node l r => l.numAdds + r.numAdds + 1

/-- Every `SumTree n` has `n ≥ 1`. -/
lemma n_pos : ∀ (_ : SumTree n), 0 < n := by
  intro t; induction t with
  | leaf => norm_num
  | node _ _ ihl ihr => omega

/-- A `SumTree n` performs exactly `n − 1` additions. -/
lemma numAdds_eq (t : SumTree n) : t.numAdds + 1 = n := by
  induction t with
  | leaf => simp [numAdds]
  | node l r ihl ihr => simp only [numAdds]; omega

/-- The depth of a `SumTree n` is at most `n − 1`. -/
lemma depth_le (t : SumTree n) : t.depth ≤ n - 1 := by
  induction t with
  | leaf => simp [depth]
  | node l r ihl ihr =>
    simp only [depth]
    have hl := n_pos l; have hr := n_pos r
    omega

-- ============================================================
-- Transport helpers
-- ============================================================

/-- Depth is invariant under index transport. -/
lemma depth_cast {m n : ℕ} (h : m = n) (t : SumTree m) :
    (h ▸ t).depth = t.depth := by
  subst h; rfl

-- ============================================================
-- Floating-point evaluation
-- ============================================================

/-- Evaluate a `SumTree` using floating-point arithmetic.
    Leaves map to vector entries; internal nodes call `fp.fl_add`. -/
noncomputable def eval (fp : FPModel) : SumTree n → (Fin n → ℝ) → ℝ
  | .leaf,     v => v ⟨0, by norm_num⟩
  | .node l r, v => fp.fl_add
      (eval fp l (fun i => v (Fin.castAdd _ i)))
      (eval fp r (fun i => v (Fin.natAdd _ i)))

/-- Exact real evaluation of the same binary summation tree. -/
noncomputable def exactSum : SumTree n → (Fin n → ℝ) → ℝ
  | .leaf,     v => v ⟨0, by norm_num⟩
  | .node l r, v =>
      exactSum l (fun i => v (Fin.castAdd _ i)) +
        exactSum r (fun i => v (Fin.natAdd _ i))

/-- The exact tree sum is the ordinary sum of the leaves. -/
theorem exactSum_eq_sum (t : SumTree n) (v : Fin n → ℝ) :
    exactSum t v = ∑ i : Fin n, v i := by
  induction t with
  | leaf =>
      simp [exactSum]
  | node l r ihl ihr =>
      simp [exactSum, ihl, ihr, Fin.sum_univ_add]

/-- Source-shaped inverse relative-error witnesses for every internal addition
of a summation tree.

Higham Chapter 4 equation (4.1) uses the modified model (2.5),
`computed = exact / (1 + δ)`, with the already-computed child sums as the
operands of the current addition.  This predicate supplies that witness at
every internal node of Algorithm 4.1. -/
def inverseEvalModel (fp : FPModel) : SumTree n → (Fin n → ℝ) → Prop
  | .leaf,     _ => True
  | .node l r, v =>
      inverseEvalModel fp l (fun i => v (Fin.castAdd _ i)) ∧
      inverseEvalModel fp r (fun i => v (Fin.natAdd _ i)) ∧
      inverseRelErrorModel
        (fp.fl_add
          (eval fp l (fun i => v (Fin.castAdd _ i)))
          (eval fp r (fun i => v (Fin.natAdd _ i))))
        (eval fp l (fun i => v (Fin.castAdd _ i)) +
          eval fp r (fun i => v (Fin.natAdd _ i)))
        fp.u

/-- Sum of the absolute values of the computed internal sums of a summation
tree, the quantity appearing in Higham Chapter 4 equation (4.3). -/
noncomputable def runningErrorBudget (fp : FPModel) : SumTree n → (Fin n → ℝ) → ℝ
  | .leaf,     _ => 0
  | .node l r, v =>
      runningErrorBudget fp l (fun i => v (Fin.castAdd _ i)) +
      runningErrorBudget fp r (fun i => v (Fin.natAdd _ i)) +
      |eval fp (.node l r) v|

/-- The computed internal sums of an Algorithm 4.1 tree, flattened in
left-to-right tree order.

These are the deterministic weights `T_hat_i` multiplying the local random
addition errors in the statistical reading of Higham equation (4.2). -/
noncomputable def computedInternalSums (fp : FPModel) :
    SumTree n → (Fin n → ℝ) → List ℝ
  | .leaf, _ => []
  | .node l r, v =>
      computedInternalSums fp l (fun i => v (Fin.castAdd _ i)) ++
      computedInternalSums fp r (fun i => v (Fin.natAdd _ i)) ++
      [eval fp (.node l r) v]

/-- The flattened internal-sum list has one entry per internal addition. -/
theorem computedInternalSums_length_eq_numAdds (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ) :
    (computedInternalSums fp t v).length = t.numAdds := by
  induction t with
  | leaf =>
      simp [computedInternalSums, numAdds]
  | node l r ihl ihr =>
      simp [computedInternalSums, numAdds, ihl, ihr]
      omega

/-- The absolute sum of the flattened internal computed sums is exactly the
running-error budget from Higham equation (4.3). -/
theorem computedInternalSums_abs_sum_eq_runningErrorBudget (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ) :
    ((computedInternalSums fp t v).map (fun z => |z|)).sum =
      runningErrorBudget fp t v := by
  induction t with
  | leaf =>
      simp [computedInternalSums, runningErrorBudget]
  | node l r ihl ihr =>
      simp [computedInternalSums, runningErrorBudget, List.map_append,
        List.sum_append, ihl, ihr]
      ring

/-- Statistical version of the Algorithm 4.1 running-error contribution sum:
`sum_i T_hat_i eps_i`, where `T_hat_i` are the computed internal sums of the
tree. -/
noncomputable def statisticalRunningErrorContribution (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ) {Ω : Type*}
    (eps : Fin (computedInternalSums fp t v).length → Ω → ℝ) (ω : Ω) : ℝ :=
  statisticalWeightedRoundingErrorSum
    (fun i => (computedInternalSums fp t v).get i) eps ω

/-- Statistical Algorithm 4.1 running-error contributions have zero mean when
the local addition errors have zero mean. -/
theorem statisticalRunningErrorContribution_expectation_eq_zero
    (fp : FPModel) (t : SumTree n) (v : Fin n → ℝ)
    {Ω : Type*} [Fintype Ω] {P : FiniteProbability Ω} {u : ℝ}
    {eps : Fin (computedInternalSums fp t v).length → Ω → ℝ}
    (h : StatisticalRoundingErrorModel P eps u) :
    P.expectationReal
        (statisticalRunningErrorContribution fp t v eps) = 0 := by
  simpa [statisticalRunningErrorContribution] using
    h.expectation_weighted_sum_eq_zero
      (fun i => (computedInternalSums fp t v).get i)

/-- Mean-square identity for the statistical Algorithm 4.1 running-error
contribution sum.  This is the tree-specific form of the cross-term
cancellation used in Higham Section 4.5. -/
theorem statisticalRunningErrorContribution_expectation_sq_eq_sum
    (fp : FPModel) (t : SumTree n) (v : Fin n → ℝ)
    {Ω : Type*} [Fintype Ω] {P : FiniteProbability Ω} {u : ℝ}
    {eps : Fin (computedInternalSums fp t v).length → Ω → ℝ}
    (h : StatisticalRoundingErrorModel P eps u) :
    P.expectationReal
        (fun ω => (statisticalRunningErrorContribution fp t v eps ω) ^ 2) =
      ∑ i : Fin (computedInternalSums fp t v).length,
        ((computedInternalSums fp t v).get i) ^ 2 *
          P.expectationReal (fun ω => (eps i ω) ^ 2) := by
  simpa [statisticalRunningErrorContribution] using
    h.expectation_weighted_sum_sq_eq_sum_weight_sq_second_moments
      (fun i => (computedInternalSums fp t v).get i)

/-- Mean-square bound for the statistical Algorithm 4.1 running-error
contribution sum under a uniform second-moment bound for local errors. -/
theorem statisticalRunningErrorContribution_expectation_sq_le
    (fp : FPModel) (t : SumTree n) (v : Fin n → ℝ)
    {Ω : Type*} [Fintype Ω] {P : FiniteProbability Ω} {u : ℝ}
    {eps : Fin (computedInternalSums fp t v).length → Ω → ℝ}
    (h : StatisticalRoundingErrorModel P eps u) :
    P.expectationReal
        (fun ω => (statisticalRunningErrorContribution fp t v eps ω) ^ 2) ≤
      (∑ i : Fin (computedInternalSums fp t v).length,
        ((computedInternalSums fp t v).get i) ^ 2) * u ^ 2 := by
  simpa [statisticalRunningErrorContribution] using
    h.expectation_weighted_sum_sq_le_weight_sq_mul_unit_sq
      (fun i => (computedInternalSums fp t v).get i)

/-- RMS bound for the statistical Algorithm 4.1 running-error contribution
sum under a uniform second-moment bound for local errors. -/
theorem statisticalRunningErrorContribution_rms_le
    (fp : FPModel) (t : SumTree n) (v : Fin n → ℝ)
    {Ω : Type*} [Fintype Ω] {P : FiniteProbability Ω} {u : ℝ}
    {eps : Fin (computedInternalSums fp t v).length → Ω → ℝ}
    (h : StatisticalRoundingErrorModel P eps u) (hu : 0 ≤ u) :
    Real.sqrt (P.expectationReal
        (fun ω => (statisticalRunningErrorContribution fp t v eps ω) ^ 2)) ≤
      Real.sqrt (∑ i : Fin (computedInternalSums fp t v).length,
        ((computedInternalSums fp t v).get i) ^ 2) * u := by
  simpa [statisticalRunningErrorContribution] using
    h.rms_weighted_sum_le_sqrt_weight_sq_mul_unit
      (fun i => (computedInternalSums fp t v).get i) hu

/-- The tree running-error budget is nonnegative. -/
theorem runningErrorBudget_nonneg (fp : FPModel) (t : SumTree n) (v : Fin n → ℝ) :
    0 ≤ runningErrorBudget fp t v := by
  induction t with
  | leaf =>
      simp [runningErrorBudget]
  | node l r ihl ihr =>
      exact add_nonneg (add_nonneg (ihl _) (ihr _)) (abs_nonneg _)

/-- Source-shaped signed local-error decomposition for Algorithm 4.1.

The statement `runningErrorContribution fp t v e` means that `e` is a sum of
one term `δ_i * T_hat_i` over the internal additions of the tree, with each
`δ_i` supplied by the inverse model (2.5). -/
def runningErrorContribution (fp : FPModel) :
    SumTree n → (Fin n → ℝ) → ℝ → Prop
  | .leaf,     _, e => e = 0
  | .node l r, v, e =>
      ∃ eL eR δ : ℝ,
        runningErrorContribution fp l (fun i => v (Fin.castAdd _ i)) eL ∧
        runningErrorContribution fp r (fun i => v (Fin.natAdd _ i)) eR ∧
        |δ| ≤ fp.u ∧
        inverseRelErrorWitness
          (eval fp (.node l r) v)
          (eval fp l (fun i => v (Fin.castAdd _ i)) +
            eval fp r (fun i => v (Fin.natAdd _ i)))
          δ ∧
        e = eL + eR + δ * eval fp (.node l r) v

/-- Internal inverse-model witnesses produce a signed local-error contribution
sum for the tree. -/
theorem exists_runningErrorContribution_of_inverseEvalModel (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ)
    (hmodel : inverseEvalModel fp t v) :
    ∃ e : ℝ, runningErrorContribution fp t v e := by
  induction t with
  | leaf =>
      exact ⟨0, rfl⟩
  | node l r ihl ihr =>
      rcases hmodel with ⟨hmodelL, hmodelR, hmodelTop⟩
      obtain ⟨eL, hL⟩ := ihl (fun i => v (Fin.castAdd _ i)) hmodelL
      obtain ⟨eR, hR⟩ := ihr (fun i => v (Fin.natAdd _ i)) hmodelR
      rcases hmodelTop with ⟨δ, hδ, hδwit⟩
      refine ⟨eL + eR + δ * eval fp (.node l r) v, ?_⟩
      exact ⟨eL, eR, δ, hL, hR, hδ, hδwit, rfl⟩

/-- **General Algorithm 4.1 local-error identity** (Higham §4.2, equation
(4.2)).

Any source-shaped contribution sum is exactly `S_n - S_hat_n` for the same
tree. -/
theorem runningErrorContribution_eq_error (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ) (e : ℝ)
    (hcontrib : runningErrorContribution fp t v e) :
    exactSum t v - eval fp t v = e := by
  induction t generalizing e with
  | leaf =>
      simp [runningErrorContribution, exactSum, eval] at hcontrib ⊢
      exact hcontrib.symm
  | node l r ihl ihr =>
      rcases hcontrib with ⟨eL, eR, δ, hLcontrib, hRcontrib, _hδ, hδwit, he⟩
      let vL : Fin _ → ℝ := fun i => v (Fin.castAdd _ i)
      let vR : Fin _ → ℝ := fun i => v (Fin.natAdd _ i)
      have hL := ihl vL eL hLcontrib
      have hR := ihr vR eR hRcontrib
      have hlocal :
          (eval fp l vL + eval fp r vR) -
              fp.fl_add (eval fp l vL) (eval fp r vR) =
            δ * fp.fl_add (eval fp l vL) (eval fp r vR) := by
        rcases hδwit with ⟨hden, hcomp⟩
        have hsigned : signedRelErrorWitness
            (eval fp l vL + eval fp r vR)
            (fp.fl_add (eval fp l vL) (eval fp r vR)) δ :=
          (inverseRelErrorWitness_iff_signedRelErrorWitness
            (fp.fl_add (eval fp l vL) (eval fp r vR))
            (eval fp l vL + eval fp r vR) δ hden).mp ⟨hden, hcomp⟩
        unfold signedRelErrorWitness at hsigned
        rw [hsigned]
        ring
      rw [he]
      simp [exactSum, eval]
      linarith

/-- A signed local-error contribution sum is bounded by the running-error
budget from Higham equation (4.3). -/
theorem runningErrorContribution_abs_le (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ) (e : ℝ)
    (hcontrib : runningErrorContribution fp t v e) :
    |e| ≤ fp.u * runningErrorBudget fp t v := by
  induction t generalizing e with
  | leaf =>
      simp [runningErrorContribution, runningErrorBudget] at hcontrib ⊢
      rw [hcontrib]
  | node l r ihl ihr =>
      rcases hcontrib with ⟨eL, eR, δ, hLcontrib, hRcontrib, hδ, _hδwit, he⟩
      let vL : Fin _ → ℝ := fun i => v (Fin.castAdd _ i)
      let vR : Fin _ → ℝ := fun i => v (Fin.natAdd _ i)
      have hL := ihl vL eL hLcontrib
      have hR := ihr vR eR hRcontrib
      have hlocal :
          |δ * eval fp (.node l r) v| ≤ fp.u * |eval fp (.node l r) v| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
      rw [he]
      have htri :
          |eL + eR + δ * eval fp (.node l r) v| ≤
            |eL| + |eR| + |δ * eval fp (.node l r) v| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le eL, neg_abs_le eR,
            neg_abs_le (δ * eval fp (.node l r) v)]
        · linarith [le_abs_self eL, le_abs_self eR,
            le_abs_self (δ * eval fp (.node l r) v)]
      calc
        |eL + eR + δ * eval fp (.node l r) v|
            ≤ |eL| + |eR| + |δ * eval fp (.node l r) v| := htri
        _ ≤ fp.u * runningErrorBudget fp l vL +
              fp.u * runningErrorBudget fp r vR +
              fp.u * |eval fp (.node l r) v| := by
                linarith [hL, hR, hlocal]
        _ = fp.u * runningErrorBudget fp (.node l r) v := by
              simp [runningErrorBudget, vL, vR]
              ring

/-- **General Algorithm 4.1 running-error bound** (Higham §4.2, equations
(4.1)--(4.3)).

If every internal addition of a summation tree satisfies the inverse
relative-error model (2.5), then the forward error is bounded by `u` times the
sum of the absolute values of the computed internal sums:

`|S_n - S_hat_n| <= u * sum_i |T_hat_i|`.

The theorem is stated for an arbitrary binary `SumTree`, so recursive,
pairwise, insertion, and any other Algorithm 4.1 ordering are all instances
once their tree shape and inverse-model operation witnesses are supplied. -/
theorem running_error_bound_from_inverse_models (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ)
    (hmodel : inverseEvalModel fp t v) :
    |exactSum t v - eval fp t v| ≤ fp.u * runningErrorBudget fp t v := by
  induction t with
  | leaf =>
      simp [exactSum, eval, runningErrorBudget]
  | node l r ihl ihr =>
      rcases hmodel with ⟨hmodelL, hmodelR, hmodelTop⟩
      let vL : Fin _ → ℝ := fun i => v (Fin.castAdd _ i)
      let vR : Fin _ → ℝ := fun i => v (Fin.natAdd _ i)
      have hL := ihl vL hmodelL
      have hR := ihr vR hmodelR
      have hTop :
          |(eval fp l vL + eval fp r vR) -
              fp.fl_add (eval fp l vL) (eval fp r vR)| ≤
            fp.u * |fp.fl_add (eval fp l vL) (eval fp r vR)| :=
        inverseRelErrorModel_abs_exact_sub_computed_le
          (fp.fl_add (eval fp l vL) (eval fp r vR))
          (eval fp l vL + eval fp r vR) fp.u hmodelTop
      have hdecomp :
          exactSum (.node l r) v - eval fp (.node l r) v =
            (exactSum l vL - eval fp l vL) +
            (exactSum r vR - eval fp r vR) +
            ((eval fp l vL + eval fp r vR) -
              fp.fl_add (eval fp l vL) (eval fp r vR)) := by
        simp [exactSum, eval, vL, vR]
        ring
      rw [hdecomp]
      have htri :
          |(exactSum l vL - eval fp l vL) +
              (exactSum r vR - eval fp r vR) +
              ((eval fp l vL + eval fp r vR) -
                fp.fl_add (eval fp l vL) (eval fp r vR))| ≤
            |exactSum l vL - eval fp l vL| +
              |exactSum r vR - eval fp r vR| +
              |(eval fp l vL + eval fp r vR) -
                fp.fl_add (eval fp l vL) (eval fp r vR)| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (exactSum l vL - eval fp l vL),
            neg_abs_le (exactSum r vR - eval fp r vR),
            neg_abs_le ((eval fp l vL + eval fp r vR) -
              fp.fl_add (eval fp l vL) (eval fp r vR))]
        · linarith [le_abs_self (exactSum l vL - eval fp l vL),
            le_abs_self (exactSum r vR - eval fp r vR),
            le_abs_self ((eval fp l vL + eval fp r vR) -
              fp.fl_add (eval fp l vL) (eval fp r vR))]
      calc
        |(exactSum l vL - eval fp l vL) +
            (exactSum r vR - eval fp r vR) +
            ((eval fp l vL + eval fp r vR) -
              fp.fl_add (eval fp l vL) (eval fp r vR))|
            ≤ |exactSum l vL - eval fp l vL| +
              |exactSum r vR - eval fp r vR| +
              |(eval fp l vL + eval fp r vR) -
                fp.fl_add (eval fp l vL) (eval fp r vR)| := htri
        _ ≤ fp.u * runningErrorBudget fp l vL +
              fp.u * runningErrorBudget fp r vR +
              fp.u * |fp.fl_add (eval fp l vL) (eval fp r vR)| := by
                linarith [hL, hR, hTop]
        _ = fp.u * runningErrorBudget fp (.node l r) v := by
              simp [runningErrorBudget, eval, vL, vR]
              ring

/-- Version of `running_error_bound_from_inverse_models` with the exact sum
written as `∑ i, v i`, matching Higham's `S_n`. -/
theorem running_error_sum_bound_from_inverse_models (fp : FPModel)
    (t : SumTree n) (v : Fin n → ℝ)
    (hmodel : inverseEvalModel fp t v) :
    |(∑ i : Fin n, v i) - eval fp t v| ≤
      fp.u * runningErrorBudget fp t v := by
  rw [← exactSum_eq_sum t v]
  exact running_error_bound_from_inverse_models fp t v hmodel

/-- `eval` is invariant under index transport. -/
lemma eval_cast {m n : ℕ} (h : m = n) (fp : FPModel) (t : SumTree m) (v : Fin n → ℝ) :
    (h ▸ t).eval fp v = t.eval fp (fun i => v ⟨i.val, h ▸ i.isLt⟩) := by
  subst h; rfl

-- ============================================================
-- Backward error theorem (Algorithm 4.1, Higham §4.2)
-- ============================================================

/-- **Summation tree backward error** (Higham §4.2, equations 4.1–4.4).

    For any `SumTree n` with depth `d`, the computed sum satisfies:
      `t.eval fp v = ∑ i, v i * (1 + η i)`
    where each `|η i| ≤ γ(d)`.

    Specialises to eq. (4.4) for chain trees (d = n−1) and eq. (4.6)
    for balanced trees (d = r = log₂n).

    Proof: structural induction.  Leaf is exact; at each `node` the two IH
    witnesses are combined with the top-level rounding error `δ` via
    `gamma_mul`, giving per-summand error `ηL + δ + ηL·δ` bounded by
    `γ(l.depth + 1) ≤ γ(depth (node l r))`. -/
theorem backward_error (fp : FPModel) {n : ℕ} (t : SumTree n) :
    ∀ (_ : gammaValid fp t.depth) (v : Fin n → ℝ), ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp t.depth) ∧
      t.eval fp v = ∑ i : Fin n, v i * (1 + η i) := by
  induction t with
  | leaf =>
    intro ht v
    refine ⟨fun _ => 0, fun _ => ?_, by simp [eval]⟩
    simp only [abs_zero]; exact gamma_nonneg fp ht
  | node l r ihl ihr =>
    rename_i m k
    intro ht v
    simp only [depth] at ht
    -- gammaValid for subtrees
    have hml : l.depth ≤ max l.depth r.depth + 1 :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
    have hmr : r.depth ≤ max l.depth r.depth + 1 :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
    have ht_l  : gammaValid fp l.depth := gammaValid_mono fp hml ht
    have ht_r  : gammaValid fp r.depth := gammaValid_mono fp hmr ht
    have ht_1  : gammaValid fp 1       :=
      gammaValid_mono fp (Nat.succ_le_succ (Nat.zero_le _)) ht
    have ht_l1 : gammaValid fp (l.depth + 1) :=
      gammaValid_mono fp (Nat.add_le_add_right (Nat.le_max_left _ _) 1) ht
    have ht_r1 : gammaValid fp (r.depth + 1) :=
      gammaValid_mono fp (Nat.add_le_add_right (Nat.le_max_right _ _) 1) ht
    -- IH on left and right subtrees
    obtain ⟨ηL, hηL, hL⟩ := ihl ht_l (fun i => v (Fin.castAdd k i))
    obtain ⟨ηR, hηR, hR⟩ := ihr ht_r (fun i => v (Fin.natAdd m i))
    -- Rounding error from the top-level fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (l.eval fp (fun i => v (Fin.castAdd k i)))
        (r.eval fp (fun i => v (Fin.natAdd m i)))
    have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos ht_1)
    -- Witness: per-element combined error using Fin.addCases
    refine ⟨Fin.addCases (fun i => ηL i + δ + ηL i * δ) (fun i => ηR i + δ + ηR i * δ),
            ?_, ?_⟩
    · -- Bound: ∀ i, |η i| ≤ γ(max l.depth r.depth + 1)
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Fin.addCases_left]
        obtain ⟨e, he, heq⟩ := gamma_mul fp l.depth 1 (ηL j) δ (hηL j) hδ_1 ht_l1
        have hval : e = ηL j + δ + ηL j * δ := by
          linarith [heq, (by ring : (1 + ηL j) * (1 + δ) = 1 + (ηL j + δ + ηL j * δ))]
        rw [← hval]
        exact le_trans he (gamma_mono fp (Nat.add_le_add_right (Nat.le_max_left _ _) 1) ht)
      · intro j
        simp only [Fin.addCases_right]
        obtain ⟨e, he, heq⟩ := gamma_mul fp r.depth 1 (ηR j) δ (hηR j) hδ_1 ht_r1
        have hval : e = ηR j + δ + ηR j * δ := by
          linarith [heq, (by ring : (1 + ηR j) * (1 + δ) = 1 + (ηR j + δ + ηR j * δ))]
        rw [← hval]
        exact le_trans he (gamma_mono fp (Nat.add_le_add_right (Nat.le_max_right _ _) 1) ht)
    · -- Sum equality
      show fp.fl_add (l.eval fp fun i => v (Fin.castAdd k i))
                     (r.eval fp fun i => v (Fin.natAdd m i)) =
           ∑ i : Fin (m + k), v i * (1 + Fin.addCases (fun i => ηL i + δ + ηL i * δ)
                                                        (fun i => ηR i + δ + ηR i * δ) i)
      rw [hfl, hL, hR]
      conv_rhs => rw [Fin.sum_univ_add]
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl; intro i _
        simp only [Fin.addCases_left]; ring
      · apply Finset.sum_congr rfl; intro i _
        simp only [Fin.addCases_right]; ring

-- ============================================================
-- Forward error bound
-- ============================================================

/-- **Summation tree forward error bound** (Higham §4.2, eqs. 4.4 and 4.6).

    For any `SumTree n` with depth `d`:
      `|t.eval fp v − ∑ i, v i| ≤ γ(d) * ∑ i, |v i|`

    This is eq. (4.4) for chain trees and eq. (4.6) for balanced trees. -/
theorem forward_error (fp : FPModel) {n : ℕ} (t : SumTree n)
    (ht : gammaValid fp t.depth) (v : Fin n → ℝ) :
    |t.eval fp v - ∑ i : Fin n, v i| ≤ gamma fp t.depth * ∑ i : Fin n, |v i| := by
  obtain ⟨η, hη, hfold⟩ := backward_error fp t ht v
  have herr : t.eval fp v - ∑ i : Fin n, v i = ∑ i : Fin n, v i * η i := by
    rw [hfold, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [herr]
  calc |∑ i : Fin n, v i * η i|
      ≤ ∑ i : Fin n, |v i * η i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |η i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * gamma fp t.depth :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
    _ = gamma fp t.depth * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- One-signed Algorithm 4.1 tree sums have a relative-form forward bound with
the tree-depth `gamma` radius. -/
theorem forward_error_oneSigned (fp : FPModel) {n : ℕ} (t : SumTree n)
    (ht : gammaValid fp t.depth) (v : Fin n → ℝ) (hv : OneSigned v) :
    |t.eval fp v - ∑ i : Fin n, v i| ≤
      gamma fp t.depth * |∑ i : Fin n, v i| := by
  have hbound := forward_error fp t ht v
  simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound

/-- Relative-error form of `forward_error_oneSigned`. -/
theorem relError_le_gamma_of_oneSigned (fp : FPModel) {n : ℕ} (t : SumTree n)
    (ht : gammaValid fp t.depth) (v : Fin n → ℝ) (hv : OneSigned v)
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (t.eval fp v) (∑ i : Fin n, v i) ≤ gamma fp t.depth := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := forward_error_oneSigned fp t ht v hv
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

/-- **General Algorithm 4.1 backward error with the source `n-1` radius**
(Higham §4.2, after equation (4.4)).

This is the weaker source-uniform form of `backward_error`, obtained from
`t.depth <= n - 1`. -/
theorem backward_error_n_minus_one (fp : FPModel) {n : ℕ} (t : SumTree n)
    (h : gammaValid fp (n - 1)) (v : Fin n → ℝ) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (n - 1)) ∧
      t.eval fp v = ∑ i : Fin n, v i * (1 + η i) := by
  have ht : gammaValid fp t.depth := gammaValid_mono fp (depth_le t) h
  obtain ⟨η, hη, heq⟩ := backward_error fp t ht v
  refine ⟨η, ?_, heq⟩
  intro i
  exact le_trans (hη i) (gamma_mono fp (depth_le t) h)

/-- **General Algorithm 4.1 forward error with the source `n-1` radius**
(Higham §4.2, equation (4.4), gamma-form).

The source writes the first-order expansion
`(n - 1)u * sum |x_i| + O(u^2)`; this theorem keeps the exact proved
`gamma (n - 1)` radius. -/
theorem forward_error_n_minus_one (fp : FPModel) {n : ℕ} (t : SumTree n)
    (h : gammaValid fp (n - 1)) (v : Fin n → ℝ) :
    |t.eval fp v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
  obtain ⟨η, hη, hfold⟩ := backward_error_n_minus_one fp t h v
  have herr : t.eval fp v - ∑ i : Fin n, v i = ∑ i : Fin n, v i * η i := by
    rw [hfold, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [herr]
  calc |∑ i : Fin n, v i * η i|
      ≤ ∑ i : Fin n, |v i * η i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |η i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * gamma fp (n - 1) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
    _ = gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- General Algorithm 4.1 one-signed relative-form forward bound with the
source-uniform `n-1` radius. -/
theorem forward_error_n_minus_one_oneSigned (fp : FPModel) {n : ℕ}
    (t : SumTree n) (h : gammaValid fp (n - 1)) (v : Fin n → ℝ)
    (hv : OneSigned v) :
    |t.eval fp v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) * |∑ i : Fin n, v i| := by
  have hbound := forward_error_n_minus_one fp t h v
  simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound

/-- Relative-error form of the source-uniform Algorithm 4.1 one-signed bound. -/
theorem relError_le_gamma_n_minus_one_of_oneSigned (fp : FPModel) {n : ℕ}
    (t : SumTree n) (h : gammaValid fp (n - 1)) (v : Fin n → ℝ)
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (t.eval fp v) (∑ i : Fin n, v i) ≤ gamma fp (n - 1) := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := forward_error_n_minus_one_oneSigned fp t h v hv
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

/-- Linear small-`u` version of the source-uniform one-signed relative-error
bound for Algorithm 4.1 trees.  Under the explicit regime
`(n - 1) * u <= 1/2`, the exact `gamma (n - 1)` theorem gives a readable
`2 * (n - 1) * u` bound. -/
theorem relError_le_two_mul_n_minus_one_u_of_oneSigned
    (fp : FPModel) {n : ℕ} (t : SumTree n)
    (hsmall : ((n - 1 : ℕ) : ℝ) * fp.u ≤ 1 / 2)
    (v : Fin n → ℝ) (hv : OneSigned v)
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (t.eval fp v) (∑ i : Fin n, v i) ≤
      2 * (((n - 1 : ℕ) : ℝ) * fp.u) := by
  have hvalid : gammaValid fp (n - 1) := by
    unfold gammaValid
    linarith
  exact le_trans
    (relError_le_gamma_n_minus_one_of_oneSigned fp t hvalid v hv hsum)
    (gamma_le_two_mul_n_u_of_nu_le_half fp (n - 1) hsmall)

/-- Source-shaped `nu` corollary for one-signed Algorithm 4.1 sums.

Higham's method-choice advice in §4.6 (printed p. 89) says one-signed data give a relative
error at most `nu`.  This theorem derives that displayed form from the exact
`gamma (n - 1)` bound under the explicit smallness side condition
`n * (n - 1) * u ≤ 1`, which is the condition needed for
`gamma (n - 1) ≤ n * u`. -/
theorem relError_le_n_mul_u_of_oneSigned
    (fp : FPModel) {n : ℕ} (t : SumTree n)
    (hn : 0 < n) (hvalid : gammaValid fp (n - 1))
    (hsmall : (n : ℝ) * (((n - 1 : ℕ) : ℝ) * fp.u) ≤ 1)
    (v : Fin n → ℝ) (hv : OneSigned v)
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (t.eval fp v) (∑ i : Fin n, v i) ≤ (n : ℝ) * fp.u := by
  exact le_trans
    (relError_le_gamma_n_minus_one_of_oneSigned fp t hvalid v hv hsum)
    (gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one fp hn hvalid hsmall)

end SumTree

end NumStability
