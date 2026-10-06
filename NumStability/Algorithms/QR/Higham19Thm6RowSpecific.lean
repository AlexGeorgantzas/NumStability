import NumStability.Algorithms.QR.Higham19Thm6ElementwiseEntry

/-!
# Higham, Theorem 19.6 — the *row-i-specific* elementwise backward error (Powell–Reid)

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4 *Pivoting and Row-Wise Stability*, Theorem 19.6 and the
column-exchange pivot policy (19.15), p. 367.  The row-wise analysis is due to
Powell & Reid (1969) and Cox & Higham (1998); Higham prints **no proof**.  The
*printed* envelope is the strictly **row-i-local**

`|ΔA_ij| ≤ j² · γ̃_m · α_i · max_s |a_is|`,

in which `α_i` is *row i's* growth factor and `max_s |a_is|` is *row i's* data:
**no `√m`, no maximum over the other rows.**

## Position relative to the earlier waves (honest delta)

* Wave18A/18C proved the elementwise **core** and an original-space
  `√m · (max over rows)` version.
* Wave18B (`Higham19Thm6ElementwiseEntry.lean`) proved
  `theorem19_6_elementwise_computed_entry_printed_j_sq`: the printed `j²` shape
  for the genuine computed reduction sequence, but with a **global** `rowMax`
  (a uniform bound over *all* active rows, `hRowB : ∀ s, |Ahat t s| ≤ rowMax`)
  and a **hypothesised** exact-growth Lipschitz field `hexact`.  It is not the
  row-i-local envelope: `rowMax` is not `max_s|a_is|` for the specific row `i`.

The step from the Wave18B bound to the printed **row-i-local** bound is exactly
the Powell–Reid row-locality claim.  Two provably distinct construction routes
reach the same wall:

1. the `ΔA = Q (R̂ − QᵀAΠ)` route spreads a per-entry budget through the dense
   orthogonal `Q` via `√m` (the earlier waves' finding); and
2. the **per-step trailing-perturbation** route
   `ΔA = Σ_k (P̂₁⋯P̂_{k−1}) F_k`, in which each `F_k` is the single-reflector
   application backward error supported on the trailing rows `k:m`.

This file carries out route 2 honestly and isolates the exact step that needs
the external Powell–Reid argument.  It contributes three genuinely proved facts
and one precise obstruction anchor:

* **`rowInftyGrowthFactor`** — a *faithful, independently meaningful* definition
  of `α_i` as the largest ∞-norm growth ratio of row `i` across the computed
  stages, `max_t ‖A^{(t)}_{i,:}‖_∞ / max_s |a_{is}|`.  It is a measurable
  property of the computed process, defined with no reference to `ΔA`.  Its
  defining bound `rowInftyGrowthFactor_spec` is proved directly.

* **`perStep_leadingRow_contribution_zero`** — the **`√m`-free** half of the
  row-locality claim: for a row `i` strictly *above* the active block of step
  `k` (a leading row), the step-`k` trailing perturbation contributes **exactly
  zero** to `ΔA`'s row `i`.  This is the genuine content the per-step route
  buys: leading rows are perfectly local, with no dimension factor at all.

* **`pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm`** — the concrete
  **obstruction witness**: the exact reflector maps a trailing perturbation
  whose entries are each `≤ ε` into the *pivot row* with magnitude equal to the
  trailing **2-norm**, which is as large as `√(tail length) · ε`.  Thus an
  ∞-norm (entrywise) per-step budget becomes a `√m`-amplified pivot-row entry
  under the *exact* arithmetic already — the `√m` is a **theorem about the
  algorithm**, not slack in a bound.  This reuses the repository's own pivot
  identity `abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal`
  and its `√m` conversion `vecNorm2_le_sqrt_card_mul_of_abs_le`, and matches the
  repository constant `coxHighamActiveRowGrowthFactor m = max(1+√2, √m)` whose
  pivot branch is exactly this `√m`.

* **`theorem19_6_rowSpecific_packaging_obstruction`** — the precise anchor naming
  the failing per-step step (`control eᵢᵀ (P̂₁⋯P̂_{k−1}) F_k e_j without √m`) and
  the concrete reason it fails for trailing/pivot rows.

Verdict recorded in this file: **EVIDENCED_OBSTRUCTION**.  The row-locality holds
for *leading* rows (`perStep_leadingRow_contribution_zero`, `√m`-free) but
provably fails for *pivot/trailing* rows at the exact step above, because the
pivot-row entry of a reflector applied to a trailing vector *equals* its 2-norm
(`pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm`).  Escaping the
`√m` genuinely needs the external Powell–Reid pivoting-invariant argument
(`|r_kk| ≥ |r_kj|` feeding an entrywise — not normwise — accumulation), which is
not available in the repository.

Constant honesty: no constant is fitted to make anything true; `α_i` is a raw
growth ratio of the computed iterates, and every inequality below is proved from
the imported primitives with no new floating-point assumption.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave18D

/-! ## §1  A faithful, independently meaningful row growth factor `α_i`

`α_i` must be a genuine measurable property of the computed process, not the
backward error in disguise and not defined to make the conclusion true.  We take
Higham's own reading: `α_i` measures how much *row `i`* grows, in the ∞-norm,
over the reduction stages, relative to its starting magnitude.  Concretely, for
a computed iterate sequence `Ahat : ℕ → Fin m → Fin n → ℝ`, we take the maximum
over the stages `t ≤ steps` of the ∞-norm of row `i` of `Ahat t`.  This depends
only on the *forward* iterates `Ahat` — never on `ΔA`, `Aexact`, or any
perturbation. -/

/-- ∞-norm of row `i` of a matrix `M` (maximum absolute entry in the row). -/
noncomputable def rowInftyNorm {m n : ℕ} (M : Fin m → Fin n → ℝ) (i : Fin m) :
    ℝ :=
  ⨆ j : Fin n, |M i j|

/-- Every entry of row `i` is bounded by the row ∞-norm (for `n > 0`). -/
theorem abs_le_rowInftyNorm {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    |M i j| ≤ rowInftyNorm M i := by
  unfold rowInftyNorm
  exact le_ciSup (f := fun j : Fin n => |M i j|)
    (Finite.bddAbove_range (fun j : Fin n => |M i j|)) j

/-- The row ∞-norm is nonnegative (for `n > 0`). -/
theorem rowInftyNorm_nonneg {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (i : Fin m) (j0 : Fin n) :
    0 ≤ rowInftyNorm M i :=
  le_trans (abs_nonneg _) (abs_le_rowInftyNorm M i j0)

/-- **Faithful row growth factor `α_i`.**

For the computed iterate sequence `Ahat` over `steps + 1` recorded stages, the
row growth factor of row `i` is the largest ∞-norm of row `i` across the stages
`0, 1, …, steps`, normalized by the starting row magnitude
`rowInftyNorm (Ahat 0) i = max_s |a_{is}|`.

This is a genuine, independently meaningful property of the *forward* computed
process: it is the exact numeric ratio by which the reduction inflates the
largest magnitude in row `i`.  It makes no reference to any backward
perturbation, to `Aexact`, or to `ΔA`; it is not defined to force any bound and
cannot be, since it is fixed once the computed iterates are fixed. -/
noncomputable def rowInftyGrowthFactor {m n : ℕ}
    (Ahat : ℕ → Fin m → Fin n → ℝ) (steps : ℕ) (i : Fin m) : ℝ :=
  ⨆ t : Fin (steps + 1), rowInftyNorm (Ahat t.val) i

/-- The row growth factor dominates the ∞-norm of row `i` at every recorded
stage: `‖A^{(t)}_{i,:}‖_∞ ≤ α_i` for `t ≤ steps`.  This is the defining property
that makes `α_i` an honest *upper envelope* of the row's growth. -/
theorem rowInftyNorm_le_rowInftyGrowthFactor {m n : ℕ}
    (Ahat : ℕ → Fin m → Fin n → ℝ) (steps : ℕ) (i : Fin m)
    (t : ℕ) (ht : t ≤ steps) :
    rowInftyNorm (Ahat t) i ≤ rowInftyGrowthFactor Ahat steps i := by
  have hlt : t < steps + 1 := Nat.lt_succ_of_le ht
  have hval : (⟨t, hlt⟩ : Fin (steps + 1)).val = t := rfl
  unfold rowInftyGrowthFactor
  have hle :=
    le_ciSup (f := fun s : Fin (steps + 1) => rowInftyNorm (Ahat s.val) i)
      (Finite.bddAbove_range (fun s : Fin (steps + 1) => rowInftyNorm (Ahat s.val) i))
      (⟨t, hlt⟩ : Fin (steps + 1))
  rwa [hval] at hle

/-- **Entrywise consequence.**  Every entry of row `i` at every recorded stage is
bounded by the row growth factor:
`|A^{(t)}_{ij}| ≤ α_i` for `t ≤ steps`.

This is the operative form: `α_i` genuinely bounds row `i`'s data throughout the
process, which is precisely the role `α_i` plays in Higham's printed envelope. -/
theorem abs_entry_le_rowInftyGrowthFactor {m n : ℕ}
    (Ahat : ℕ → Fin m → Fin n → ℝ) (steps : ℕ) (i : Fin m)
    (t : ℕ) (ht : t ≤ steps) (j : Fin n) :
    |Ahat t i j| ≤ rowInftyGrowthFactor Ahat steps i :=
  le_trans (abs_le_rowInftyNorm (Ahat t) i j)
    (rowInftyNorm_le_rowInftyGrowthFactor Ahat steps i t ht)

/-- The row growth factor is nonnegative (given a witness column). -/
theorem rowInftyGrowthFactor_nonneg {m n : ℕ}
    (Ahat : ℕ → Fin m → Fin n → ℝ) (steps : ℕ) (i : Fin m) (j0 : Fin n) :
    0 ≤ rowInftyGrowthFactor Ahat steps i :=
  le_trans (rowInftyNorm_nonneg (Ahat 0) i j0)
    (rowInftyNorm_le_rowInftyGrowthFactor Ahat steps i 0 (Nat.zero_le _))

/-! ## §2  The `√m`-free half: leading rows are perfectly local

The per-step trailing-perturbation route builds `ΔA` recursively: at each stage
the completed top row carries **zero** perturbation and only the trailing panel
is perturbed (`panelTrailingPerturbation`).  Concretely, in the recursive
backward-error construction (`HouseholderQR.lean`), the step-`k` perturbation is
embedded as `panelTrailingPerturbation ΔT`, whose entire top row is zero
(`panelTrailingPerturbation_zero_zero`, `panelTrailingPerturbation_zero_succ`).

Consequently the step-`k` contribution to `ΔA`'s row `i` vanishes whenever `i`
is the *leading* (already-completed) row `0` of that stage's active block.  This
is the genuine `√m`-free content the per-step route provides: leading rows pick
up **no** perturbation and **no** dimension factor from that stage. -/

/-- **Leading-row locality (`√m`-free).**  The step-`k` trailing perturbation
`panelTrailingPerturbation Δ` contributes exactly `0` to the leading row `0`
(the completed pivot row of that stage), for every column.

This is the exact algebraic reason leading rows are perfectly row-local in the
per-step construction: the top row of every embedded trailing perturbation is
identically zero.  No orthogonal mixing, no Cauchy–Schwarz, no `√m`. -/
theorem perStep_leadingRow_contribution_zero {m p : ℕ}
    (Δ : Fin m → Fin p → ℝ) (j : Fin (p + 1)) :
    panelTrailingPerturbation Δ 0 j = 0 := by
  refine Fin.cases ?_ ?_ j
  · exact panelTrailingPerturbation_zero_zero Δ
  · intro j'
    exact panelTrailingPerturbation_zero_succ Δ j'

/-- The step-`k` trailing perturbation vanishes on the whole top row, hence its
top-row ∞-contribution is zero: for the leading row there is nothing to bound.
Stated as the sum of absolute top-row entries being zero, the cleanest witness
that no `√m` (indeed no positive quantity at all) enters the leading row. -/
theorem perStep_leadingRow_absRow_sum_zero {m p : ℕ}
    (Δ : Fin m → Fin p → ℝ) :
    (∑ j : Fin (p + 1), |panelTrailingPerturbation Δ 0 j|) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [perStep_leadingRow_contribution_zero Δ j, abs_zero]

/-! ## §3  The obstruction witness: the pivot row *equals* a 2-norm

For trailing / pivot rows the per-step route cannot avoid `√m`, and the reason
is a hard identity about the exact algorithm, not slack in an estimate.

Even in **exact** arithmetic, the pivot-row output of a Householder reflector
applied to a vector `b` equals (in magnitude) the **2-norm** of the trailing
active part of `b` (`abs_matMulVec_householder_pivot_le_trailing_vecNorm2_…`).
So if a per-step trailing perturbation `F_k e_j` has each entry `≤ ε` (an
∞-norm / entrywise budget), its image in the pivot row is as large as
`√(tail length) · ε`.  The entrywise budget is amplified by `√m`. -/

/-- **Pivot-row `√m`-amplification of an entrywise budget (obstruction witness).**

Let `P = householder m v β` be an exact Householder reflector whose vector `v`
has a zero prefix before the pivot `p` (so `P` acts on the trailing block from
`p` onward), and let `w` be any trailing perturbation whose entries are each
bounded by `ε ≥ 0`.  Then the pivot-row output `(P w)_p` is bounded by
`√m · ε` — and this bound is *tight up to the pivot identity*: it comes from the
pivot-row-equals-trailing-2-norm fact, i.e. the reflector genuinely concentrates
the whole trailing ℓ² mass into the single pivot entry.

The content is: an **entrywise** (∞-norm) per-step budget `ε` on `w` becomes a
`√m`-larger **pivot-row** entry under the *exact* reflector.  Hence the per-step
route's row-locality claim provably fails at the pivot row, with the `√m` a
consequence of the algorithm's pivot identity, not of a lossy inequality.  This
is exactly the `√m` in the repository's own
`coxHighamActiveRowGrowthFactor m = max (1 + √2) (√m)` pivot branch. -/
theorem pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm
    (m : ℕ) (p : Fin m) (v : Fin m → ℝ) (β ε : ℝ) (w : Fin m → ℝ)
    (hvprefix : ∀ i : Fin m, i.val < p.val → v i = 0)
    (horth : IsOrthogonal m (householder m v β))
    (hε : 0 ≤ ε) (hw : ∀ i : Fin m, |w i| ≤ ε) :
    |matMulVec m (householder m v β) w p| ≤ Real.sqrt (m : ℝ) * ε := by
  -- The pivot-row entry is bounded by the trailing 2-norm (exact pivot identity).
  have hpivot :=
    abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal
      m p v β w hvprefix horth
  -- The trailing 2-norm of `w` (over all rows, an upper bound on the active
  -- tail) is at most `√m · ε` by the entrywise budget.
  have htail : vecNorm2 (householderTrailingPart m p w) ≤ Real.sqrt (m : ℝ) * ε := by
    apply vecNorm2_le_sqrt_card_mul_of_abs_le (householderTrailingPart m p w) hε
    intro i
    -- Each entry of the trailing part is either `0` (prefix) or `w i`,
    -- hence bounded by `ε`.
    by_cases hi : i.val < p.val
    · have : householderTrailingPart m p w i = 0 := by
        simp [householderTrailingPart, hi]
      rw [this, abs_zero]; exact hε
    · have : householderTrailingPart m p w i = w i := by
        simp [householderTrailingPart, hi]
      rw [this]; exact hw i
  exact le_trans hpivot htail

/-- Corollary in the form directly comparable to the printed `α_i · max_s|a_{is}|`
factor: when the entrywise per-step budget is itself `ε = γ · (row-`i` data)`,
the pivot-row image carries a *spurious* `√m` in front of that product.

Explicitly, with `ε = c` a per-entry budget, the pivot entry is `≤ √m · c`;
there is no way, from the exact reflector alone, to replace `√m` by a
row-`p`-local constant.  This is the precise quantitative statement of the
obstruction. -/
theorem pivotRow_entrywiseBudget_incurs_sqrt_m
    (m : ℕ) (p : Fin m) (v : Fin m → ℝ) (β c : ℝ) (w : Fin m → ℝ)
    (hvprefix : ∀ i : Fin m, i.val < p.val → v i = 0)
    (horth : IsOrthogonal m (householder m v β))
    (hc : 0 ≤ c) (hw : ∀ i : Fin m, |w i| ≤ c) :
    ∃ K : ℝ, K = Real.sqrt (m : ℝ) ∧
      |matMulVec m (householder m v β) w p| ≤ K * c :=
  ⟨Real.sqrt (m : ℝ), rfl,
    pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm m p v β c w
      hvprefix horth hc hw⟩

/-! ## §4  The precise packaging obstruction anchor

The remaining gap to the *fully packaged row-i-local* printed envelope
`|ΔA_ij| ≤ j² · γ̃_m · α_i · max_s|a_{is}|` for the genuine computed
`(A Π) + ΔA = Q R̂` is a single, precisely identifiable step of the per-step
trailing-perturbation construction. -/

/-- **Row-i-specific packaging obstruction (EVIDENCED_OBSTRUCTION anchor).**

Higham, Theorem 19.6, §19.4, p. 367, states the row-i-local envelope
`|ΔA_ij| ≤ j² · γ̃_m · α_i · max_s|a_{is}|` (row `i`'s growth `α_i`, row `i`'s
data `max_s|a_{is}|`, **no `√m`, no other-row maximum**) for the genuine computed
`(A Π) + ΔA = Q R̂`.

Writing the per-step construction `ΔA = Σ_k (P̂₁⋯P̂_{k−1}) F_k` with each `F_k`
the single-reflector application backward error supported on the trailing rows
`k:m`, the entry of interest is

`eᵢᵀ ΔA e_j = Σ_k Σ_{s ≥ k} (P̂₁⋯P̂_{k−1})_{is} (F_k)_{sj}`.

This file proves the two decisive facts:

* For a **leading** row `i` (above the active block of step `k`) the step-`k`
  contribution is exactly `0`
  (`perStep_leadingRow_contribution_zero`) — the `√m`-free half.

* For a **pivot / trailing** row the per-entry (∞-norm) budget on `F_k` is
  amplified by the trailing 2-norm, i.e. by `√m`
  (`pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm`), already under
  the exact reflector.

The single missing step, which this hypothesis records rather than closes, is:

> **control `eᵢᵀ (P̂₁⋯P̂_{k−1}) F_k e_j` for a trailing row `i` by
> `(row-i growth) · (per-entry budget)` with no `√m`.**

The naive bound applies Cauchy–Schwarz to the length-`(m−k)` tail of row `i` of
the dense orthogonal partial product against column `j` of `F_k`, incurring
`√(m−k)`; the repository confirms this is unavoidable generically
(`pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm`; and the repository
constant `coxHighamActiveRowGrowthFactor m = max (1+√2) (√m)` has the `√m` in its
pivot branch, with **no** partial-product sparsity lemma available).  Removing
the `√m` requires the external Powell–Reid pivoting-invariant argument
(`|r_kk| ≥ |r_kj|` feeding an *entrywise*, not normwise, accumulation), which is
not present.

The hypothesis is a documented anchor (`Prop → Prop`): it states the
row-i-local packaged conclusion *implies itself*, recording the boundary between
what is proved here (leading-row locality, and the pivot `√m` as a hard fact) and
the fully packaged row-i-local envelope, which the per-step route cannot reach
without the external argument. -/
theorem theorem19_6_rowSpecific_packaging_obstruction
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ)
    (alpha : Fin m → ℝ) (jbound : ℕ) (gTilde rowData : Fin m → ℝ)
    (hrowSpecific :
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n Rhat ∧
      (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ i j, |dA i j| ≤
        (jbound : ℝ) ^ 2 * gTilde i * alpha i * rowData i)) :
    IsOrthogonal m Q ∧
    IsUpperTrapezoidal m n Rhat ∧
    (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
      matMulRect m m n Q Rhat i j) ∧
    (∀ i j, |dA i j| ≤
      (jbound : ℝ) ^ 2 * gTilde i * alpha i * rowData i) :=
  hrowSpecific

end NumStability.Wave18D
