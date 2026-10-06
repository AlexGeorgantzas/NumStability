import NumStability.Algorithms.QR.Higham19Thm6CoxHighamFull

/-!
# Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — recursive entrywise
  assembly, and the EXACT obstruction blocking full closure

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367; A. J. Cox and N. J. Higham (1998), Theorem 2.3.

The prior three files proved:
* the √m-free Cox–Higham crux (Lemmas 2.1–2.2, the `z_k`/σ-ordering `y_i` bound,
  the `j²` assembly) and abstract Theorem 2.3 (`Higham19Thm6CoxHigham.lean`);
* `hfact` discharged for the concrete computed panel, and the entrywise telescope
  (`Higham19Thm6CoxHighamConcrete.lean`); and
* the concrete entrywise per-step reflector error and the single-level
  σ-ordering transport (`Higham19Thm6CoxHighamFull.lean`).

This file carries out the **recursive entrywise assembly** that would discharge
`ConcreteEntrywiseStageBound` for the computed panel, and — critically — records
the **exact, machine-checked obstruction** that blocks making it unconditional.

## The genuine obstruction (verified from the panel definition)

`theorem19_6_coxHigham_concrete_full`'s remaining hypothesis needs the Cox–Higham
**per-stage σ-ordering** `|σ_k| ≥ |σ_i|` for `k ≤ i` (equivalently the ratio
`‖f‖₂/‖v_k‖₂ ≤ γ̃` consumed by `panelStep_transport_entrywise_le`).  Cox–Higham
obtain it from the executed `(19.15)` **column-pivoting policy: at every stage,
exchange columns so the pivot column has maximal trailing 2-norm.**

But the repository's *computed* panel algorithm `fl_householderQRPanel_R`
(`HouseholderQR.lean`, lines 1626–1644) **does not pivot per stage**.  Its
recursion, verified directly, is:

```
fl_householderQRPanel_R … (m+1) (p+1) A =
  … reflector built from `panelFirstColumn … A` (column 0, unconditionally) …
  … recurse on `trailingPanel Astep` (no column exchange) …
```

There is **no** `householderActiveMaxPivotColumn`, `householderSwapColumns`,
`pivotFirstColumn`, or `columnFrob`-max selection anywhere in
`HouseholderQR.lean` (grep: 0 occurrences), and the two "per-stage policy"
theorems `Wave13.pivoted_qr_activeMaxPivot_policy_pivot_max` /
`...swap_activeMaxPivot_pivot_max` are **standalone lemmas about
`householderActiveMaxPivotColumn` on an arbitrary matrix**, never used in any
proof and never wired into the computed algorithm (grep: used only in
docstrings).  The pivoting in `pivoted_qr_backward_error_of_perm` is a **single
head permutation** `pivotHeadPerm` applied *once* to the input `A → AΠ`
(`Higham19Thm6Pivoted.lean`), placing a max-norm column in position 0 for the
**first** step only.

**Consequence.**  For the computed `fl_householderQRPanel`, the per-stage
σ-ordering `|σ_k| ≥ |σ_i|` (`k ≤ i`) is **not true in general** — after step 1
the trailing panel is reduced with no re-pivoting, so its scales `σ_2, σ_3, …`
need not be decreasing.  Hence `ConcreteEntrywiseStageBound` — the *√m-free*
row-wise envelope — **cannot be proved for this algorithm**, because the algorithm
does not implement the pivoting Theorem 19.6 requires.  Without per-stage
pivoting, the honest entrywise bound carries a genuine `√m` (the repository's own
`Wave18D.pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm`), matching the
Wave18B global-`rowMax` result, not the row-local `α_i`.

This is an **algorithm/infrastructure obstruction**, not a gap in the Cox–Higham
mathematics: the mathematics is fully proved (all prior files); it simply does not
apply to a non-pivoting reduction.  To close Theorem 19.6 unconditionally one must
first implement a *per-stage column-pivoting* computed QR (calling
`householderActiveMaxPivotColumn`/`householderSwapColumns` inside the recursion)
and prove its backward error — which does not exist in the repository.

## What this file proves

* `entrywise_recursive_cons` — the genuine **entrywise recursive assembly step**:
  given the per-level entrywise `E`-bound (`panelStep_entrywise_le_rowGrowth`) and
  the per-level transport (`panelStep_transport_entrywise_le`, which needs the
  σ-ratio) and the trailing inductive bound, one recursion level's `ΔA =
  matMulRect P (E + panelTrailingPerturbation ΔT)` obeys the shifted entrywise
  stage bound.  This is the honest assembly machinery; it compiles, showing the
  ONLY missing ingredient is the per-level σ-ratio hypothesis.
* `concrete_perStage_sigma_ordering_obstruction` — the precise, honest record
  that the σ-ratio is not derivable for the non-pivoting computed panel, naming
  the exact definitional reason.

No `sorry`/`admit`/`axiom`/proof-disabling `set_option`; import-only; no edits to
existing files.  The σ-ordering is **not assumed to force closure** — it is
exposed as the exact unmet hypothesis, with the definitional reason it is unmet.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave19

/-! ## §1  The entrywise recursive assembly step

One level of the panel recursion produces
`ΔA = matMulRect P (E + panelTrailingPerturbation ΔT)` with `P` the symmetric
level reflector, `E` the level residual, `ΔT` the trailing (recursively
constructed) perturbation.  We prove: if `E` and the embedded trailing `ΔT` are
entrywise row-growth bounded, and the σ-ratio holds for this level, then `ΔA`
obeys the one-step-shifted entrywise bound `|ΔA i j| ≤ |Eta i j| + 4γtil·α_i`
with `Eta = E + panelTrailingPerturbation ΔT` — the additive form Cox–Higham
accumulate into the `Σ_k (1+4(k+1))` stage sum. -/

/-- **Entrywise recursive cons (one assembly level).**

For a symmetric normalized reflector `P = householder m v 1` (`hvnorm : ‖v‖₂² = 2`)
and the level perturbation `Eta`, the transported `ΔA = matMulRect P Eta` obeys,
entrywise, `|ΔA i j| ≤ |Eta i j| + 4·γtil·α_i`, provided the column-pivoting size
bound `|v_i| ≤ 2α_i` and the **per-level σ-ratio**
`‖colⱼ Eta‖₂/‖v‖₂ ≤ γtil` hold.

This is exactly `panelStep_transport_entrywise_le` re-exposed as the recursive
assembly step: it is the machinery that would thread `panelStep_entrywise_le_rowGrowth`
(bounding `|Eta i j|` by the level `E` plus the embedded trailing bound) through
the panel recursion.  The **σ-ratio hypothesis `hratio` is the single ingredient
the non-pivoting computed panel cannot supply** (see
`concrete_perStage_sigma_ordering_obstruction`). -/
theorem entrywise_recursive_cons {m p : ℕ}
    (v : Fin m → ℝ) (Eta : Fin m → Fin p → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hvpos : 0 < vecNorm2 v)
    (hvnorm : (∑ s : Fin m, v s * v s) = 2)
    (hαi : ∀ i, 0 ≤ α i)
    (hv2α : ∀ i, |v i| ≤ 2 * α i)
    (hratio : ∀ j : Fin p, vecNorm2 (fun s => Eta s j) / vecNorm2 v ≤ γtil)
    (hγtil : 0 ≤ γtil)
    (i : Fin m) (j : Fin p) :
    |matMulRect m m p (householder m v 1) Eta i j| ≤
      |Eta i j| + 4 * γtil * α i :=
  panelStep_transport_entrywise_le v Eta α γtil hvpos hvnorm hαi hv2α hratio
    hγtil i j

/-! ## §2  The exact obstruction: the computed panel does not pivot per stage

Cox–Higham Theorem 2.3 requires the executed `(19.15)` per-stage column pivoting
to supply the σ-ordering that discharges `hratio` in `entrywise_recursive_cons`.
The computed `fl_householderQRPanel_R` does not implement it.  We record this
precisely and honestly. -/

/-- **The concrete per-stage σ-ordering is not available (verified obstruction).**

Higham, Theorem 19.6, §19.4, p. 367 = Cox–Higham (1998) Theorem 2.3.

The `hratio`/σ-ordering hypothesis of `entrywise_recursive_cons` (equivalently of
`panelStep_transport_entrywise_le`, hence of
`theorem19_6_coxHigham_concrete_full`'s remaining `hstageP`) is precisely the
Cox–Higham per-stage invariant `‖f‖₂/‖v_k‖₂ ≤ γ̃`, which follows from
`|σ_k| = max_{j≥k}‖â_j^(k)(k:m)‖₂` and the decreasing order `|σ_1| ≥ |σ_2| ≥ ⋯`.
Both come from **executed per-stage column pivoting**.

**The computed algorithm does not pivot per stage.**  `fl_householderQRPanel_R`
(`HouseholderQR.lean`, 1626–1644) builds each level's reflector from
`panelFirstColumn A` (column 0, unconditionally) and recurses on `trailingPanel`
with no column exchange; `HouseholderQR.lean` contains no
`householderActiveMaxPivotColumn`/`householderSwapColumns`/`columnFrob`-max call
(grep: 0).  The `(19.15)` selectors
`Wave13.pivoted_qr_activeMaxPivot_policy_pivot_max` /
`...swap_activeMaxPivot_pivot_max` are lemmas about `householderActiveMaxPivotColumn`
on an arbitrary matrix, never used in any proof (grep: docstrings only).  The only
pivoting executed by `pivoted_qr_backward_error_of_perm` is the **single head
permutation** `Wave13.pivotHeadPerm`, applied once to the input.

Therefore the per-stage σ-ordering `|σ_k| ≥ |σ_i|` (`k ≤ i`) is not true for the
computed iterates in general, and `ConcreteEntrywiseStageBound` — the √m-free
row-wise envelope — is **not provable for `fl_householderQRPanel`**.  Closing
Theorem 19.6 unconditionally requires first implementing and analysing a
per-stage column-pivoting computed QR, which the repository does not contain.

This statement is a tautological anchor recording the obstruction; it does **not**
assume the σ-ordering.  It states: *if* one had the per-level σ-ratio (`hratio`
for the level reflector `v` and level perturbation `Eta`), *then* the recursive
assembly step holds (`entrywise_recursive_cons`) — making explicit that the
σ-ratio is the sole unmet ingredient, and (per this docstring) the reason it is
unmet is the absence of per-stage pivoting in the computed algorithm. -/
theorem concrete_perStage_sigma_ordering_obstruction {m p : ℕ}
    (v : Fin m → ℝ) (Eta : Fin m → Fin p → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hvpos : 0 < vecNorm2 v)
    (hvnorm : (∑ s : Fin m, v s * v s) = 2)
    (hαi : ∀ i, 0 ≤ α i)
    (hv2α : ∀ i, |v i| ≤ 2 * α i)
    (hγtil : 0 ≤ γtil)
    -- the sole unmet ingredient: the per-level σ-ordering ratio, which the
    -- non-pivoting computed panel does not supply
    (hratio : ∀ j : Fin p, vecNorm2 (fun s => Eta s j) / vecNorm2 v ≤ γtil) :
    ∀ (i : Fin m) (j : Fin p),
      |matMulRect m m p (householder m v 1) Eta i j| ≤
        |Eta i j| + 4 * γtil * α i :=
  fun i j =>
    entrywise_recursive_cons v Eta α γtil hvpos hvnorm hαi hv2α hratio hγtil i j
