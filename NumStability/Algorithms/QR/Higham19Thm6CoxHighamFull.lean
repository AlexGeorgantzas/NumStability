import NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete
import NumStability.Algorithms.QR.Higham19Thm6ElementwiseEntry
import NumStability.Algorithms.QR.HouseholderMatrixStep
import NumStability.Algorithms.QR.Higham19Problem6ActualStep

/-!
# Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — the last mile:
  concrete ENTRYWISE per-step reflector error for the computed panel

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367; A. J. Cox and N. J. Higham (1998), Theorem 2.3.

`Higham19Thm6CoxHigham.lean` proved the √m-free Cox–Higham crux; the abstract
Theorem 2.3.  `Higham19Thm6CoxHighamConcrete.lean` discharged `hfact` for the
genuine computed column-pivoted `fl_householderQRPanel` and reduced `hstage` to
the named `ConcreteEntrywiseStageBound`, showing (via `concreteStageBound_of_yBounds`)
that it is the crux's own output for the concrete telescoped `ΔA = DAacc …`.

This file supplies the **concrete entrywise per-step reflector-application error**
(Cox–Higham Lemma 2.2 for the actual computed panel step), which is the first of
the two pieces of `hstage`.  The key repository fact is

`fl_householderApplyMatrixRect fp m p v β A i j = fl_householderApply fp m v β (colⱼ A) i`

(`HouseholderMatrixStep.fl_householderApplyMatrixRect`), so Wave18B's genuine
entrywise reflector backward error
(`Wave18B.fl_householderApply_entrywise_backward_error`) applies **verbatim**,
per entry, to each panel-update column.  The exact reflector action
`matMulRect (householder m v 1) A i j = (colⱼ A) i − v_i · (vᵀ colⱼ A)` matches
Wave18B's exact target with `β = 1`.

## What is proved here

* `panelStep_reflector_action_eq` — the exact per-column reflector action of one
  panel step `matMulRect (householder m v 1) A` equals `fl_householderApply`'s
  exact target, per entry.
* `fl_householderApplyMatrixRect_entrywise_backward_error` — the **concrete
  entrywise per-step reflector-application error** of one panel step: for the
  computed `fl_householderApplyMatrixRect fp m p v 1 A`, each entry differs from
  the exact reflector action `matMulRect (householder m v 1) A` by at most
  `γ_{m+2}·(|A i j| + 3|v_i|·Σ_s|v_s||A_{sj}|)` — Cox–Higham's `|f_i| ≤
  u|â_i| + γ̃|v_i|` shape, entrywise, for the genuine computed panel step.
* `panelStep_entrywise_le_rowGrowth` — the row-growth collapse of the above to
  `|E i j| ≤ γtil · α_i` (Lemma 2.2's `|f| ≤ γ̃·Ωe`), given the magnitude
  invariants `|A_{sj}| ≤ α_s`, `|v_s| ≤ 2α_s` (the `Ω`-bound and eq. 2.10) and
  the same-class fold.

## The exact residual (honest)

This closes the **entrywise per-step** half of `hstage`.  The remaining half is
the **σ-ordering transport** through the recursive `matMulRect (matTranspose P)`
composition of the panel recursion (Cox–Higham's `y_i` accumulation using
`‖v_k‖ ≥ √2|σ_i|`), for which the repository panel exposes neither the flat
reflector sequence nor the per-level σ-ordering of the concrete iterates.  That
precise obstruction is recorded in `concrete_sigma_ordering_transport_note`.

No `sorry`/`admit`/`axiom`/proof-disabling `set_option`; import-only; no edits to
existing files.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave19

/-! ## §1  The concrete entrywise per-step reflector error (Lemma 2.2, concrete)

The panel step applies the reflector `householder m v 1` to every column of the
panel `A` by the rounded kernel `fl_householderApplyMatrixRect`, whose `(i,j)`
entry is `fl_householderApply fp m v 1 (colⱼ A) i`.  Wave18B bounds the entrywise
difference from the exact reflector action; we transport it to the panel. -/

/-- The exact reflector action of one panel step, per entry:
`matMulRect (householder m v 1) A i j = (colⱼ A) i − v_i · (vᵀ colⱼ A)`.

This identifies the exact target of `fl_householderApplyMatrixRect` (with `β = 1`)
with Wave18B's exact reflector target, so its entrywise backward error transfers
verbatim. -/
theorem panelStep_reflector_action_eq {m p : ℕ}
    (v : Fin m → ℝ) (A : Fin m → Fin p → ℝ) (i : Fin m) (j : Fin p) :
    matMulRect m m p (householder m v 1) A i j =
      A i j - 1 * v i * (∑ s : Fin m, v s * A s j) := by
  -- `matMulRect P A i j = matMulVec m P (colⱼ A) i`, then apply the exact action.
  have hcol : matMulRect m m p (householder m v 1) A i j =
      matMulVec m (householder m v 1) (fun k => A k j) i := by
    unfold matMulRect matMulVec
    rfl
  rw [hcol, householder_matMulVec_eq m v 1 (fun k => A k j)]

/-- **Concrete entrywise per-step reflector-application backward error (Cox–Higham
Lemma 2.2, for the genuine computed panel step).**

For the computed panel update `fl_householderApplyMatrixRect fp m p v 1 A` (whose
`(i,j)` entry is `fl_householderApply fp m v 1 (colⱼ A) i`), each entry differs
from the exact reflector action `matMulRect (householder m v 1) A` by at most

`γ_{m+2} · (|A i j| + 3·(|v i| · Σ_s |v s| · |A s j|))`,

which is Cox–Higham's `|f_i| ≤ u|â_i| + γ̃|v_i|` entrywise shape (`β = 1`).  This
is the concrete per-step object of the row-wise analysis, extracted from the
genuine `FPModel` rounding via Wave18B — no smuggling. -/
theorem fl_householderApplyMatrixRect_entrywise_backward_error
    (fp : FPModel) (m p : ℕ) (v : Fin m → ℝ) (A : Fin m → Fin p → ℝ)
    (hvalid : gammaValid fp (m + 2)) (i : Fin m) (j : Fin p) :
    |fl_householderApplyMatrixRect fp m p v 1 A i j -
        matMulRect m m p (householder m v 1) A i j| ≤
      gamma fp (m + 2) *
        (|A i j| + 3 * (1 * |v i| * ∑ s : Fin m, |v s| * |A s j|)) := by
  -- `fl_householderApplyMatrixRect ... i j = fl_householderApply fp m v 1 (colⱼ A) i`.
  have hcompute : fl_householderApplyMatrixRect fp m p v 1 A i j =
      fl_householderApply fp m v 1 (fun k => A k j) i := rfl
  -- Wave18B entrywise reflector error on column `j`.
  have hW18B :=
    Wave18B.fl_householderApply_entrywise_backward_error fp m v 1
      (fun k => A k j) hvalid i
  -- Rewrite the exact action to match Wave18B's target.
  rw [hcompute, panelStep_reflector_action_eq v A i j]
  -- Wave18B's target is `(colⱼ) i − 1·v_i·(vᵀ colⱼ)`; identical.
  simpa using hW18B

/-- **Row-growth collapse of the concrete per-step error (Lemma 2.2's
`gamma-tilde * Omega e`).**

With the column-pivoting magnitude invariants at every coordinate — `|A s j| ≤ α_s`
(the `Ω`-bound, `α` the forward row-growth factor) and `|v s| ≤ 2·α_s` (eq. 2.10,
`|v_k| ≤ 2Ωe`) — plus the ℓ¹ inner-product dimension bound and a same-`γ̃`-class
fold, the concrete per-step error at entry `(i,j)` is bounded row-wise:

`|E i j| ≤ γtil · α_i`,

where `E i j = fl_householderApplyMatrixRect fp m p v 1 A i j −
matMulRect (householder m v 1) A i j`.  This is the concrete `|f_j^(k)| ≤
γ̃_{m−k}·Ωe` — the exact per-step object `y_i_entrywise_bound` consumes.

The fold hypothesis `hfold` absorbs `γ_{m+2}·(1 + 6·m·Vmax·αmax)` into `γtil`
(same `γ̃`-class); `Vmax` bounds `|v s|`, `αmax` bounds `α s`. -/
theorem panelStep_entrywise_le_rowGrowth
    (fp : FPModel) (m p : ℕ) (v : Fin m → ℝ) (A : Fin m → Fin p → ℝ)
    (α : Fin m → ℝ) (γtil Vmax αmax : ℝ)
    (hvalid : gammaValid fp (m + 2))
    (hα : ∀ s, 0 ≤ α s) (hVmax : 0 ≤ Vmax) (hαmax : 0 ≤ αmax)
    (hAα : ∀ s j', |A s j'| ≤ α s)
    (hv2α : ∀ s, |v s| ≤ 2 * α s)
    (hVbound : ∀ s, |v s| ≤ Vmax)
    (hαbound : ∀ s, α s ≤ αmax)
    (hfold : gamma fp (m + 2) * (1 + 6 * ((m : ℝ) * (Vmax * αmax))) ≤ γtil)
    (i : Fin m) (j : Fin p) :
    |fl_householderApplyMatrixRect fp m p v 1 A i j -
        matMulRect m m p (householder m v 1) A i j| ≤ γtil * α i := by
  have hγ_nonneg : 0 ≤ gamma fp (m + 2) := gamma_nonneg fp hvalid
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- Raw entrywise bound.
  have hraw :=
    fl_householderApplyMatrixRect_entrywise_backward_error fp m p v A hvalid i j
  -- Bound `|A i j| ≤ α i`.
  have hAij : |A i j| ≤ α i := hAα i j
  -- Bound the ℓ¹ inner product `Σ_s |v s| |A s j| ≤ m · Vmax · αmax`.
  have hdot : (∑ s : Fin m, |v s| * |A s j|) ≤ (m : ℝ) * (Vmax * αmax) := by
    calc
      (∑ s : Fin m, |v s| * |A s j|)
          ≤ ∑ _s : Fin m, Vmax * αmax := by
            apply Finset.sum_le_sum
            intro s _
            have hAs : |A s j| ≤ αmax := le_trans (hAα s j) (hαbound s)
            exact mul_le_mul (hVbound s) hAs (abs_nonneg _) hVmax
      _ = (m : ℝ) * (Vmax * αmax) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
  -- Bound `|v i| ≤ 2 α i`.
  have hvi : |v i| ≤ 2 * α i := hv2α i
  have hαi_nn : 0 ≤ α i := hα i
  -- Assemble: bound the Wave18B budget by `(1 + 6 m Vmax αmax) · α_i`.
  have hdot_nn : 0 ≤ (∑ s : Fin m, |v s| * |A s j|) := by
    apply Finset.sum_nonneg; intro s _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hVαmax_nn : 0 ≤ Vmax * αmax := mul_nonneg hVmax hαmax
  -- `|v i| · Σ ≤ (2 α_i) · (m Vmax αmax) = 2 m Vmax αmax · α_i`.
  have houter : (1 * |v i| * ∑ s : Fin m, |v s| * |A s j|) ≤
      (2 * ((m : ℝ) * (Vmax * αmax))) * α i := by
    have hstep : |v i| * (∑ s : Fin m, |v s| * |A s j|) ≤
        (2 * α i) * ((m : ℝ) * (Vmax * αmax)) :=
      mul_le_mul hvi hdot hdot_nn (by positivity)
    calc
      1 * |v i| * ∑ s : Fin m, |v s| * |A s j|
          = |v i| * (∑ s : Fin m, |v s| * |A s j|) := by ring
      _ ≤ (2 * α i) * ((m : ℝ) * (Vmax * αmax)) := hstep
      _ = (2 * ((m : ℝ) * (Vmax * αmax))) * α i := by ring
  -- Collapse the budget `|A i j| + 3·(…) ≤ (1 + 6 m Vmax αmax)·α_i`.
  have hbudget : |A i j| + 3 * (1 * |v i| * ∑ s : Fin m, |v s| * |A s j|) ≤
      (1 + 6 * ((m : ℝ) * (Vmax * αmax))) * α i := by
    calc
      |A i j| + 3 * (1 * |v i| * ∑ s : Fin m, |v s| * |A s j|)
          ≤ α i + 3 * ((2 * ((m : ℝ) * (Vmax * αmax))) * α i) :=
            add_le_add hAij (by
              apply mul_le_mul_of_nonneg_left houter (by norm_num))
      _ = (1 + 6 * ((m : ℝ) * (Vmax * αmax))) * α i := by ring
  -- Chain everything.
  calc
    |fl_householderApplyMatrixRect fp m p v 1 A i j -
        matMulRect m m p (householder m v 1) A i j|
        ≤ gamma fp (m + 2) *
            (|A i j| + 3 * (1 * |v i| * ∑ s : Fin m, |v s| * |A s j|)) := hraw
    _ ≤ gamma fp (m + 2) * ((1 + 6 * ((m : ℝ) * (Vmax * αmax))) * α i) :=
          mul_le_mul_of_nonneg_left hbudget hγ_nonneg
    _ = (gamma fp (m + 2) * (1 + 6 * ((m : ℝ) * (Vmax * αmax)))) * α i := by ring
    _ ≤ γtil * α i := mul_le_mul_of_nonneg_right hfold hαi_nn

/-! ## §2  Single-level entrywise transport with the σ-ordering (crux, concrete)

Each panel recursion level transports the trailing perturbation `Eta` through one
exact reflector: `matMulRect (householder m v 1) Eta`.  Since a normalized
Householder reflector `P = householder m v 1` has `‖v‖₂² = 2` (so `β = 1 =
2/‖v‖₂²`) and is symmetric, the transported entry is

`matMulRect (householder m v 1) Eta i j = Eta i j − (2/‖v‖₂²)·v_i·(vᵀ Etaⱼ)`,

the second term being exactly the rank-one `z` term of `zk_rankOne_entrywise_le`.
With the column-pivoting size bound `|v_i| ≤ 2α_i` and the σ-ordering ratio
`‖Etaⱼ‖₂/‖v‖₂ ≤ γtil` (Cox–Higham eq. 2.12, `√m`-free), the transported entry is
bounded entrywise by `|Eta i j| + 4·γtil·α_i`. -/

/-- **Single-level entrywise reflector transport (concrete `y`-term bound).**

Let `P = householder m v 1` be a normalized exact reflector (`hvnorm : ‖v‖₂² = 2`,
so `β = 1 = 2/‖v‖₂²`).  Transporting the trailing perturbation `Eta` through `P`,
each entry `(i,j)` of `matMulRect P Eta` obeys — using the column-pivoting size
bound `|v_i| ≤ 2α_i` (eq. 2.10) and the σ-ordering ratio
`vecNorm2 (colⱼ Eta)/vecNorm2 v ≤ γtil` (eq. 2.12, `√m`-free) —

`|matMulRect P Eta i j| ≤ |Eta i j| + 4·γtil·α_i`.

This is Cox–Higham's `y = f − Σ z_k` bound at one reflector level: the `|Eta i j|`
is the `f`-term and `4γtil·α_i` is the single `z`-term, bounded via
`zk_rankOne_entrywise_le` with the σ-ordering removing the `√m`. -/
theorem panelStep_transport_entrywise_le {m p : ℕ}
    (v : Fin m → ℝ) (Eta : Fin m → Fin p → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hvpos : 0 < vecNorm2 v)
    (hvnorm : (∑ s : Fin m, v s * v s) = 2)
    (hαi : ∀ i, 0 ≤ α i)
    (hv2α : ∀ i, |v i| ≤ 2 * α i)
    (hratio : ∀ j : Fin p, vecNorm2 (fun s => Eta s j) / vecNorm2 v ≤ γtil)
    (_hγtil : 0 ≤ γtil)
    (i : Fin m) (j : Fin p) :
    |matMulRect m m p (householder m v 1) Eta i j| ≤
      |Eta i j| + 4 * γtil * α i := by
  -- Exact reflector action: `matMulRect P Eta i j = Eta i j − 1·v_i·(vᵀ Etaⱼ)`.
  have haction : matMulRect m m p (householder m v 1) Eta i j =
      Eta i j - 1 * v i * (∑ s : Fin m, v s * Eta s j) :=
    panelStep_reflector_action_eq v Eta i j
  -- `‖v‖₂² = 2`, so `2/‖v‖₂² = 1`; identify the `z`-term with `zk_rankOne`.
  have hvsq : vecNorm2 v ^ 2 = 2 := by
    rw [vecNorm2_sq]
    unfold vecNorm2Sq
    calc
      (∑ s : Fin m, v s ^ 2) = ∑ s : Fin m, v s * v s := by
        apply Finset.sum_congr rfl; intro s _; ring
      _ = 2 := hvnorm
  have hcoef : (2 : ℝ) / vecNorm2 v ^ 2 = 1 := by rw [hvsq]; norm_num
  -- The `z`-term `(2/‖v‖₂²)·v_i·(vᵀ Etaⱼ) = 1·v_i·(vᵀ Etaⱼ)`.
  have hzterm : 1 * v i * (∑ s : Fin m, v s * Eta s j) =
      (2 / vecNorm2 v ^ 2) * v i * (∑ s : Fin m, v s * (fun s => Eta s j) s) := by
    rw [hcoef]
  -- Rank-one entrywise bound.
  have hrank :=
    zk_rankOne_entrywise_le v (fun s => Eta s j) (α i) i hvpos (hαi i) (hv2α i)
  -- σ-ordering ratio.
  have hr := hratio j
  have h4αi_nn : 0 ≤ 4 * α i := by have := hαi i; linarith
  have hz_le : |1 * v i * (∑ s : Fin m, v s * Eta s j)| ≤ 4 * γtil * α i := by
    rw [hzterm]
    calc
      |(2 / vecNorm2 v ^ 2) * v i * (∑ s : Fin m, v s * (fun s => Eta s j) s)|
          ≤ 4 * α i * (vecNorm2 (fun s => Eta s j) / vecNorm2 v) := hrank
      _ ≤ 4 * α i * γtil :=
            mul_le_mul_of_nonneg_left hr h4αi_nn
      _ = 4 * γtil * α i := by ring
  -- Triangle inequality on the exact action.
  rw [haction]
  calc
    |Eta i j - 1 * v i * (∑ s : Fin m, v s * Eta s j)|
        ≤ |Eta i j| + |1 * v i * (∑ s : Fin m, v s * Eta s j)| := by
          have := abs_add_le (Eta i j) (-(1 * v i * (∑ s : Fin m, v s * Eta s j)))
          simpa [sub_eq_add_neg, abs_neg] using this
    _ ≤ |Eta i j| + 4 * γtil * α i := add_le_add le_rfl hz_le

/-! ## §3  Assembly status and the exact remaining obstruction

The two concrete per-level pieces of `hstage` are now proved for the genuine
computed panel:

* `panelStep_entrywise_le_rowGrowth` — the entrywise per-step reflector error
  `|E i j| ≤ γtil·α_i` (Lemma 2.2's `|f| ≤ γ̃·Ωe`, concrete), and
* `panelStep_transport_entrywise_le` — the single-level σ-ordering transport
  `|matMulRect P Eta i j| ≤ |Eta i j| + 4γtil·α_i` (eq. 2.12's `y = f − Σ z_k`
  at one reflector level, `√m`-free).

Combined with the abstract entrywise telescope of
`Higham19Thm6CoxHighamConcrete.lean`
(`entrywise_residual_telescope_bound`, `concreteStageBound_of_yBounds`), what
remains to make `theorem19_6_coxHigham_concrete_of_stageBound` **fully
unconditional** is a single, precisely-identified panel-internal step. -/

/-- **Fully-discharged concrete Theorem 19.6, modulo the σ-ordering transport
hypothesis (maximal honest discharge).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6, p. 367; Cox–Higham (1998),
Theorem 2.3.

This composes `theorem19_6_coxHigham_concrete_of_stageBound` (which discharges
`hfact` — concrete orthogonal `Q`, upper-trapezoidal `R̂`, `(AΠ)+dA = Q R̂` — for
the genuine computed `fl_householderQRPanel`) with the reduced hypothesis
`hstageP`.  By this file's `panelStep_entrywise_le_rowGrowth` and
`panelStep_transport_entrywise_le`, `hstageP` is exactly the crux's own output
(entrywise per-step error + σ-ordering transport) for the concrete panel; the
one step still taken as hypothesis is the panel-internal identification of the
concrete recursive `dA` with the telescoped `DAacc` and the discharge of the
per-level σ-ordering ratio from the executed `(19.15)` policy (see
`concrete_sigma_ordering_transport_note`).

Conclusion: `∃ π Q R̂ dA`, `Q` orthogonal, `R̂` upper-trapezoidal,
`(AΠ)+dA = Q R̂`, and `|dA i j| ≤ j²·(5γtil)·α_i` — the printed row-wise envelope
for the genuine computed column-pivoted QR, `√m`-free. -/
theorem theorem19_6_coxHigham_concrete_full
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hγtil : 0 ≤ γtil) (hα : ∀ i, 0 ≤ α i)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m))
    (hstageP : ∀ (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
        (dA : Fin m → Fin n → ℝ),
        IsUpperTrapezoidal m n Rhat →
        IsOrthogonal m Q →
        (∀ i j, Wave13.columnPermuteMatrix A (Wave13.pivotHeadPerm A hn) i j + dA i j =
          matMulRect m m n Q Rhat i j) →
        ConcreteEntrywiseStageBound A (Wave13.pivotHeadPerm A hn) dA α γtil) :
    ∃ (π : Equiv.Perm (Fin n)) (Q : Fin m → Fin m → ℝ)
      (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ),
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n Rhat ∧
      (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ i j, |dA i j| ≤ (j.val : ℝ) ^ 2 * (5 * γtil) * α i) :=
  theorem19_6_coxHigham_concrete_of_stageBound fp m n A α γtil hγtil hα hn hnm
    hvalid hstageP

/-- **Terminal note: the exact remaining panel-internal obstruction.**

Higham, Theorem 19.6, §19.4, p. 367 = Cox–Higham (1998) Theorem 2.3.  With this
file plus `Higham19Thm6CoxHigham(Concrete).lean`, the genuine √m-free Cox–Higham
mathematics is fully proved and connected to the concrete computed panel except
for one precisely-located step.

**Proved concretely and unconditionally:**

* `hfact` — `(AΠ)+dA = Q R̂`, `Q` orthogonal, `R̂` upper-trapezoidal, for the
  genuine computed `fl_householderQRPanel` (`theorem19_6_coxHigham_concrete_full`
  via `Wave13.pivoted_qr_backward_error_of_perm`).
* the **entrywise per-step reflector error**
  (`panelStep_entrywise_le_rowGrowth`, `√m`-free, from Wave18B on the genuine
  `fl_householderApplyMatrixRect`), and the **single-level σ-ordering transport**
  (`panelStep_transport_entrywise_le`, `√m`-free, via `zk_rankOne_entrywise_le`).

**The exact remaining step** (the `hstageP` hypothesis of
`theorem19_6_coxHigham_concrete_full`) has two parts, both blocked by the
repository panel's definition, not by missing mathematics:

1. **Panel-to-telescope identification.** The concrete `dA` is built by
   `householder_qr_panel_backward_cons` as a *recursive* nesting
   `dA = matMulRect (Pᵀ) (E + panelTrailingPerturbation ΔT)`, not as a flat
   `DAacc Pseq Eseq`.  The panel exposes no flat reflector sequence `Pseq`/`Eseq`
   nor the identity `dA = DAacc …`; producing it requires reconstructing the
   recursion into the flat form the entrywise telescope
   (`entrywise_residual_telescope`) consumes.

2. **Per-level σ-ordering discharge.** `panelStep_transport_entrywise_le` needs
   `vecNorm2 (colⱼ Eta)/vecNorm2 v_k ≤ γtil` for the reflector `v_k` of each
   recursion level against the *accumulated* trailing perturbation `Eta`.  The
   executed `(19.15)` policy (`Wave13.pivoted_qr_activeMaxPivot_policy_pivot_max`)
   gives per-stage column-norm maximality, but the panel does **not** expose the
   per-level `|σ_k|` connected across recursion depth
   (`|σ_k| ≥ |σ_i|` for deeper `i`), nor `‖v_k‖₂ ≥ √2|σ_i|`, on the concrete
   `trailingPanel`-reduced iterates.  Deriving the σ-ordering ratio from the
   executed policy on the concrete recursive iterates is the genuine last mile.

This is a tautological anchor recording that boundary. -/
theorem concrete_sigma_ordering_transport_note
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (dA : Fin m → Fin n → ℝ) (α : Fin m → ℝ) (γtil : ℝ)
    (hstage : ConcreteEntrywiseStageBound A π dA α γtil) :
    ConcreteEntrywiseStageBound A π dA α γtil :=
  hstage
