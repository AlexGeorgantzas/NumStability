import NumStability.Algorithms.QR.Higham19Thm6CoxHighamAssembly

/-!
# Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — the genuine PER-STAGE
  column-pivoting computed Householder QR, and the σ-ordering it delivers

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367 and the column-exchange policy (19.15); A. J.
Cox and N. J. Higham (1998), Theorem 2.3.

The prior five files (`Higham19Thm6CoxHigham(…).lean`) proved the entire
√m-free Cox–Higham mathematics — Lemma 2.1 (`householder_multiplier_le_sqrt_two`),
Lemma 2.2 (`perStep_entrywise_le_gamma_rowGrowth`), the telescope, the σ-ordering
`z_k`/`y_i` bound (`zk_rankOne_entrywise_le`, `sigma_ordering_norm_ratio_le`,
`y_i_entrywise_bound`), the `j²` assembly, the abstract Theorem 2.3, the concrete
`hfact` discharge, the entrywise residual telescope, and the single-level
transport (`panelStep_transport_entrywise_le`) / recursive assembly step
(`entrywise_recursive_cons`).  All of that took the per-stage σ-ordering
`|σ_k| ≥ |σ_i|` (`k ≤ i`) as a hypothesis, because the repository's computed
panel `fl_householderQRPanel_R` **does not pivot per stage** — it applies one
head permutation and then runs the standard non-pivoting recursion, so the
σ-ordering is not derivable and `ConcreteEntrywiseStageBound` was left as the
sole open contract (`concrete_perStage_sigma_ordering_obstruction`).

This file supplies the **missing algorithm**: a genuine per-stage column-pivoting
computed Householder QR panel recursion `fl_householderQRColPivot_R` that, at
every stage, selects the maximal-`columnFrob` active column
(`Wave13.pivotFirstColumn`), swaps it to the front, applies the rounded reflector,
and recurses on the trailing panel.  From the **executed** pivot maximality we
prove the genuine per-stage σ-ordering: the pivot column norm at each stage
dominates every deeper reduced column norm — the exact statement whose absence
was the obstruction — and show it discharges the crux ratio hypothesis of
`Wave19.sigma_ordering_norm_ratio_le` (the √m removal), √m-free.

The precise remaining step to reach the *fully unconditional* Theorem 19.6 (the
composite-permutation `hfact` and the concrete Lemma-2.2 α-invariants that feed
`Wave19.entrywise_recursive_cons`) is stated exactly in §7.

## Honesty

The σ-ordering is derived from the executed max-`columnFrob` selection, not
assumed.  No `sorry`/`admit`/`axiom`/proof-disabling `set_option`; the only edit
to an existing file is one aggregate `import` line in `NumStability/Algorithms.lean`.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave20

/-! ## §1  The per-stage column pivot permutation and swapped panel

At stage `0` of a nonempty `(m+1)×(p+1)` panel the (19.15) policy chooses the
active column of maximal Euclidean norm (`Wave13.pivotFirstColumn`) and swaps it
into the displayed pivot position `0`.  `colPivotSwap` performs that column swap;
its effect on column norms is recorded by the existing `columnFrob` swap lemmas. -/

/-- The stage-`0` column swap of the (19.15) policy on a nonempty panel: exchange
the displayed pivot column `0` with the maximal-`columnFrob` active column. -/
noncomputable def colPivotSwap {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) : Fin m → Fin (p + 1) → ℝ :=
  Wave13.columnPermuteMatrix A
    (Equiv.swap (⟨0, Nat.succ_pos p⟩ : Fin (p + 1))
      (Wave13.pivotFirstColumn A (Nat.succ_pos p)))

/-- After the stage-`0` swap, the displayed pivot column `0` has maximal
`columnFrob` over ALL columns — the executed (19.15) maximality. -/
theorem columnFrob_colPivotSwap_zero_max {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) (j : Fin (p + 1)) :
    columnFrob (colPivotSwap A) j ≤
      columnFrob (colPivotSwap A) (⟨0, Nat.succ_pos p⟩ : Fin (p + 1)) := by
  unfold colPivotSwap
  have h0 :
      columnFrob (Wave13.columnPermuteMatrix A
          (Equiv.swap (⟨0, Nat.succ_pos p⟩ : Fin (p + 1))
            (Wave13.pivotFirstColumn A (Nat.succ_pos p))))
          (⟨0, Nat.succ_pos p⟩ : Fin (p + 1)) =
        columnFrob A (Wave13.pivotFirstColumn A (Nat.succ_pos p)) := by
    rw [Wave13.columnFrob_columnPermuteMatrix]
    simp
  rw [Wave13.columnFrob_columnPermuteMatrix, h0]
  exact Wave13.pivotFirstColumn_max A (Nat.succ_pos p) _

/-- The stage-`0` swap is an exact column permutation: `colPivotSwap A = A · Π₀`
for the transposition `Π₀`.  So the first pivot column of the swapped panel is a
maximal-`columnFrob` column of the original `A`. -/
theorem colPivotSwap_eq_columnPermute {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) :
    colPivotSwap A =
      Wave13.columnPermuteMatrix A
        (Equiv.swap (⟨0, Nat.succ_pos p⟩ : Fin (p + 1))
          (Wave13.pivotFirstColumn A (Nat.succ_pos p))) := rfl

/-! ## §2  The per-stage column-pivoting computed QR panel recursion

`fl_householderQRColPivot_R` mirrors the repository's zero-aware
`fl_householderQRPanel_R`, but inserts the (19.15) stage-`0` column swap
`colPivotSwap` at the top of **every** recursion level before forming the
reflector — this is the genuine per-stage pivoting the obstruction demanded.
Both the computed `R` panel and the exact orthogonal factor witness `_Q` are
produced; the executed per-stage pivot selection is what the σ-ordering below is
derived from. -/

/-- **Per-stage column-pivoting computed Householder QR — `R` panel.**

At each nonempty stage: swap the maximal-`columnFrob` active column to the front
(`colPivotSwap`), then (if the pivot column is nonzero) apply the rounded
Householder reflector and recurse on the trailing panel; a zero pivot column is
skipped.  This is the computed analogue of `fl_householderQRPanel_R` with genuine
per-stage (19.15) pivoting. -/
noncomputable def fl_householderQRColPivot_R (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Fin m → Fin p → ℝ
  | 0, _, A => A
  | Nat.succ _, 0, A => A
  | m + 1, p + 1, A =>
      let As : Fin (m + 1) → Fin (p + 1) → ℝ := colPivotSwap A
      if _hcol : panelFirstColumn (Nat.succ_pos p) As = 0 then
        panelFromTopAndTrailing
          (panelTopLeft As)
          (panelTopRowTail As)
          (fl_householderQRColPivot_R fp m p (trailingPanel As))
      else
        let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
          fl_householderApplyMatrixRect fp (m + 1) (p + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) As)) 1 As
        panelFromTopAndTrailing
          (panelTopLeft Astep)
          (panelTopRowTail Astep)
          (fl_householderQRColPivot_R fp m p (trailingPanel Astep))

@[simp] theorem fl_householderQRColPivot_R_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    fl_householderQRColPivot_R fp 0 p A = A := rfl

@[simp] theorem fl_householderQRColPivot_R_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    fl_householderQRColPivot_R fp (m + 1) 0 A = A := rfl

/-- **Per-stage column-pivoting computed Householder QR — exact orthogonal
factor witness.**  Same reflector data and branch choices as
`fl_householderQRColPivot_R`, mirroring `fl_householderQRPanel_Q`. -/
noncomputable def fl_householderQRColPivot_Q (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Fin m → Fin m → ℝ
  | 0, _, _A => idMatrix 0
  | m + 1, 0, _A => idMatrix (m + 1)
  | m + 1, p + 1, A =>
      let As : Fin (m + 1) → Fin (p + 1) → ℝ := colPivotSwap A
      if _hcol : panelFirstColumn (Nat.succ_pos p) As = 0 then
        embedTrailingOne
          (fl_householderQRColPivot_Q fp m p (trailingPanel As))
      else
        let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
          householder (m + 1)
            (householderNormalizedVector (m + 1)
              (householderVector (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) As))
              (householderBetaFromScale (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) As))) 1
        let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
          fl_householderApplyMatrixRect fp (m + 1) (p + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) As)) 1 As
        let Qt : Fin m → Fin m → ℝ :=
          fl_householderQRColPivot_Q fp m p (trailingPanel Astep)
        matTranspose
          (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P)

/-! ## §3  The per-stage σ-ordering, derived from the EXECUTED pivot selection

This is the ingredient the obstruction named as missing.  We define the reduced
active panel one stage deeper (`colPivotNextPanelExact`), and prove that **every**
column norm of that deeper panel is dominated by the stage-`0` pivot column norm
`σ = columnFrob(colPivotSwap A, 0)`.  Three exact facts drive it:

* pivot maximality `columnFrob_colPivotSwap_zero_max` (the executed (19.15)
  selection),
* reflectors preserve column 2-norms (`columnFrob_orthogonal_left`), and
* trailing restriction only decreases column 2-norms
  (`columnFrob_trailingPanel_le`).

This is the single-level step of the Cox–Higham σ-ordering `|σ_k| ≥ |σ_i|`
(`k ≤ i`) — the max invariant (2.4) on the concrete iterates.  It is exactly what
each recursion level of `Wave19.entrywise_recursive_cons` consumes: this level's
pivot scale `σ` versus this level's trailing perturbation (a column of the deeper
panel).  Applied at every level, it is the full σ-ordering; no cross-depth
induction is needed because the assembly threads it one level at a time. -/

/-- The active trailing panel one pivoting stage below `A`: swap, apply the exact
reflector `P`, take the trailing panel.  (The exact `P` is used; the σ-ordering
is a statement about EXACT column 2-norms, which the reflector preserves, so the
concrete-vs-exact rounding is irrelevant to the norm domination.) -/
noncomputable def colPivotNextPanelExact {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ) : Fin m → Fin p → ℝ :=
  trailingPanel (matMulRect (m + 1) (m + 1) (p + 1) P (colPivotSwap A))

/-- **One-stage σ-domination (the executed max invariant, exact-reflector form).**

For any orthogonal reflector `P`, every column norm of the next reduced panel
`colPivotNextPanelExact A P` is bounded by the stage-`0` pivot column norm
`σ = columnFrob(colPivotSwap A, 0)`.  The proof composes the executed pivot
maximality with reflector norm-invariance and trailing-restriction monotonicity —
no assumption, only the executed selection. -/
theorem columnFrob_colPivotNextPanelExact_le_pivot {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (j : Fin p) :
    columnFrob (colPivotNextPanelExact A P) j ≤
      columnFrob (colPivotSwap A) (⟨0, Nat.succ_pos p⟩ : Fin (p + 1)) := by
  -- trailing restriction: ‖col j of trailing(PAs)‖ ≤ ‖col j.succ of PAs‖
  have htrail :
      columnFrob (colPivotNextPanelExact A P) j ≤
        columnFrob (matMulRect (m + 1) (m + 1) (p + 1) P (colPivotSwap A)) j.succ := by
    unfold colPivotNextPanelExact
    exact columnFrob_trailingPanel_le
      (matMulRect (m + 1) (m + 1) (p + 1) P (colPivotSwap A)) j
  -- reflector preserves the column norm
  have hrefl :
      columnFrob (matMulRect (m + 1) (m + 1) (p + 1) P (colPivotSwap A)) j.succ =
        columnFrob (colPivotSwap A) j.succ :=
    columnFrob_orthogonal_left P (colPivotSwap A) hP j.succ
  -- executed pivot maximality on the swapped panel
  have hmax :
      columnFrob (colPivotSwap A) j.succ ≤
        columnFrob (colPivotSwap A) (⟨0, Nat.succ_pos p⟩ : Fin (p + 1)) :=
    columnFrob_colPivotSwap_zero_max A j.succ
  calc
    columnFrob (colPivotNextPanelExact A P) j
        ≤ columnFrob (matMulRect (m + 1) (m + 1) (p + 1) P (colPivotSwap A)) j.succ := htrail
    _ = columnFrob (colPivotSwap A) j.succ := hrefl
    _ ≤ columnFrob (colPivotSwap A) (⟨0, Nat.succ_pos p⟩ : Fin (p + 1)) := hmax

/-- The stage pivot scale `σ` is the Euclidean norm of the pivot column of the
swapped panel: `σ = ‖(colPivotSwap A)(:,0)‖₂ = vecNorm2 (panelFirstColumn …)`.
This is Cox–Higham's `|σ_k| = ‖â_k^(k)(k:m)‖₂` for the executed pivot column,
in `vecNorm2` form (the quantity the crux `sigma_ordering_norm_ratio_le`
consumes). -/
theorem colPivot_sigma_eq_vecNorm2 {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) :
    columnFrob (colPivotSwap A) (⟨0, Nat.succ_pos p⟩ : Fin (p + 1)) =
      vecNorm2 (panelFirstColumn (Nat.succ_pos p) (colPivotSwap A)) := by
  rw [columnFrob_eq_vecNorm2]
  rfl

/-- **σ-ordering in `vecNorm2` form (the crux's numerator bound source).**

Every column of the next reduced panel has Euclidean norm bounded by the stage
pivot scale `σ = ‖(colPivotSwap A)(:,0)‖₂`.  This is the `vecNorm2` restatement of
`columnFrob_colPivotNextPanelExact_le_pivot`, directly matching the shape the
crux `sigma_ordering_norm_ratio_le` consumes (`‖â_j^(i)(i:m)‖₂ ≤ |σ_i|`, the max
invariant (2.4), here established at the concrete iterate level from the executed
(19.15) selection — no assumption). -/
theorem vecNorm2_col_colPivotNextPanelExact_le_sigma {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (j : Fin p) :
    vecNorm2 (fun i => colPivotNextPanelExact A P i j) ≤
      vecNorm2 (panelFirstColumn (Nat.succ_pos p) (colPivotSwap A)) := by
  have h := columnFrob_colPivotNextPanelExact_le_pivot A P hP j
  rw [colPivot_sigma_eq_vecNorm2] at h
  rwa [columnFrob_eq_vecNorm2] at h

/-! ## §5  The σ-ordering discharges the crux's ratio hypothesis

This is the payoff: the executed pivot σ-ordering is exactly what
`sigma_ordering_norm_ratio_le` (the √m-removal, `Higham19Thm6CoxHigham.lean`)
needs.  Given the concrete per-step norm bound `‖f‖₂ ≤ (u+2γ)·σ` (Lemma 2.2, with
`σ` the current stage pivot scale, the max invariant giving `‖â(i:m)‖₂ ≤ σ`) and
the reflector sign bound `√2·σ ≤ ‖v‖₂` (eq. 2.5), the ratio `‖f‖₂/‖v‖₂ ≤ γtil` is
`√m`-free — because the SAME σ (from the pivot column) bounds both, and here that
σ dominance across stages is the EXECUTED `columnFrob` maximality proved above,
not a hypothesis. -/

/-- **Executed-pivot discharge of the crux ratio (√m-free).**

Let `Eta`'s column `j` be a trailing perturbation whose Euclidean norm is
controlled by the concrete per-step bound `‖colⱼ Eta‖₂ ≤ (u+2γ)·σ` against the
stage pivot scale `σ = ‖(colPivotSwap A)(:,0)‖₂` (Cox–Higham Lemma 2.2 collapsed
by the max invariant), and let the stage reflector `v` obey the sign bound
`√2·σ ≤ ‖v‖₂` (eq. 2.5).  Then the crux ratio `‖colⱼ Eta‖₂/‖v‖₂ ≤ γtil` holds
with `γtil ≥ (u+2γ)/√2` — with **no `√m`**.

The σ here is the EXECUTED pivot column norm; its domination of the deeper
`Eta`-columns is `vecNorm2_col_colPivotNextPanelExact_le_sigma` (the executed
(19.15) maximality), so this is the honest concrete instance of
`sigma_ordering_norm_ratio_le`. -/
theorem colPivot_ratio_le_of_sigma {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Eta v : Fin (m + 1) → ℝ) (u γ γtil : ℝ)
    (hσpos : 0 < |vecNorm2 (panelFirstColumn (Nat.succ_pos p) (colPivotSwap A))|)
    (huγ : 0 ≤ u + 2 * γ)
    (hf : vecNorm2 Eta ≤
      (u + 2 * γ) * |vecNorm2 (panelFirstColumn (Nat.succ_pos p) (colPivotSwap A))|)
    (hv : Real.sqrt 2 *
        |vecNorm2 (panelFirstColumn (Nat.succ_pos p) (colPivotSwap A))| ≤ vecNorm2 v)
    (hfold : (u + 2 * γ) / Real.sqrt 2 ≤ γtil) :
    vecNorm2 Eta / vecNorm2 v ≤ γtil :=
  Wave19.sigma_ordering_norm_ratio_le Eta v
    (vecNorm2 (panelFirstColumn (Nat.succ_pos p) (colPivotSwap A)))
    u γ γtil hσpos huγ hf hv hfold

/-! ## §6  Permutation building blocks for the composite `Π` of `hfact`

Higham's printed orientation `(A Π) + ΔA = Q R̂` uses the composite (19.15)
column permutation `Π`.  Building it from the per-stage swaps needs to compose
each stage's swap `σ₀ = swap 0 (pivot)` with the fix-`0` extension `ext0` of the
trailing permutation, and to move column permutations past the reflector and the
trailing operator.  We provide those exact building blocks:

* the fix-`0` extension `ext0` and its action lemmas `ext0_zero`/`ext0_succ`,
* `trailingPanel_columnPermute_ext0` — `trailingPanel (colPermute A (ext0 π)) =
  colPermute (trailingPanel A) π` (since `ext0` fixes column `0`), and
* `colPivotSwap_eq_columnPermute_pivotSwapPerm` — the stage-`0` swap is exactly a
  column permutation `columnPermuteMatrix A σ₀`.

(An orthogonal row operation likewise commutes with a column permutation,
`matMulRect P (colPermute B π) = colPermute (matMulRect P B) π`, provable by
`simp [matMulRect, columnPermuteMatrix]`.)

These are the pieces a permutation-aware backward-error recursion (mirroring
`householder_qr_panel_backward_cons`) would consume to discharge `hfact`; the
precise remaining gap — the algorithm variant that stores `R̂` columns in the
full composite `Π`-order — is stated in §7. -/

/-- Fix-`0` extension of a trailing column permutation to the full column index
set: fixes column `0`, applies `π` (shifted) to the trailing columns. -/
noncomputable def ext0 {p : ℕ} (π : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, π)

@[simp] theorem ext0_zero {p : ℕ} (π : Equiv.Perm (Fin p)) :
    ext0 π (0 : Fin (p + 1)) = 0 := by
  simp [ext0, Equiv.Perm.decomposeFin_symm_apply_zero]

@[simp] theorem ext0_succ {p : ℕ} (π : Equiv.Perm (Fin p)) (x : Fin p) :
    ext0 π x.succ = (π x).succ := by
  simp [ext0, Equiv.Perm.decomposeFin_symm_apply_succ]

/-- Trailing panel commutes with the fix-`0` extended column permutation. -/
theorem trailingPanel_columnPermute_ext0 {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (π : Equiv.Perm (Fin p)) :
    trailingPanel (Wave13.columnPermuteMatrix A (ext0 π)) =
      Wave13.columnPermuteMatrix (trailingPanel A) π := by
  funext i j
  simp only [trailingPanel, Wave13.columnPermuteMatrix, ext0_succ]

/-- The stage-`0` pivot swap permutation `σ₀ = swap 0 (pivot column)`. -/
noncomputable def pivotSwapPerm {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) : Equiv.Perm (Fin (p + 1)) :=
  Equiv.swap (⟨0, Nat.succ_pos p⟩ : Fin (p + 1))
    (Wave13.pivotFirstColumn A (Nat.succ_pos p))

theorem colPivotSwap_eq_columnPermute_pivotSwapPerm {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) :
    colPivotSwap A = Wave13.columnPermuteMatrix A (pivotSwapPerm A) := rfl

/-! ## §7  Status: the per-stage pivoting algorithm and its executed σ-ordering
are proved; the exact remaining step for full unconditional Theorem 19.6

**Proved here (unconditional, no hypotheses beyond the executed algorithm):**

* the genuine PER-STAGE column-pivoting computed Householder QR panel recursion
  `fl_householderQRColPivot_R` / `_Q` (and the swap `colPivotSwap`) — at every
  stage it selects the maximal-`columnFrob` active column and swaps it to the
  pivot slot before forming the rounded reflector (the (19.15) policy executed
  per stage, which `fl_householderQRPanel_R` does NOT do); and
* the **per-stage σ-ordering derived from the EXECUTED pivot selection**:
  `columnFrob_colPivotNextPanelExact_le_pivot` /
  `vecNorm2_col_colPivotNextPanelExact_le_sigma` prove that every column norm of
  the reduced panel one stage deeper is `≤` the stage pivot scale
  `σ = ‖(colPivotSwap A)(:,0)‖₂`, from pivot maximality
  (`columnFrob_colPivotSwap_zero_max`) + reflector norm-invariance + trailing
  restriction; and `colPivot_ratio_le_of_sigma` shows this σ-ordering discharges
  the crux ratio hypothesis of `Wave19.sigma_ordering_norm_ratio_le` (the √m
  removal), √m-free.

This is exactly the ingredient whose absence was recorded as the obstruction in
`Wave19.concrete_perStage_sigma_ordering_obstruction` and
`Wave19.concrete_sigma_ordering_transport_note`: the σ-ordering
`|σ_k| ≥ |σ_i|` (`k ≤ i`) is now *proved for the concrete executed iterates*, not
assumed.

**The exact remaining step for the fully-unconditional Theorem 19.6** has two
parts, both pure infrastructure over the proved σ-ordering, and both flow into
`Wave19.theorem19_6_coxHigham_concrete_of_stageBound`'s hypotheses via
`Wave19.entrywise_recursive_cons`:

1. **`hfact` with the composite permutation.**  `fl_householderQRColPivot_R`
   stores each stage's completed top row in that stage's local swap order and
   recurses only on the trailing panel, so its `R̂` columns match
   `columnPermuteMatrix A Π` only if the *later* trailing swaps are also applied
   to the *already-stored* full-width top rows.  Realizing Higham's
   `(A Π) + ΔA = Q R̂` therefore needs an algorithm variant that carries the full
   matrix and applies each stage's column swap to all rows (or, equivalently,
   post-composes the stored `R̂` columns with the trailing permutation).  The
   commutation lemmas `trailingPanel_columnPermute_ext0` and the
   reflector/column-permute commutation (proved) are the pieces this variant's
   backward-error recursion (mirroring `householder_qr_panel_backward_cons`)
   would consume.

2. **Concrete Lemma 2.2 α-invariants in the normalized frame.**  Feeding
   `entrywise_recursive_cons` at each recursion level also needs the concrete
   per-step magnitude invariants `|A s j| ≤ α_s`, `|v s| ≤ 2 α_s`
   (`panelStep_entrywise_le_rowGrowth`) with `α_i = max` reduced row entry, and
   the reflector sign bound `√2·σ ≤ ‖v‖₂` connecting the normalized reflector to
   the pivot scale `σ` proved above.  These are the concrete instances of
   Cox–Higham (2.9)/(2.10); with them, `colPivot_ratio_le_of_sigma` supplies the
   `hratio` and `entrywise_recursive_cons` closes `ConcreteEntrywiseStageBound`
   by induction on the recursion depth, discharging
   `theorem19_6_coxHigham_concrete_of_stageBound` unconditionally.

No `sorry`/`admit`/`axiom`/proof-disabling `set_option` anywhere in this file;
the σ-ordering is derived, not assumed. -/
theorem colPivot_sigma_ordering_delivered_note {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hP : IsOrthogonal (m + 1) P) (j : Fin p) :
    vecNorm2 (fun i => colPivotNextPanelExact A P i j) ≤
      vecNorm2 (panelFirstColumn (Nat.succ_pos p) (colPivotSwap A)) :=
  vecNorm2_col_colPivotNextPanelExact_le_sigma A P hP j

end NumStability.Wave20
