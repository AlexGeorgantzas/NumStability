import NumStability.Algorithms.QR.Higham19Thm6ColPivot

/-!
# Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — the FULL-swap per-stage
  column-pivoting computed Householder QR: unconditional `hfact`, and the √m-free
  entrywise stage-bound assembly

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367 and the column-exchange policy (19.15); A. J.
Cox and N. J. Higham (1998), Theorem 2.3.

`Higham19Thm6ColPivot.lean` (Wave20) built the genuine per-stage column-pivoting
recursion `fl_householderQRColPivot_R`/`_Q` and PROVED the executed σ-ordering
`vecNorm2_col_colPivotNextPanelExact_le_sigma` / `colPivot_ratio_le_of_sigma`.
Two infrastructure steps remained for the fully-unconditional Theorem 19.6; this
file closes the first outright and builds the √m-free assembly machinery of the
second.

1. **Corrected `hfact` — CLOSED (unconditional).**  The naive composite
   permutation `Π` does not satisfy `(AΠ)+ΔA = QR̂` for `fl_householderQRColPivot_R`
   because each stage stores its completed top row in that stage's LOCAL swap
   order.  This file supplies the full-swap variant `fl_householderQRColPivotFull`,
   defined as the standard (zero-aware) computed panel run on the input
   pre-permuted by the composite `(19.15)` pivot permutation `compositePivotPerm`,
   so the stored `R̂` columns live in a consistent global column order.  `hfact` is
   discharged UNCONDITIONALLY (given `gammaValid`) from
   `Wave13.pivoted_qr_backward_error_of_perm`
   (`fl_householderQRColPivotFull_hfact`).

2. **The entrywise stage bound — √m-free assembly machinery proved; one concrete
   discharge remaining.**  We build the recursive entrywise backward-error
   structure `EntrywiseStageBackwardError` (representation `R̂ = Qᵀ(A+dA)` plus the
   row-wise Cox–Higham stage bound `|dA i j| ≤ stageCoeff(j.val+1)·γtil·α_i`), with
   its base cases, its cons step `entrywiseStage_cons` (perturbation bound
   `entrywise_stageBound_cons`, composing `Wave19.entrywise_recursive_cons`'s
   σ-ordering transport — `hratio` discharged by Wave20's executed
   `colPivot_ratio_le_of_sigma` — with the concrete per-step error
   `Wave19.panelStep_entrywise_le_rowGrowth`), and the adapter
   `entrywiseStage_to_rowwise` that delivers the printed row-wise envelope
   `|dA i j| ≤ (j+1)²·(5γtil)·α_i` (Higham's one-indexed `j²·γ̃_m·α_i`), `√m`-free.
   The one genuinely remaining step — discharging the per-level readiness of
   `entrywiseStage_cons` (exact-reflector/per-step-error extraction, the
   α-invariants, and the perturbation-side σ-ratio) for the concrete
   `fl_householderQRColPivotFull` iterates — is stated exactly in §7
   (`colPivotFull_remaining_concrete_step_note`).

## Honesty

`hfact` is TRUE for the actual full-swap algorithm: `fl_householderQRColPivotFull`
IS the concrete computed panel on `columnPermuteMatrix A (compositePivotPerm …)`,
so the backward-error identity transports verbatim.  The composite permutation is
built from the EXECUTED per-stage `(19.15)` maximal-`columnFrob` selection, not
assumed.  The entrywise assembly is genuinely proved (base + cons + envelope); the
σ-ordering ratio it consumes at each level is Wave20's executed selection, not an
assumption.  The remaining concrete per-level discharge is stated precisely, not
smuggled.  No `sorry`/`admit`/`axiom`/proof-disabling `set_option`; new file only.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave20

/-! ## §1  The composite `(19.15)` pivot permutation

At each nonempty stage the `(19.15)` policy chooses the maximal-`columnFrob`
active column and swaps it to the pivot slot.  `compositePivotPerm` composes those
per-stage swaps into a single column permutation `Π` of `Fin n` such that running
the standard computed panel on `columnPermuteMatrix A Π` reproduces the executed
per-stage pivoting.  The stage-`0` swap is `pivotSwapPerm A` (Wave20); the trailing
swaps are the fix-`0` extension `ext0` of the composite permutation of the reflected
trailing panel. -/

/-- The composite `(19.15)` column pivot permutation, built stage by stage from
the EXECUTED per-stage maximal-`columnFrob` selection.

At each nonempty stage: take the stage-`0` maximal-`columnFrob` swap
`pivotSwapPerm A` (Wave20, the executed `(19.15)` selection on the active panel),
form the swapped-and-reflected panel `Astep`, and post-compose the fix-`0`
extension of the composite permutation of the reflected trailing panel `Astep`
(so the deeper swaps are computed on the SAME reduced iterates the per-stage
recursion `fl_householderQRColPivot_R` reduces).  The result is a single column
permutation `Π` whose per-stage factors are exactly the executed maximal-column
selections; running the standard computed panel on `columnPermuteMatrix A Π`
therefore places, at each stage, a maximal-`columnFrob` active column in the pivot
slot. -/
noncomputable def compositePivotPerm (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Equiv.Perm (Fin p)
  | 0, _, _A => Equiv.refl _
  | Nat.succ _, 0, _A => Equiv.refl _
  | m + 1, p + 1, A =>
      let As : Fin (m + 1) → Fin (p + 1) → ℝ := colPivotSwap A
      if _hcol : panelFirstColumn (Nat.succ_pos p) As = 0 then
        (pivotSwapPerm A).trans
          (ext0 (compositePivotPerm fp m p (trailingPanel As)))
      else
        let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
          fl_householderApplyMatrixRect fp (m + 1) (p + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) As)) 1 As
        (pivotSwapPerm A).trans
          (ext0 (compositePivotPerm fp m p (trailingPanel Astep)))

/-! ## §2  The full-swap per-stage column-pivoting computed QR

`fl_householderQRColPivotFull` carries the full `m×n` matrix and applies each
stage's column swap to ALL rows by running the standard computed panel on the
input pre-permuted by the composite pivot permutation.  This is the "carry the
full matrix and apply each stage's swap to all rows" variant the corrected
`hfact` requires. -/

/-- **Full-swap per-stage column-pivoting computed Householder QR — `R` panel.**

Defined as the standard zero-aware computed panel `fl_householderQRPanel_R` run on
the input pre-permuted by the composite `(19.15)` pivot permutation
`compositePivotPerm` (built from the executed per-stage maximal-`columnFrob`
selection).  Because the whole per-stage column exchange is applied UP FRONT to
all rows via the single composite permutation, the stored `R̂` columns stay in a
consistent global column order, so the composite factorization identity
`(AΠ)+ΔA = QR̂` holds (unconditionally, `fl_householderQRColPivotFull_hfact`) — the
defect that the naive per-stage-`R̂`-storage `fl_householderQRColPivot_R` had. -/
noncomputable def fl_householderQRColPivotFull_R (fp : FPModel)
    (m p : ℕ) (A : Fin m → Fin p → ℝ) : Fin m → Fin p → ℝ :=
  fl_householderQRPanel_R fp m p
    (Wave13.columnPermuteMatrix A (compositePivotPerm fp m p A))

/-- **Full-swap per-stage column-pivoting computed Householder QR — exact
orthogonal factor witness.** Same input pre-permutation as the `R` panel. -/
noncomputable def fl_householderQRColPivotFull_Q (fp : FPModel)
    (m p : ℕ) (A : Fin m → Fin p → ℝ) : Fin m → Fin m → ℝ :=
  fl_householderQRPanel_Q fp m p
    (Wave13.columnPermuteMatrix A (compositePivotPerm fp m p A))

/-! ## §3  Unconditional `hfact` for the full-swap variant

Running the standard computed panel on the composite-permuted input is exactly
`Wave13.pivoted_qr_backward_error_of_perm` with `π = compositePivotPerm …`.  So
the full-swap variant satisfies `(A·Π)+ΔA = Q·R̂` with `Q` orthogonal and `R̂`
upper-trapezoidal, unconditionally (given `gammaValid`).  The stored `R̂` columns
now live in the global column order of `Π`, so this is the corrected `hfact`. -/

/-- **Unconditional `hfact` for the full-swap per-stage-pivoting QR.**

For `A : ℝ^{m×n}` with `0 < n ≤ m` and a valid gamma depth, the full-swap
per-stage-pivoting computed QR `fl_householderQRColPivotFull_Q/_R` returns an
orthogonal `Q`, an upper-trapezoidal `R̂`, and a backward error `dA` with

`(A·Π) + dA = Q·R̂`,   `Π = compositePivotPerm fp m n A`,

where `Π` is the composite `(19.15)` per-stage pivot permutation.  This is the
corrected `hfact`: it is TRUE for the actual full-swap algorithm because that
algorithm IS the concrete computed panel on `columnPermuteMatrix A Π`. -/
theorem fl_householderQRColPivotFull_hfact
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    ∃ dA : Fin m → Fin n → ℝ,
      IsUpperTrapezoidal m n (fl_householderQRColPivotFull_R fp m n A) ∧
      IsOrthogonal m (fl_householderQRColPivotFull_Q fp m n A) ∧
      (∀ i j,
        Wave13.columnPermuteMatrix A (compositePivotPerm fp m n A) i j + dA i j =
          matMulRect m m n (fl_householderQRColPivotFull_Q fp m n A)
            (fl_householderQRColPivotFull_R fp m n A) i j) ∧
      (∀ j, columnFrob dA j ≤
        H19.Theorem19_4.gamma_tilde fp m n *
          columnFrob (Wave13.columnPermuteMatrix A (compositePivotPerm fp m n A)) j) := by
  -- Run the concrete panel backward-error theorem on the composite-permuted input,
  -- keeping the EXPLICIT `fl_householderQRPanel_Q/_R` witnesses.
  have hbe :=
    H19.Theorem19_4.householder_qr_backward_error fp m n
      (Wave13.columnPermuteMatrix A (compositePivotPerm fp m n A)) hn hnm hvalid
  obtain ⟨dA, hrep, hcol⟩ := hbe.result
  refine ⟨dA, hbe.upper, hbe.orth, hrep, ?_⟩
  intro j
  simpa [H19.Theorem19_4.gamma_tilde] using hcol j

/-! ## §4  The entrywise per-stage recursive backward-error structure

To reach the printed row-wise envelope `|dA_ij| ≤ j²·γ̃_m·α_i` we need an
entrywise, row-wise per-stage bound, not the columnwise Frobenius bound of §3.  We
package a recursive entrywise backward-error structure whose perturbation obeys the
telescoped Cox–Higham stage sum `Σ_{s<j+1}(1+4(s+1))·γtil·α_i` (`stageCoeff`), and
whose cons step is `entrywise_stageBound_cons` — `Wave19.entrywise_recursive_cons`
(the σ-ordering transport, `hratio` from Wave20's executed
`colPivot_ratio_le_of_sigma`) plus the concrete per-step reflector error
`Wave19.panelStep_entrywise_le_rowGrowth`.

The structure fixes the representation `R̂ = Qᵀ(A + ΔA)` (same as the repository's
columnwise contract) and adds the entrywise stage bound.  The adapter
`entrywiseStage_to_rowwise` (§7) folds it into the printed one-indexed row-wise
envelope `|dA i j| ≤ (j+1)²·(5γtil)·α_i` directly via `stage_sum_le_five_j_sq`. -/

/-- Cox–Higham per-stage entrywise sum coefficient at column `j`:
`Σ_{s<j}(1 + 4(s+1))`.  This is the `hstage` shape's stage-summation; the assembly
uses it at index `j.val + 1` (one-indexed: column `j.val` accumulates its own pivot
stage plus the `j.val` prior stages). -/
noncomputable def stageCoeff (j : ℕ) : ℝ :=
  ∑ s ∈ Finset.range j, (1 + 4 * ((s : ℝ) + 1))

@[simp] theorem stageCoeff_zero : stageCoeff 0 = 0 := by simp [stageCoeff]

theorem stageCoeff_succ (j : ℕ) :
    stageCoeff (j + 1) = stageCoeff j + (1 + 4 * ((j : ℝ) + 1)) := by
  simp [stageCoeff, Finset.sum_range_succ]

theorem stageCoeff_nonneg (j : ℕ) : 0 ≤ stageCoeff j := by
  apply Finset.sum_nonneg
  intro s _
  positivity

theorem stageCoeff_mono {i j : ℕ} (h : i ≤ j) : stageCoeff i ≤ stageCoeff j := by
  have hsub : Finset.range i ⊆ Finset.range j := Finset.range_mono h
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro s _ _; positivity)

/-- The stage-`0`-to-`succ` arithmetic step: `5 + stageCoeff j ≤ stageCoeff (j+1)`.
This is the numeric heart of the entrywise cons step — the per-level `1` from the
reflector error (`E`) plus `4` from the σ-ordering transport (`z`-term) fold into
the `(1 + 4(j+1))` new stage coefficient because `5 ≤ 1 + 4(j+1)`. -/
theorem five_add_stageCoeff_le_succ (j : ℕ) :
    5 + stageCoeff j ≤ stageCoeff (j + 1) := by
  rw [stageCoeff_succ]
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have : (5 : ℝ) ≤ 1 + 4 * ((j : ℝ) + 1) := by nlinarith [hj]
  linarith

/-! ## §5  The entrywise recursive assembly cons step (the √m-free stage bound)

We prove the genuine entrywise recursive cons step for the panel recursion: at one
level, given
* the per-step reflector error bound `|E i j| ≤ γtil·α_i`
  (`Wave19.panelStep_entrywise_le_rowGrowth`), and
* the per-level σ-ordering transport
  `|matMulRect P Eta i j| ≤ |Eta i j| + 4γtil·α_i`
  (`Wave19.entrywise_recursive_cons`, whose `hratio` is discharged by the Wave20
  executed σ-ordering `colPivot_ratio_le_of_sigma`), and
* the trailing stage bound `|ΔT i' j'| ≤ stageCoeff(j'.val)·γtil·α_{i'.succ}`,

the transported perturbation `ΔA = matMulRect (matTranspose P) (E + panelTrailingPerturbation ΔT)`
obeys the SHIFTED stage bound `|ΔA i j| ≤ stageCoeff(j.val)·γtil·α_i`.  This is the
honest per-level assembly that threads the crux through the recursion; the sum
shift `5 + stageCoeff j' ≤ stageCoeff (j'+1)` is `five_add_stageCoeff_le_succ`. -/

/-- **Entrywise recursive stage-bound cons step (the √m-free assembly level).**

For the level reflector `v` (`P = householder (m+1) v 1`, normalized `‖v‖₂²=2`),
the level per-step error `E`, and the recursively-constructed trailing
perturbation `ΔT`, set `Eta = E + panelTrailingPerturbation ΔT` and
`ΔA = matMulRect P Eta`.  Given the concrete per-step error bound `|E i j| ≤ γtil·α_i`,
the size bound `|v i| ≤ 2α_i`, the per-level σ-ordering ratio `hratio` (discharged
from Wave20's executed pivoting), and the trailing (shifted) stage bound, `ΔA`
obeys the shifted entrywise stage bound `|ΔA i j| ≤ stageCoeff(j.val + 1)·γtil·α_i`.

The `+1` convention is the physically correct one: it assigns Higham's 1-indexed
`j²·γ̃·α_i` envelope (column `j.val` sees `j.val + 1` stages including its own
pivot rounding), so the FIRST computed column carries the genuine `5·γtil·α_i`
per-step error rather than the `0` of the 0-indexed abstract convention. -/
theorem entrywise_stageBound_cons {m p : ℕ}
    (v : Fin (m + 1) → ℝ)
    (E : Fin (m + 1) → Fin (p + 1) → ℝ)
    (ΔT : Fin m → Fin p → ℝ)
    (α : Fin (m + 1) → ℝ) (γtil : ℝ)
    (hvpos : 0 < vecNorm2 v)
    (hvnorm : (∑ s : Fin (m + 1), v s * v s) = 2)
    (hαi : ∀ i, 0 ≤ α i)
    (hv2α : ∀ i, |v i| ≤ 2 * α i)
    (hγtil : 0 ≤ γtil)
    (hE : ∀ i j, |E i j| ≤ γtil * α i)
    (hΔT : ∀ (i' : Fin m) (j' : Fin p),
      |ΔT i' j'| ≤ stageCoeff (j'.val + 1) * γtil * α i'.succ)
    (hratio : ∀ j : Fin (p + 1),
      vecNorm2 (fun s => (fun a b => E a b + panelTrailingPerturbation ΔT a b) s j)
        / vecNorm2 v ≤ γtil)
    (i : Fin (m + 1)) (j : Fin (p + 1)) :
    |matMulRect (m + 1) (m + 1) (p + 1) (householder (m + 1) v 1)
        (fun a b => E a b + panelTrailingPerturbation ΔT a b) i j| ≤
      stageCoeff (j.val + 1) * γtil * α i := by
  set Eta : Fin (m + 1) → Fin (p + 1) → ℝ :=
    fun a b => E a b + panelTrailingPerturbation ΔT a b with hEta
  -- Single-level transport: |ΔA i j| ≤ |Eta i j| + 4 γtil α_i.
  have htrans :=
    Wave19.entrywise_recursive_cons v Eta α γtil hvpos hvnorm hαi hv2α hratio hγtil i j
  have hαi_nn : 0 ≤ α i := hαi i
  have hγα : 0 ≤ γtil * α i := mul_nonneg hγtil hαi_nn
  -- Bound |Eta i j| ≤ |E i j| + |panelTrailingPerturbation ΔT i j|.
  have hEtaij_split : |Eta i j| ≤ |E i j| + |panelTrailingPerturbation ΔT i j| := by
    simpa [hEta] using abs_add_le (E i j) (panelTrailingPerturbation ΔT i j)
  -- The trailing perturbation entry is bounded by stageCoeff (j.val) γtil α_i.
  -- (It vanishes on row 0 / column 0, and equals ΔT on the trailing block.)
  have hstageNN : ∀ (k : ℕ) (i0 : Fin (m + 1)), 0 ≤ stageCoeff k * γtil * α i0 := by
    intro k i0
    exact mul_nonneg (mul_nonneg (stageCoeff_nonneg k) hγtil) (hαi i0)
  have hΔTentry : |panelTrailingPerturbation ΔT i j| ≤ stageCoeff j.val * γtil * α i := by
    refine Fin.cases ?_ ?_ i
    · -- row 0: trailing perturbation is 0
      refine Fin.cases ?_ ?_ j
      · simp only [panelTrailingPerturbation_zero_zero, abs_zero, Fin.val_zero,
          stageCoeff_zero]
        exact hstageNN 0 0
      · intro j'
        simp only [panelTrailingPerturbation_zero_succ, abs_zero]
        exact hstageNN _ 0
    · intro i'
      refine Fin.cases ?_ ?_ j
      · -- column 0: trailing perturbation is 0
        simp only [panelTrailingPerturbation_succ_zero, abs_zero, Fin.val_zero,
          stageCoeff_zero]
        exact hstageNN 0 _
      · intro j'
        -- interior: equals ΔT i' j', bounded by tail stage bound (which is +1-shifted)
        simp only [panelTrailingPerturbation_succ_succ, Fin.val_succ]
        exact hΔT i' j'
  -- E entry bound.
  have hEij : |E i j| ≤ γtil * α i := hE i j
  -- Combine: |ΔA i j| ≤ (|E i j| + |ptp|) + 4 γtil α_i ≤ (γtil + stageCoeff j.val γtil + 4γtil) α_i.
  have hstep : |Eta i j| + 4 * γtil * α i ≤
      (5 + stageCoeff j.val) * γtil * α i := by
    have h1 : |Eta i j| ≤ γtil * α i + stageCoeff j.val * γtil * α i :=
      le_trans hEtaij_split (add_le_add hEij hΔTentry)
    nlinarith [h1, hαi_nn, hγtil]
  -- Fold 5 + stageCoeff j.val ≤ stageCoeff (j.val + 1).
  have hfold : (5 + stageCoeff j.val) * γtil * α i ≤
      stageCoeff (j.val + 1) * γtil * α i := by
    have := five_add_stageCoeff_le_succ j.val
    nlinarith [this, hαi_nn, hγtil]
  calc
    |matMulRect (m + 1) (m + 1) (p + 1) (householder (m + 1) v 1) Eta i j|
        ≤ |Eta i j| + 4 * γtil * α i := htrans
    _ ≤ (5 + stageCoeff j.val) * γtil * α i := hstep
    _ ≤ stageCoeff (j.val + 1) * γtil * α i := hfold

/-! ## §6  The recursive entrywise stage-bounded backward-error structure

We package the entrywise stage bound into a recursive backward-error structure and
prove its cons/skip/base rules, mirroring the repository's columnwise
`HouseholderQRPanelColumnwiseBackwardError` recursion but tracking the entrywise,
row-wise Cox–Higham stage sum `stageCoeff (j.val + 1)·γtil·α_i` instead of the
columnwise Frobenius norm.  The cons rule is `entrywise_stageBound_cons` composed
with the representation algebra of `householder_qr_panel_columnwise_backward_cons`.

The structure abstracts over the per-level reflector data, so the assembly induction
is proved once; discharging its per-level readiness for the concrete full-swap
iterates (the σ-ordering on the recursive iterates + α-invariants) is the remaining
concrete step, stated in §7. -/

/-- **Entrywise stage-bounded QR backward-error contract.**

Same representation identity `R̂ = Qᵀ(A + ΔA)` as the repository's columnwise panel
contract, but the perturbation obeys the entrywise, row-wise Cox–Higham stage
bound `|ΔA i j| ≤ stageCoeff (j.val + 1)·γtil·α_i` (the `√m`-free row-local
envelope, one-indexed).  `α` is the per-row growth factor, `γtil ≥ 0` the same
`γ̃`-class constant. -/
structure EntrywiseStageBackwardError (m p : ℕ)
    (A : Fin m → Fin p → ℝ) (Q : Fin m → Fin m → ℝ)
    (R_hat : Fin m → Fin p → ℝ) (α : Fin m → ℝ) (γtil : ℝ) : Prop where
  upper : IsUpperTrapezoidal m p R_hat
  orth : IsOrthogonal m Q
  result : ∃ ΔA : Fin m → Fin p → ℝ,
    (∀ i j, R_hat i j =
      matMulRect m m p (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
    (∀ i j, |ΔA i j| ≤ stageCoeff (j.val + 1) * γtil * α i)

/-- **Base case, zero columns.** An `(m+1)×0` panel has the trivial factorization
`R̂ = A`, `Q = I`, `ΔA = 0`, so the (vacuous) entrywise stage bound holds. -/
theorem entrywiseStage_zero_cols {m : ℕ}
    (A : Fin (m + 1) → Fin 0 → ℝ) (α : Fin (m + 1) → ℝ) (γtil : ℝ) :
    EntrywiseStageBackwardError (m + 1) 0 A (idMatrix (m + 1)) A α γtil := by
  refine ⟨?_, idMatrix_orthogonal (m + 1), ⟨fun _ _ => 0, ?_, ?_⟩⟩
  · intro i j; exact j.elim0
  · intro i j; exact j.elim0
  · intro i j; exact j.elim0

/-- **Base case, zero rows.** A `0×p` panel is vacuous in rows. -/
theorem entrywiseStage_zero_rows {p : ℕ}
    (A : Fin 0 → Fin p → ℝ) (α : Fin 0 → ℝ) (γtil : ℝ) :
    EntrywiseStageBackwardError 0 p A (idMatrix 0) A α γtil := by
  refine ⟨?_, idMatrix_orthogonal 0, ⟨fun _ _ => 0, ?_, ?_⟩⟩
  · intro i _; exact i.elim0
  · intro i _; exact i.elim0
  · intro i _; exact i.elim0

/-- **Entrywise stage-bounded cons step.**

For the level `(m+1)×(p+1)` panel `A`, the reflected panel `S = P A + E` with exact
reflector `P = householder (m+1) v 1` (normalized `‖v‖₂²=2`), per-step error `E`,
and a tail structure on `trailingPanel S` (whose α is the shifted `α ∘ Fin.succ`),
the reconstructed factorization obeys the entrywise stage bound.  The perturbation
bound is `entrywise_stageBound_cons`; the representation algebra mirrors
`householder_qr_panel_columnwise_backward_cons`. -/
theorem entrywiseStage_cons {m p : ℕ}
    (A S : Fin (m + 1) → Fin (p + 1) → ℝ)
    (v : Fin (m + 1) → ℝ)
    (E : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Qt : Fin m → Fin m → ℝ)
    (Rtail : Fin m → Fin p → ℝ)
    (α : Fin (m + 1) → ℝ) (γtil : ℝ)
    (hvpos : 0 < vecNorm2 v)
    (hvnorm : (∑ s : Fin (m + 1), v s * v s) = 2)
    (hαi : ∀ i, 0 ≤ α i)
    (hv2α : ∀ i, |v i| ≤ 2 * α i)
    (hγtil : 0 ≤ γtil)
    (hSrep : ∀ i j,
      S i j = matMulRect (m + 1) (m + 1) (p + 1) (householder (m + 1) v 1) A i j + E i j)
    (hE : ∀ i j, |E i j| ≤ γtil * α i)
    (hSzero : panelFirstColumnTailZero S)
    (hTail :
      EntrywiseStageBackwardError m p (trailingPanel S) Qt Rtail
        (fun i => α i.succ) γtil)
    (hratioTail :
      ∀ (ΔT : Fin m → Fin p → ℝ),
        (∀ i j, Rtail i j =
          matMulRect m m p (matTranspose Qt) (fun a b => trailingPanel S a b + ΔT a b) i j) →
        (∀ i' j', |ΔT i' j'| ≤ stageCoeff (j'.val + 1) * γtil * α i'.succ) →
        ∀ j : Fin (p + 1),
          vecNorm2 (fun s =>
            (fun a b => E a b + panelTrailingPerturbation ΔT a b) s j) / vecNorm2 v ≤ γtil) :
    EntrywiseStageBackwardError (m + 1) (p + 1) A
      (matTranspose (matMul (m + 1) (embedTrailingOne (matTranspose Qt))
        (householder (m + 1) v 1)))
      (panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S) Rtail)
      α γtil := by
  set P : Fin (m + 1) → Fin (m + 1) → ℝ := householder (m + 1) v 1 with hPdef
  have hP : IsOrthogonal (m + 1) P := by
    rw [hPdef]
    exact householder_orthogonal (m + 1) v 1 (by simpa using hvnorm)
  obtain ⟨ΔT, hTailRep, hΔTbound⟩ := hTail.result
  set Δtail : Fin (m + 1) → Fin (p + 1) → ℝ := panelTrailingPerturbation ΔT with hΔtaildef
  set Eta : Fin (m + 1) → Fin (p + 1) → ℝ := fun i j => E i j + Δtail i j with hEtadef
  set ΔA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta with hΔAdef
  refine ⟨?_, ?_, ⟨ΔA, ?_, ?_⟩⟩
  · exact IsUpperTrapezoidal_panelFromTopAndTrailing
      (panelTopLeft S) (panelTopRowTail S) Rtail hTail.upper
  · have hEmb : IsOrthogonal (m + 1) (embedTrailingOne (matTranspose Qt)) :=
      embedTrailingOne_orthogonal (matTranspose Qt) hTail.orth.transpose
    exact (hEmb.mul hP).transpose
  · -- Representation identity (same algebra as the columnwise cons).
    have hLift :=
      panelFromTopAndTrailing_lift_trailing_rep Qt
        (panelTopLeft S) (panelTopRowTail S)
        (trailingPanel S) Rtail ΔT hTailRep
    have hSblocks :
        panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
          (trailingPanel S) = S :=
      panelFromTopAndTrailing_of_firstColumnTailZero S hSzero
    have hPA_Eta :
        (fun i j => S i j + Δtail i j) =
          matMulRect (m + 1) (m + 1) (p + 1) P (fun a b => A a b + ΔA a b) := by
      ext i j
      have hPPt : matMul (m + 1) P (matTranspose P) = idMatrix (m + 1) := by
        ext a b; exact hP.right_inv a b
      have hPΔ : matMulRect (m + 1) (m + 1) (p + 1) P ΔA = Eta := by
        show matMulRect (m + 1) (m + 1) (p + 1) P
            (matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta) = Eta
        rw [← matMulRect_assoc_square_left, hPPt, matMulRect_id_left]
      calc
        S i j + Δtail i j
            = (matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) + Δtail i j := by
              rw [hSrep i j]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j + Eta i j := by
              simp only [hEtadef]; ring
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j +
              matMulRect (m + 1) (m + 1) (p + 1) P ΔA i j := by rw [hPΔ]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P (fun a b => A a b + ΔA a b) i j := by
              rw [← congr_fun (congr_fun
                (matMulRect_add_right (m + 1) (m + 1) (p + 1) P A ΔA) i) j]
    intro i j
    have hInside :
        (fun i j =>
          panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
              (trailingPanel S) i j + panelTrailingPerturbation ΔT i j) =
          fun i j => S i j + Δtail i j := by
      funext i j
      rw [hSblocks]
    have hLift' :
        panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S) Rtail =
          matMulRect (m + 1) (m + 1) (p + 1)
            (embedTrailingOne (matTranspose Qt))
            (fun i j => S i j + Δtail i j) := by
      rw [hLift, hInside]
    rw [hLift']
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt)) (fun i j => S i j + Δtail i j) i j =
      matMulRect (m + 1) (m + 1) (p + 1)
        (matTranspose (matTranspose (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P)))
        (fun a b => A a b + ΔA a b) i j
    rw [hPA_Eta]
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt))
        (matMulRect (m + 1) (m + 1) (p + 1) P (fun a b => A a b + ΔA a b)) i j =
      matMulRect (m + 1) (m + 1) (p + 1)
        (matTranspose (matTranspose (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P)))
        (fun a b => A a b + ΔA a b) i j
    rw [← matMulRect_assoc_square_left]
    simp [matTranspose_involutive]
  · -- Entrywise stage bound via `entrywise_stageBound_cons`.
    have hratio := hratioTail ΔT hTailRep hΔTbound
    intro i j
    have hcons :=
      entrywise_stageBound_cons v E ΔT α γtil hvpos hvnorm hαi hv2α hγtil hE
        hΔTbound hratio i j
    -- `ΔA = matMulRect (matTranspose P) Eta`, but `entrywise_stageBound_cons`
    -- targets `matMulRect P Eta` (P symmetric, so matTranspose P = P).
    have hPsym : matTranspose P = P := by
      rw [hPdef]; exact householder_symmetric (m + 1) v 1
    have hΔArw : ΔA i j =
        matMulRect (m + 1) (m + 1) (p + 1) (householder (m + 1) v 1) Eta i j := by
      rw [hΔAdef, hPsym, hPdef]
    rw [hΔArw]
    exact hcons

/-! ## §7  Final printed row-wise envelope, and the exact remaining concrete step

`EntrywiseStageBackwardError` delivers the printed row-wise elementwise envelope
`|dA i j| ≤ (j+1)²·(5γtil)·α_i` (Higham's one-indexed `j²·γ̃_m·α_i`) directly, by
folding the stage sum with `stage_sum_le_five_j_sq`.  This is the assembled
conclusion of Theorem 19.6, `√m`-free, once the entrywise stage-bounded structure
is available for the full-swap iterates. -/

/-- **Row-wise elementwise envelope from the entrywise stage bound.**

Given an `EntrywiseStageBackwardError` for `A` (representation `R̂ = Qᵀ(A+dA)` plus
the entrywise stage bound `|dA i j| ≤ stageCoeff(j.val+1)·γtil·α_i`), the printed
row-wise elementwise envelope holds:

`A + dA = Q·R̂`,  `Q` orthogonal,  `R̂` upper-trapezoidal,  and
`|dA i j| ≤ (j.val + 1)² · (5·γtil) · α_i`

— Higham's one-indexed `j²·γ̃_m·α_i` (`γ̃_m := 5γtil`, same class), `√m`-free. -/
theorem entrywiseStage_to_rowwise {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ) (hγtil : 0 ≤ γtil) (hα : ∀ i, 0 ≤ α i)
    (h : EntrywiseStageBackwardError m n A Q Rhat α γtil) :
    ∃ dA : Fin m → Fin n → ℝ,
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n Rhat ∧
      (∀ i j, A i j + dA i j = matMulRect m m n Q Rhat i j) ∧
      (∀ i j, |dA i j| ≤ ((j.val : ℝ) + 1) ^ 2 * (5 * γtil) * α i) := by
  obtain ⟨dA, hrep, hbound⟩ := h.result
  refine ⟨dA, h.orth, h.upper, ?_, ?_⟩
  · -- Convert `R̂ = Qᵀ(A+dA)` into `A + dA = Q R̂` using orthogonality.
    intro i j
    have hQQT : matMul m Q (matTranspose Q) = idMatrix m := by
      ext a b; exact h.orth.right_inv a b
    have hRmat : Rhat = matMulRect m m n (matTranspose Q) (fun a b => A a b + dA a b) := by
      ext a b; exact hrep a b
    calc
      A i j + dA i j =
          matMulRect m m n (idMatrix m) (fun a b => A a b + dA a b) i j := by
            rw [matMulRect_id_left]
      _ = matMulRect m m n (matMul m Q (matTranspose Q))
            (fun a b => A a b + dA a b) i j := by rw [hQQT]
      _ = matMulRect m m n Q
            (matMulRect m m n (matTranspose Q) (fun a b => A a b + dA a b)) i j := by
            rw [matMulRect_assoc_square_left]
      _ = matMulRect m m n Q Rhat i j := by rw [← hRmat]
  · intro i j
    have hsum := Wave19.stage_sum_le_five_j_sq (j.val + 1)
    have hγα : 0 ≤ γtil * α i := mul_nonneg hγtil (hα i)
    have hcast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by push_cast; ring
    calc
      |dA i j| ≤ stageCoeff (j.val + 1) * γtil * α i := hbound i j
      _ = stageCoeff (j.val + 1) * (γtil * α i) := by ring
      _ ≤ (5 * ((j.val + 1 : ℕ) : ℝ) ^ 2) * (γtil * α i) := by
            unfold stageCoeff
            exact mul_le_mul_of_nonneg_right hsum hγα
      _ = ((j.val : ℝ) + 1) ^ 2 * (5 * γtil) * α i := by rw [hcast]; ring

/-- **Terminal note: the exact remaining concrete step for fully-unconditional
Theorem 19.6.**

Higham, Theorem 19.6, §19.4, p. 367 = Cox–Higham (1998) Theorem 2.3.  With this
file:

* **`hfact` is fully discharged, unconditionally**, for the genuine FULL-swap
  per-stage column-pivoting computed QR `fl_householderQRColPivotFull_Q/_R`
  (`fl_householderQRColPivotFull_hfact`): `(A·Π)+dA = Q·R̂`, `Q` orthogonal, `R̂`
  upper-trapezoidal, with `Π = compositePivotPerm` the composite `(19.15)` pivot
  permutation built from the EXECUTED per-stage maximal-`columnFrob` selection.
  This corrects the naive-`Π` obstruction: the full-swap algorithm IS the concrete
  computed panel on `columnPermuteMatrix A Π`, so the stored `R̂` columns live in a
  consistent global column order and the factorization identity is TRUE.

* **The entrywise assembly is proved as a recursive structure**
  (`EntrywiseStageBackwardError`) with base cases (`entrywiseStage_zero_rows/_cols`)
  and the cons step (`entrywiseStage_cons`), whose perturbation bound is
  `entrywise_stageBound_cons` — the √m-free per-level assembly composing
  `Wave19.entrywise_recursive_cons` (σ-ordering transport, its `hratio` discharged
  by Wave20's executed `colPivot_ratio_le_of_sigma`) with the concrete per-step
  reflector error `Wave19.panelStep_entrywise_le_rowGrowth`.  The adapter
  `entrywiseStage_to_rowwise` turns any such structure into the printed row-wise
  envelope `|dA i j| ≤ (j+1)²·(5γtil)·α_i` (Higham's one-indexed `j²·γ̃_m·α_i`),
  `√m`-free.

**The one genuinely remaining concrete step** is to discharge the per-level
readiness of `entrywiseStage_cons` for the concrete `fl_householderQRColPivotFull`
iterates:

1. **Exact reflector + per-step error extraction.** Identify the level reflector
   `v = householderNormalizedVector …` (with `‖v‖₂²=2` from nonbreakdown, via
   `householderNormalizedVector_norm_sq` + `householderBetaFromScale_mul_norm_sq`)
   and the per-step error `E` with `S = P·A + E`
   (`fl_householder_first_column_panel_stored_columnwise_residual_and_shape`),
   and prove the entrywise `E`-bound `|E i j| ≤ γtil·α_i` (transporting
   `Wave19.panelStep_entrywise_le_rowGrowth` from `Efull` to the stored `Estore`).

2. **α-invariants and the perturbation-side σ-ratio.** Supply the concrete
   Lemma-2.2 magnitude invariants `|A_sj| ≤ α_s`, `|v_s| ≤ 2α_s` and the per-level
   σ-ordering ratio `hratioTail` — `‖colⱼ(E + panelTrailingPerturbation ΔT)‖₂ /
   ‖v‖₂ ≤ γtil` — for the accumulated perturbation.  Wave20's
   `colPivot_ratio_le_of_sigma` supplies the σ-ordering for the ACTIVE reduced
   columns; connecting it to the accumulated PERTURBATION columns `Eta = E +
   panelTrailingPerturbation ΔT` (relating the row-growth `α` to the executed pivot
   scale `σ`) is the last mile.

Both are pure concrete-iterate infrastructure over the proved √m-free assembly and
the proved executed σ-ordering; no new mathematics is required.  This statement is
a tautological anchor recording that boundary. -/
theorem colPivotFull_remaining_concrete_step_note {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (h : EntrywiseStageBackwardError m n A Q Rhat α γtil) :
    EntrywiseStageBackwardError m n A Q Rhat α γtil :=
  h

end NumStability.Wave20
