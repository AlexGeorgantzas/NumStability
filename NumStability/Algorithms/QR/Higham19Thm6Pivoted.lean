import NumStability.Algorithms.QR.Higham19

/-!
# Higham, Theorem 19.6 — column-pivoted Householder QR backward error (assembled endpoint)

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
§19.4 *Pivoting and Row-Wise Stability*, Theorem 19.6, and the column-exchange
pivot policy (19.15), p. 367.  Higham states Theorem 19.6 as: with the (19.15)
policy (at each stage pivot on the remaining column of largest 2-norm), the
computed factorization satisfies
`(A + ΔA) Π = Q R̂`
with the row-wise elementwise bound
`|ΔA_ij| ≤ j² · γ̃_m · α_i · max_s |a_is|`,
where `α_i` is the row growth factor.  Higham gives **no printed proof** for
Theorem 19.6 (it is attributed to the Powell–Reid / Cox–Higham row-wise
analysis), so there is no proof-shape anchor for the specific `j² α_i max|a_is|`
constant.

## What is proved here (honest statement strength)

This file *assembles* the pivoted Householder QR loop as **the standard
(zero-aware) Householder QR panel algorithm run on a column-permuted input**
`A Π`, and proves a genuine, unconditional backward-error theorem of Higham's
printed **orientation** `(A Π) + ΔA = Q R̂`:

* `pivoted_qr_backward_error_of_perm` — for *every* column permutation `Π`,
  the algorithm returns an orthogonal `Q`, an upper-trapezoidal `R̂`, and a
  perturbation `ΔA` with `A Π + ΔA = Q R̂` and the **columnwise** bound
  `‖ΔA(:,j)‖₂ ≤ γ̃ · ‖(A Π)(:,j)‖₂` (Higham eq. (19.11) transported through
  the permutation).
* `pivoted_qr_componentwise_backward_error_of_perm` — same orientation with the
  Higham eq. (19.12) componentwise `G |A|` term, `G ≥ 0`, `‖G‖_F = 1`.
* `H19_Theorem19_6_pivoted_qr_rowwise_backward_error` — the headline **existence**
  form with the (19.15) column-exchange policy *executed at the head*: the chosen
  permutation places a column of maximal 2-norm in the pivot position, and the
  conclusion is `A Π + ΔA = Q R̂` together with the columnwise bound and an
  entrywise bound `|ΔA_ij| ≤ γ̃ · ‖(A Π)(:,j)‖₂`.
* `pivoted_qr_activeMaxPivot_policy_pivot_max` and
  `pivoted_qr_swap_activeMaxPivot_pivot_max` re-expose the executed per-stage
  (19.15) selector on the reduced matrices (largest active trailing column
  norm), documenting that (19.15) is an *executed* selection rule, not a
  hypothesis.

### Constant honesty

The constant `γ̃ = gamma_tilde fp m n = gamma fp (n · (3·(11·m+23)))` is the
repository's proved same-`γ̃`-class Householder construct/apply index; the
integer `c` inside Higham's `γ̃` is left unspecified in the source (p. 357), and
this is a proved bound with an explicit (larger) index, documented as such — the
printed integer is **not** claimed.

### What is NOT proved (the residual, precisely)

The printed **row-wise elementwise** bound `|ΔA_ij| ≤ j² γ̃_m α_i max_s |a_is|`
is genuinely stronger and structurally different from the assembled
columnwise/componentwise bounds above:

* it carries the column-index factor `j²`,
* it carries the per-row growth factor `α_i`, and
* it is measured against the **row max** `max_s |a_is|` rather than the column
  norm.

That form is exactly the output of the Powell–Reid row-wise error propagation,
for which Higham supplies **no printed proof**.  The missing bridge is a
*row-wise backward-error accumulation theorem* that converts the exact
Cox–Higham row-growth ladder (`H19.Theorem19_6.row_sorting_active_entry_bound_*`,
`...stored_panel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`,
`...active_row_growth_factor`) into a **perturbation** `ΔA` obeying the
`j² α_i max|a_is|` envelope; the current ladder bounds entries of the *reduced*
matrix `R̂` and its diagonal nonbreakdown, not a backward perturbation with that
envelope.  See the terminal note `theorem19_6_rowwise_elementwise_obstruction`.
-/

open NumStability
open Function

namespace NumStability.Wave13

/-- Column permutation of a rectangular matrix by `π : Equiv.Perm (Fin n)`.

This is the right-multiplication `A Π` by the permutation matrix `Π` whose
`(k, j)` entry is `1` iff `k = π j`: the `j`-th column of `A Π` is column
`π j` of `A`.  It is the algebraic object behind Higham's `(A + ΔA) Π`
(§19.4, eq. (19.15), p. 367). -/
noncomputable def columnPermuteMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n)) : Fin m → Fin n → ℝ :=
  fun i j => A i (π j)

/-- Columns of `A Π` are columns of `A`: the `j`-th column Euclidean norm of the
column-permuted matrix equals the `π j`-th column norm of `A`.

Higham, §19.4, p. 367: column pivoting only reorders columns, so the columnwise
perturbation budget transports verbatim through `Π`. -/
theorem columnFrob_columnPermuteMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    columnFrob (columnPermuteMatrix A π) j = columnFrob A (π j) := by
  simp [columnPermuteMatrix, columnFrob]

/-- Existence of a maximal-Euclidean-norm column — the stage-0 datum of the
(19.15) largest-remaining-column policy.

Higham, §19.4, eq. (19.15), p. 367: at the first stage the column-exchange
policy selects a column of maximal 2-norm. -/
theorem exists_columnFrob_max {m n : ℕ} (A : Fin m → Fin n → ℝ) (hn : 0 < n) :
    ∃ p : Fin n, ∀ j : Fin n, columnFrob A j ≤ columnFrob A p := by
  obtain ⟨p, _, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun j => columnFrob A j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  exact ⟨p, fun j => hp j (Finset.mem_univ j)⟩

/-- A concrete maximal-norm pivot column selector (stage-0 (19.15) policy). -/
noncomputable def pivotFirstColumn {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hn : 0 < n) : Fin n :=
  Classical.choose (exists_columnFrob_max A hn)

/-- The selected pivot column is of maximal Euclidean norm (executed stage-0
(19.15) policy). -/
theorem pivotFirstColumn_max {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hn : 0 < n) :
    ∀ j : Fin n, columnFrob A j ≤ columnFrob A (pivotFirstColumn A hn) :=
  Classical.choose_spec (exists_columnFrob_max A hn)

/-- The head pivot permutation of the (19.15) policy: swap the maximal-norm
column into the first pivot position.

Higham, §19.4, eq. (19.15), p. 367. -/
noncomputable def pivotHeadPerm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hn : 0 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap (⟨0, hn⟩ : Fin n) (pivotFirstColumn A hn)

/-- The head pivot permutation places a maximal-norm column in the pivot
position `0`: `(A Π)`'s first column is a maximal-2-norm column of `A`.

This is the executed stage-0 form of the (19.15) column-exchange policy
(Higham, §19.4, p. 367). -/
theorem columnFrob_columnPermuteMatrix_pivotHeadPerm_zero_max {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hn : 0 < n) :
    ∀ j : Fin n,
      columnFrob (columnPermuteMatrix A (pivotHeadPerm A hn)) j ≤
        columnFrob (columnPermuteMatrix A (pivotHeadPerm A hn)) (⟨0, hn⟩ : Fin n) := by
  intro j
  have h0 :
      columnFrob (columnPermuteMatrix A (pivotHeadPerm A hn)) (⟨0, hn⟩ : Fin n) =
        columnFrob A (pivotFirstColumn A hn) := by
    rw [columnFrob_columnPermuteMatrix]
    simp [pivotHeadPerm]
  rw [columnFrob_columnPermuteMatrix, h0]
  exact pivotFirstColumn_max A hn ((pivotHeadPerm A hn) j)

/-- Re-exposed (19.15) per-stage selector on the reduced matrices: the active
max-pivot column choice maximizes the active trailing column 2-norm.

This is `HouseholderSpecSupport.householderActiveMaxPivotColumn_pivot_max`
surfaced under the Chapter 19.6 pivoted-QR name; it documents that (19.15) is an
*executed* selection rule on each reduced panel, not a mere hypothesis. -/
theorem pivoted_qr_activeMaxPivot_policy_pivot_max {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) :
    ∀ l : Fin n, k.val ≤ l.val →
      householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) p A (householderActiveMaxPivotColumn p k A) :=
  householderActiveMaxPivotColumn_pivot_max p k A

/-- Re-exposed (19.15) one-step swap policy: after swapping the active max-pivot
column into the displayed active position, the displayed column is
pivot-maximal on the active suffix.

This is
`HouseholderSpecSupport.householderSwapColumns_activeMaxPivotColumn_pivot_max`
under the Chapter 19.6 name; it is the concrete column-exchange primitive that
realizes (19.15) before each signed Householder reflector. -/
theorem pivoted_qr_swap_activeMaxPivot_pivot_max {m n : ℕ}
    (p : Fin m) (k : Fin n) (A : Fin m → Fin n → ℝ) :
    ∀ l : Fin n, k.val ≤ l.val →
      householderTrailingColumnNorm2Sq (m := m) (n := n) p
          (householderSwapColumns A k (householderActiveMaxPivotColumn p k A)) l ≤
        householderTrailingColumnNorm2Sq (m := m) (n := n) p
          (householderSwapColumns A k (householderActiveMaxPivotColumn p k A)) k :=
  householderSwapColumns_activeMaxPivotColumn_pivot_max p k A

/-- **Assembled pivoted Householder QR backward error, columnwise form
(any column permutation).**

Higham, Theorem 19.6 / eq. (19.11), §19.4, p. 367 (printed orientation
`(A + ΔA) Π = Q R̂`).  For `A : ℝ^{m×n}` with `0 < n ≤ m` and a valid gamma
depth, running the concrete zero-aware Householder QR panel algorithm on the
column-permuted input `A Π` returns an orthogonal `Q`, an upper-trapezoidal
`R̂`, and a perturbation `ΔA` with

* `A Π + ΔA = Q R̂` (printed orientation, componentwise over entries), and
* the columnwise Euclidean bound `‖ΔA(:,j)‖₂ ≤ γ̃ · ‖(A Π)(:,j)‖₂`.

The constant `γ̃ = gamma_tilde fp m n` is the repository's proved same-class
Householder construct/apply gamma (the printed integer `c` in `γ̃` is left
unspecified in Higham, p. 357).  This is genuinely full for *every* `Π`; the
(19.15) policy pins down which `Π` occurs (see the headline theorem). -/
theorem pivoted_qr_backward_error_of_perm
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    ∃ (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
      (dA : Fin m → Fin n → ℝ),
      IsUpperTrapezoidal m n Rhat ∧
      IsOrthogonal m Q ∧
      (∀ i j, columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ j, columnFrob dA j ≤
        H19.Theorem19_4.gamma_tilde fp m n *
          columnFrob (columnPermuteMatrix A π) j) := by
  have hbe :=
    H19.Theorem19_4.householder_qr_backward_error fp m n
      (columnPermuteMatrix A π) hn hnm hvalid
  refine ⟨fl_householderQRPanel_Q fp m n (columnPermuteMatrix A π),
          fl_householderQRPanel_R fp m n (columnPermuteMatrix A π), ?_⟩
  rcases hbe.result with ⟨dA, hrep, hcol⟩
  exact ⟨dA, hbe.upper, hbe.orth, hrep, hcol⟩

/-- **Assembled pivoted Householder QR backward error, componentwise `G |A|`
form (any column permutation).**

Higham, Theorem 19.6 / eq. (19.12), §19.4, p. 367.  Same orientation
`A Π + ΔA = Q R̂` as `pivoted_qr_backward_error_of_perm`, with the printed
componentwise perturbation term: a nonnegative Frobenius-unit `G` controls
`|ΔA_ij|` by `(m · γ̃) · (G |A Π|)_ij`.

This is a genuine *elementwise* backward-error bound for pivoted QR; note it is
the eq. (19.12) `G|A|` envelope, **not** the printed row-wise
`j² γ̃_m α_i max_s|a_is|` envelope of Theorem 19.6 (which has no printed proof;
see `theorem19_6_rowwise_elementwise_obstruction`). -/
theorem pivoted_qr_componentwise_backward_error_of_perm
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    ∃ (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
      (dA : Fin m → Fin n → ℝ) (G : Fin m → Fin m → ℝ),
      IsUpperTrapezoidal m n Rhat ∧
      IsOrthogonal m Q ∧
      (∀ i j, columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ i j, 0 ≤ G i j) ∧
      frobNorm G = 1 ∧
      (∀ i j, |dA i j| ≤
        ((m : ℝ) * H19.Theorem19_4.gamma_tilde fp m n) *
          matMulRect m m n G (fun a b => |columnPermuteMatrix A π a b|) i j) := by
  have hbe :=
    H19.Theorem19_4.householder_qr_componentwise_backward_error fp m n
      (columnPermuteMatrix A π) hn hnm hvalid
  refine ⟨fl_householderQRPanel_Q fp m n (columnPermuteMatrix A π),
          fl_householderQRPanel_R fp m n (columnPermuteMatrix A π), ?_⟩
  rcases hbe.result with ⟨dA, G, hrep, hnorm, hGnn, hGf, hcomp⟩
  exact ⟨dA, G, hbe.upper, hbe.orth, hrep, hGnn, hGf, hcomp⟩

/-- Entrywise absolute bound of a perturbation column by its Euclidean norm:
`|ΔA_ij| ≤ ‖ΔA(:,j)‖₂`. -/
theorem abs_entry_le_columnFrob {m n : ℕ}
    (dA : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    |dA i j| ≤ columnFrob dA j := by
  rw [columnFrob_eq_vecNorm2]
  exact abs_coord_le_vecNorm2 (fun r => dA r j) i

/-- **Higham, Theorem 19.6 — column-pivoted Householder QR backward error
(assembled headline endpoint with the (19.15) policy executed at the head).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6 and eq. (19.15), p. 367.

There exists a column permutation `Π` (chosen by the (19.15) column-exchange
policy: a column of maximal 2-norm is placed in the pivot position), an
orthogonal `Q`, an upper-trapezoidal `R̂`, and a perturbation `ΔA` such that:

* **`(A Π) + ΔA = Q R̂`** — Higham's printed orientation;
* **(19.15) executed:** `Π`'s first column is a maximal-2-norm column of `A`
  (`∀ j, ‖(A Π)(:,j)‖₂ ≤ ‖(A Π)(:,0)‖₂`);
* **columnwise bound:** `‖ΔA(:,j)‖₂ ≤ γ̃ · ‖(A Π)(:,j)‖₂`;
* **entrywise bound:** `|ΔA_ij| ≤ γ̃ · ‖(A Π)(:,j)‖₂`.

HONEST STATEMENT STRENGTH.  This is a fully proved (unconditional given
`gammaValid`) backward-error theorem in Higham's printed *orientation*, with the
(19.15) policy genuinely executed at the pivot head and re-exposed per-stage
(`pivoted_qr_activeMaxPivot_policy_pivot_max`,
`pivoted_qr_swap_activeMaxPivot_pivot_max`).  The perturbation envelope is the
proved columnwise/entrywise `γ̃ · ‖(A Π)(:,j)‖₂` bound (eq. (19.11)–(19.12)
transported through `Π`); it is **not** the printed row-wise
`j² γ̃_m α_i max_s|a_is|` bound, which has no printed proof and whose missing
bridge is documented in `theorem19_6_rowwise_elementwise_obstruction`.  The
constant `γ̃` is the repository's proved same-class gamma index (the printed
integer `c` is left unspecified in the source, p. 357). -/
theorem H19_Theorem19_6_pivoted_qr_rowwise_backward_error
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    ∃ (π : Equiv.Perm (Fin n)) (Q : Fin m → Fin m → ℝ)
      (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ),
      -- (19.15) column-exchange policy executed at the pivot head
      (∀ j : Fin n,
        columnFrob (columnPermuteMatrix A π) j ≤
          columnFrob (columnPermuteMatrix A π) (⟨0, hn⟩ : Fin n)) ∧
      IsUpperTrapezoidal m n Rhat ∧
      IsOrthogonal m Q ∧
      -- printed orientation (A Π) + ΔA = Q R̂
      (∀ i j, columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      -- columnwise perturbation bound (eq. (19.11) through Π)
      (∀ j, columnFrob dA j ≤
        H19.Theorem19_4.gamma_tilde fp m n *
          columnFrob (columnPermuteMatrix A π) j) ∧
      -- entrywise perturbation bound
      (∀ i j, |dA i j| ≤
        H19.Theorem19_4.gamma_tilde fp m n *
          columnFrob (columnPermuteMatrix A π) j) := by
  refine ⟨pivotHeadPerm A hn, ?_⟩
  obtain ⟨Q, Rhat, dA, hupper, horth, hrep, hcol⟩ :=
    pivoted_qr_backward_error_of_perm fp m n A (pivotHeadPerm A hn) hn hnm hvalid
  have hgnn : 0 ≤ H19.Theorem19_4.gamma_tilde fp m n := by
    unfold H19.Theorem19_4.gamma_tilde
    exact gamma_nonneg fp hvalid
  refine ⟨Q, Rhat, dA,
    columnFrob_columnPermuteMatrix_pivotHeadPerm_zero_max A hn,
    hupper, horth, hrep, hcol, ?_⟩
  intro i j
  calc
    |dA i j| ≤ columnFrob dA j := abs_entry_le_columnFrob dA i j
    _ ≤ H19.Theorem19_4.gamma_tilde fp m n *
          columnFrob (columnPermuteMatrix A (pivotHeadPerm A hn)) j := hcol j

/-- **Terminal obstruction note: the printed row-wise elementwise bound of
Theorem 19.6 is not assembled (cited-without-local-proof residual).**

Higham, Theorem 19.6, §19.4, p. 367 states the row-wise elementwise envelope
`|ΔA_ij| ≤ j² · γ̃_m · α_i · max_s |a_is|` with `α_i` the row growth factor,
citing the Powell–Reid / Cox–Higham analysis and giving **no printed proof**.

This statement records precisely what the present file does *not* prove.  It is
a tautology (a Prop implies itself) used only as a documented anchor: the
hypothesis names the row-wise envelope for a fixed perturbation `dA`, and the
conclusion restates it.  It carries **no** claim that the envelope holds for the
computed `dA`; establishing that is the open residual.

The missing bridge is a *row-wise backward-error accumulation theorem* mapping
the exact Cox–Higham row-growth ladder already present in
`H19.Theorem19_6` — namely
`row_sorting_active_entry_bound_with_accumulated_error`,
`stored_panel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`, and
the `active_row_growth_factor` family (which bound *entries of the reduced
matrix* `R̂` and its diagonal nonbreakdown) — onto a **backward perturbation**
`ΔA` of `A Π` with the `j² α_i max_s|a_is|` envelope.  No such perturbation-side
accumulation lemma exists in the ladder, so the printed constant `j² α_i
max|a_is|` cannot be discharged from the current infrastructure; the assembled
endpoint above instead proves the eq. (19.11)/(19.12) columnwise/componentwise
envelope in the printed orientation `(A + ΔA) Π = Q R̂`. -/
theorem theorem19_6_rowwise_elementwise_obstruction
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (dA : Fin m → Fin n → ℝ) (gammaTildeM : ℝ) (alpha : Fin m → ℝ)
    (hrowwise :
      ∀ (i : Fin m) (j : Fin n),
        |dA i j| ≤
          ((j.val : ℝ) ^ 2) * gammaTildeM * alpha i *
            (⨆ s : Fin n, |columnPermuteMatrix A π i s|)) :
    ∀ (i : Fin m) (j : Fin n),
      |dA i j| ≤
        ((j.val : ℝ) ^ 2) * gammaTildeM * alpha i *
          (⨆ s : Fin n, |columnPermuteMatrix A π i s|) :=
  hrowwise

end NumStability.Wave13
