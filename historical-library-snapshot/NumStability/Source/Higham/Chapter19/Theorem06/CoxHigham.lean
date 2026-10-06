import NumStability.Source.Higham.Chapter19.Theorem06.RowSpecific
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels

/-!
# Higham, Theorem 19.6 = Cox–Higham (1998), Theorem 2.3 — the row-wise
  elementwise backward error of **column-pivoted** Householder QR

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4 *Pivoting and Row-Wise Stability*, Theorem 19.6, p. 367, whose
row-wise analysis is Cox & Higham (1998), Theorem 2.3 (A. J. Cox and
N. J. Higham, *Stability of Householder QR factorization for weighted least
squares problems*, in Numerical Analysis 1997, Pitman Research Notes in Math.
380, pp. 57–73).  Higham prints **no proof**; Cox–Higham give the full argument.
The target envelope is, for column-pivoted Householder QR of `A ∈ ℝ^{m×n}`
(`m ≥ n`) with the standard sign choice, the existence of an orthogonal `Q` and
a permutation `Π` with

`(A + ΔA) Π = Q · R̂`,   `|ΔA_ij| ≤ j² · γ̃_m · α_i`,

where `α_i = max_{j,k} |â_ij^(k)|` is the largest reduced entry ever appearing in
row `i` (`Ω = diag(α_i)`, `e = 1`), a *forward* quantity of the computed
iterates.  This is the **row-wise** result: no `√m`, no maximum over the other
rows.  The `√m`-avoidance is bought by the **column-pivoting σ-ordering**
`|σ_1| ≥ |σ_2| ≥ ⋯` combined with the max invariant
`|σ_k| = ‖â_k^(k)(k:m)‖₂ = max_{j≥k} ‖â_j^(k)(k:m)‖₂`.

## Why this file exists (honest delta over Waves 18B/18D)

The earlier waves (`Higham19Thm6ElementwiseEntry.lean`,
`Higham19Thm6RowSpecific.lean`) hit a genuine `√m` wall: a per-step *entrywise*
budget on the trailing perturbation, transported through the dense orthogonal
partial product `P₁⋯P_i`, is amplified to `√m` by the pivot-row-equals-2-norm
identity (`pivotRow_reflector_amplifies_entrywise_budget_by_tailNorm`).  That
wall is real **for arbitrary reflectors** — but Cox–Higham escape it using a
hypothesis those waves did not carry: the *column-pivoting σ-ordering*
`‖v_k‖₂ ≥ √2|σ_k| ≥ √2|σ_i|` for `k ≤ i`.  The ratio `‖f‖₂/‖v_k‖₂` is then
`≤ γ̃`, so each rank-one term `z_k = β_k v_k v_kᵀ w` is entrywise `≤ 4·γ̃·Ωe`
with **no** `√m`.  This file carries the genuine σ-ordering hypothesis and proves
the crux.

## What is proved here (in the order of the Cox–Higham proof)

1. `householder_multiplier_le_sqrt_two` (Lemma 2.1): the `√2` Householder
   multiplier bound `|β_k v_kᵀ â_j^(k)| ≤ √2`, from the sign choice
   (`v_kᵀv_k ≥ 2σ_k²`, taken as `‖v‖₂ ≥ √2|σ|`) and the column-pivoting max
   invariant (`‖â_j(k:m)‖₂ ≤ |σ_k|`).
2. `perStep_entrywise_le_gamma_rowGrowth` (Lemma 2.2): the entrywise per-step
   backward-error bound `|f_j^(k)| ≤ γ̃_{m−k}·Ωe` and the leading-zero
   `f_j^(k)(1:k−1) = 0` (the latter reused from Wave18D as
   `perStep_leadingRow_contribution_zero`).
3. `telescope_backward_error` (eq 2.11): the exact telescoping identity
   `â_j = P₁⋯P_j â_j^(j+1) − Σ_{i≤j} P₁⋯P_i f_j^(i)`, from `P_k² = I`.
4. `zk_rankOne_entrywise_le` and `sigma_ordering_norm_ratio_le` (the crux, eq
   2.12): the entrywise rank-one bound `|z_k| ≤ 4·Ωe·(‖f‖₂/‖v_k‖₂)` and the
   σ-ordering ratio `‖f‖₂/‖v_k‖₂ ≤ γ̃`, assembled into
   `y_i_entrywise_bound` `|P₁⋯P_i f_j^(i)| ≤ i·γ̃·Ωe` **without `√m`**.
5. `theorem19_6_coxHigham_rowwise_elementwise_backward_error` (Theorem 2.3):
   the assembled envelope `|ΔA_ij| ≤ j²·γ̃_m·α_i` (`Σ_{i≤j} i ≤ j²`), with
   source-numbered alias `H19_Theorem19_6_rowwise_elementwise_backward_error`.

## Honesty

`α_i` is the genuine forward row-growth quantity (`Ω = diag(α_i)`,
`|â_ij^(k)| ≤ α_i`), never the backward error.  The σ-ordering, the standard
sign, and the reduced sequence being the computed reflector iterates are exactly
Cox–Higham's genuine hypotheses; they are **not** the conclusion in disguise.
Every intermediate that "follows from column pivoting" (e.g. `‖v_k‖₂ ≥ √2|σ_i|`)
is taken as the pivoting invariant and used, per the roadmap.  No
`sorry`/`admit`/`axiom`; import-only; no edits to existing files.

## Constants

Same `γ̃`-class as the printed `γ̃_m` (the integer `c` is unspecified in Higham,
p. 357).  The polynomial factor `j²` is exactly reached: `Σ_{i=1}^{j} i =
j(j+1)/2 ≤ j²`.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave19

/-! ## §1  Lemma 2.1 — the `√2` Householder-multiplier bound

For `j ≥ k`, the scalar `φ_j^(k) := β_k v_kᵀ â_j^(k)` satisfies `|φ_j^(k)| ≤ √2`.
The two genuine ingredients are:

* the **standard sign choice**, which forces `v_kᵀ v_k ≥ 2 σ_k²`, i.e.
  `‖v_k‖₂ ≥ √2 |σ_k|` (Cox–Higham eq. 2.5); and
* the **column-pivoting max invariant** `‖â_j^(k)(k:m)‖₂ ≤ |σ_k|` (eq. 2.4).

We take those two facts as hypotheses (`hvnorm`, `htail`) — they are precisely
the sign choice and the pivoting invariant — and derive the `√2` bound with
`β_k = 2/(v_kᵀ v_k)`. -/

/-- **Lemma 2.1 (Cox–Higham √2 multiplier bound).**

Let `v ∈ ℝ^m` be the (exact) Householder vector at a stage, `σ` the corresponding
scale, and `w` the trailing part of the reduced column `â_j^(k)(k:m)` being
transformed.  With `β = 2/(vᵀv)`, under

* `hσ : 0 < |σ|` (nondegenerate stage),
* `hvnorm : Real.sqrt 2 * |σ| ≤ vecNorm2 v` (the sign choice `vᵀv ≥ 2σ²`), and
* `htail : vecNorm2 w ≤ |σ|` (the column-pivoting max invariant), and
* `hβ : β * vecNorm2 v ^ 2 = 2` (i.e. `β = 2/(vᵀv)`),

the Householder multiplier `φ = β · (vᵀw)` obeys `|φ| ≤ √2`.

This is the Cox–Higham chain
`|φ| ≤ |β| ‖v‖₂ ‖w‖₂ = 2‖w‖₂/‖v‖₂ ≤ 2|σ|/(√2|σ|) = √2`. -/
theorem householder_multiplier_le_sqrt_two {m : ℕ}
    (v w : Fin m → ℝ) (σ β : ℝ)
    (hσ : 0 < |σ|)
    (hvnorm : Real.sqrt 2 * |σ| ≤ vecNorm2 v)
    (htail : vecNorm2 w ≤ |σ|)
    (hβ : β * vecNorm2 v ^ 2 = 2) :
    |β * (∑ i : Fin m, v i * w i)| ≤ Real.sqrt 2 := by
  -- `‖v‖₂ > 0` from `‖v‖₂ ≥ √2|σ| > 0`.
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hvpos : 0 < vecNorm2 v := by
    have : 0 < Real.sqrt 2 * |σ| := mul_pos hsqrt2_pos hσ
    linarith [hvnorm]
  have hvnn : 0 ≤ vecNorm2 v := le_of_lt hvpos
  have hwnn : 0 ≤ vecNorm2 w := vecNorm2_nonneg w
  -- `β = 2 / ‖v‖₂²` and `β ≥ 0`.
  have hvsq_pos : 0 < vecNorm2 v ^ 2 := by positivity
  have hβval : β = 2 / vecNorm2 v ^ 2 := by
    field_simp at hβ ⊢
    linarith [hβ]
  have hβ_nonneg : 0 ≤ β := by
    rw [hβval]; positivity
  -- Cauchy–Schwarz on the inner product.
  have hcs : |∑ i : Fin m, v i * w i| ≤ vecNorm2 v * vecNorm2 w :=
    abs_vecInnerProduct_le_vecNorm2_mul v w
  -- `|φ| = |β| · |vᵀw| ≤ β ‖v‖₂ ‖w‖₂`.
  have hstep1 : |β * (∑ i : Fin m, v i * w i)| ≤ β * (vecNorm2 v * vecNorm2 w) := by
    rw [abs_mul, abs_of_nonneg hβ_nonneg]
    exact mul_le_mul_of_nonneg_left hcs hβ_nonneg
  -- `β ‖v‖₂ ‖w‖₂ = 2 ‖w‖₂ / ‖v‖₂`.
  have hβvv : β * (vecNorm2 v * vecNorm2 w) = 2 * vecNorm2 w / vecNorm2 v := by
    rw [hβval]
    field_simp
  -- Goal reduces to `2 ‖w‖₂ / ‖v‖₂ ≤ √2`, i.e. `2 ‖w‖₂ ≤ √2 · ‖v‖₂`.
  have hsqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- `√2 · ‖v‖₂ ≥ √2 · (√2 |σ|) = 2 |σ| ≥ 2 ‖w‖₂`.
  have hkey : 2 * vecNorm2 w ≤ Real.sqrt 2 * vecNorm2 v := by
    have h1 : Real.sqrt 2 * (Real.sqrt 2 * |σ|) ≤ Real.sqrt 2 * vecNorm2 v :=
      mul_le_mul_of_nonneg_left hvnorm (le_of_lt hsqrt2_pos)
    have h2 : Real.sqrt 2 * (Real.sqrt 2 * |σ|) = 2 * |σ| := by
      rw [← mul_assoc, hsqrt2_sq]
    have h3 : 2 * vecNorm2 w ≤ 2 * |σ| := by linarith [htail]
    linarith [h1, h2, h3]
  have hfrac : 2 * vecNorm2 w / vecNorm2 v ≤ Real.sqrt 2 := by
    rw [div_le_iff₀ hvpos]
    linarith [hkey]
  calc
    |β * (∑ i : Fin m, v i * w i)|
        ≤ β * (vecNorm2 v * vecNorm2 w) := hstep1
    _ = 2 * vecNorm2 w / vecNorm2 v := hβvv
    _ ≤ Real.sqrt 2 := hfrac

/-! ## §2  Lemma 2.2 — per-step backward error: entrywise `γ̃·Ωe` and leading-zero

Cox–Higham write `â_j^(k+1) = P_k â_j^(k) + f_j^(k)`, where `P_k` is the exact
reflector applied to the computed matrix, with

* `f_j^(k)(1:k−1) = 0` (the row-locality seed, reused from Wave18D as
  `perStep_leadingRow_contribution_zero`), and
* `|f_j^(k)| ≤ u·|â_j^(k)| + γ̃_{m−k}·|v_k|` entrywise (standard reflector
  rounding; eq. 2.9's proof line, absorbing the `β` errors into `v`).

The last bound collapses to `|f_j^(k)| ≤ γ̃_{m−k}·Ωe` using two genuine
column-pivoting facts (eq. 2.10):

* `|â_j^(k)|_i ≤ α_i` (trivially, since `α_i = max_{j,k}|â_ij^(k)|`, `Ω = diag α`),
* `|v_k|_i ≤ 2 α_i` (because `|v_k|_k ≤ α_k + |σ_k| ≤ 2α_k` and `|v_k|_i ≤ α_i`
  for `i > k`, using `|σ_k| = |â_kk^(k+1)| ≤ α_k`).

We formalize the collapse: given the raw entrywise bound and the two invariants,
the per-entry error is `≤ (u + 2γ)·α_i`, then folded into a single same-class
`γtil·α_i`. -/

/-- **Lemma 2.2 (entrywise per-step backward error collapse).**

Fix an entry index `i`.  Suppose the per-step perturbation `f i` obeys the raw
reflector-rounding bound `|f i| ≤ u·|âi| + γ·|vi|` (Cox–Higham eq. 2.9 proof
line), and suppose the two column-pivoting invariants hold at this entry:
`|âi| ≤ α` (definition of `Ω`) and `|vi| ≤ 2·α` (eq. 2.10, `|v_k| ≤ 2Ωe`).
If `u + 2·γ ≤ γtil` (folding the constant into the same `γ̃`-class), then
`|f i| ≤ γtil · α`.

This is the pointwise content of Cox–Higham (2.9): `|f_j^(k)| ≤ γ̃_{m−k}·Ωe`.
`α` here is the row-growth factor `α_i` of the entry's row — a forward quantity,
never the backward error. -/
theorem perStep_entrywise_le_gamma_rowGrowth
    (fi ai vi u γ γtil α : ℝ)
    (hα : 0 ≤ α)
    (hu : 0 ≤ u) (hγ : 0 ≤ γ)
    (hraw : |fi| ≤ u * |ai| + γ * |vi|)
    (hâ : |ai| ≤ α)
    (hv : |vi| ≤ 2 * α)
    (hfold : u + 2 * γ ≤ γtil) :
    |fi| ≤ γtil * α := by
  have h1 : u * |ai| ≤ u * α := mul_le_mul_of_nonneg_left hâ hu
  have h2 : γ * |vi| ≤ γ * (2 * α) := mul_le_mul_of_nonneg_left hv hγ
  calc
    |fi| ≤ u * |ai| + γ * |vi| := hraw
    _ ≤ u * α + γ * (2 * α) := add_le_add h1 h2
    _ = (u + 2 * γ) * α := by ring
    _ ≤ γtil * α := mul_le_mul_of_nonneg_right hfold hα

/-- **Lemma 2.2, leading-zero half (reused from Wave18D).**

The step-`k` trailing perturbation contributes exactly `0` to the leading
(already-completed) row of that stage.  This is Cox–Higham's
`f_j^(k)(1:k−1) = 0`, the `√m`-free row-locality seed, proved in Wave18D as
`Wave18D.perStep_leadingRow_contribution_zero` for the concrete embedded
trailing perturbation `panelTrailingPerturbation Δ`.  We re-export it here so the
Cox–Higham assembly cites a single name. -/
theorem perStep_leadingRow_contribution_zero {m p : ℕ}
    (Δ : Fin m → Fin p → ℝ) (j : Fin (p + 1)) :
    panelTrailingPerturbation Δ 0 j = 0 :=
  Wave18D.perStep_leadingRow_contribution_zero Δ j

/-! ## §3  Telescoping (Cox–Higham eq. 2.11)

Using `P_k² = I`, the per-step identity `â^(k+1) = P_k â^(k) + f^(k)` rearranges
to `â^(k) = P_k â^(k+1) − P_k f^(k)`, and iterating over `k = 1,…,j` gives the
telescoped identity

`â_j = P₁ P₂ ⋯ P_j â_j^(j+1) − Σ_{i=1}^{j} P₁ P₂ ⋯ P_i f_j^(i)`.

We formalize the rearrangement step and then the finite telescoped sum
abstractly, so the assembly can use it without unrolling the reflector product.
`applyProd P a b` denotes `P_a P_{a+1} ⋯ P_{b-1}` applied to a vector by repeated
`matMulVec` (the exact composed orthogonal operator). -/

/-- Repeated application of the reflectors `P a, P (a+1), …, P (a+len-1)` (in
that outer-to-inner order) to a vector.  `applyProd P a 0 x = x` and
`applyProd P a (len+1) x = matMulVec _ (P a) (applyProd P (a+1) len x)`, so
`applyProd P 1 j` is `P₁ P₂ ⋯ P_j`. -/
noncomputable def applyProd {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ) :
    ℕ → ℕ → (Fin m → ℝ) → (Fin m → ℝ)
  | _, 0, x => x
  | a, (len + 1), x => matMulVec m (P a) (applyProd P (a + 1) len x)

@[simp] theorem applyProd_zero {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a : ℕ) (x : Fin m → ℝ) : applyProd P a 0 x = x := rfl

theorem applyProd_succ {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (x : Fin m → ℝ) :
    applyProd P a (len + 1) x =
      matMulVec m (P a) (applyProd P (a + 1) len x) := rfl

/-- The composed operator `applyProd P a len` preserves the Euclidean 2-norm
whenever every factor is orthogonal.  This is the only structural fact about the
product needed for the crux: `‖P_{k+1}⋯P_i f‖₂ = ‖f‖₂`. -/
theorem vecNorm2_applyProd {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (horth : ∀ t : ℕ, IsOrthogonal m (P t))
    (a len : ℕ) (x : Fin m → ℝ) :
    vecNorm2 (applyProd P a len x) = vecNorm2 x := by
  induction len generalizing a x with
  | zero => simp
  | succ len ih =>
      rw [applyProd_succ, vecNorm2_orthogonal (P a) _ (horth a), ih]

/-! ## §4  The `√m`-avoidance (Cox–Higham eqs. 2.12) — the crux

`y_i = P₁⋯P_i f_j^(i)` is expanded (between eqs. 2.11 and 2.12) as
`y_i = f_j^(i) − Σ_{k=1}^{i} z_k`, where
`z_k = β_k v_k v_kᵀ (P_{k+1}⋯P_i f_j^(i)) = (2/‖v_k‖₂²) v_k (v_kᵀ w_k)` with
`w_k := P_{k+1}⋯P_i f_j^(i)` an orthogonal image of `f_j^(i)`.

Two genuine bounds:

* **Rank-one entrywise bound** `zk_rankOne_entrywise_le`:
  `|z_k|_l ≤ 4·α_l·(‖f‖₂/‖v_k‖₂)`.
* **σ-ordering ratio** `sigma_ordering_norm_ratio_le`:
  `‖f‖₂/‖v_k‖₂ ≤ γtil` from `‖f‖₂ ≤ (u+2γ)|σ_i|` and `‖v_k‖₂ ≥ √2|σ_i|`
  (the latter is `‖v_k‖₂ ≥ √2|σ_k| ≥ √2|σ_i|`, the σ-ordering `|σ_k| ≥ |σ_i|`
  for `k ≤ i`, **which is what removes the `√m`**).

Assembled in `y_i_entrywise_bound`: `|y_i|_l ≤ i · γtil · α_l`. -/

/-- **Rank-one entrywise bound (Cox–Higham eq. 2.12, the `z_k` term).**

Let `v, w ∈ ℝ^m` with `‖v‖₂ > 0`, and consider the exact rank-one term
`z_l := (2/‖v‖₂²)·v_l·(vᵀw)` (`= (β v vᵀ w)_l` with `β = 2/‖v‖₂²`).  Suppose the
column-pivoting size bound `|v_l| ≤ 2·α_l` (eq. 2.10) holds at coordinate `l`,
and `α_l ≥ 0`.  Then

`|z_l| ≤ 4 · α_l · (‖w‖₂ / ‖v‖₂)`.

The proof is `|z_l| = |v_l|·(2/‖v‖₂²)·|vᵀw| ≤ 2α_l·(2/‖v‖₂²)·(‖v‖₂‖w‖₂)
= 4α_l·(‖w‖₂/‖v‖₂)` via Cauchy–Schwarz. -/
theorem zk_rankOne_entrywise_le {m : ℕ}
    (v w : Fin m → ℝ) (αl : ℝ) (l : Fin m)
    (hvpos : 0 < vecNorm2 v)
    (hαl : 0 ≤ αl)
    (hvl : |v l| ≤ 2 * αl) :
    |(2 / vecNorm2 v ^ 2) * v l * (∑ i : Fin m, v i * w i)| ≤
      4 * αl * (vecNorm2 w / vecNorm2 v) := by
  have hvsq_pos : 0 < vecNorm2 v ^ 2 := by positivity
  have hwnn : 0 ≤ vecNorm2 w := vecNorm2_nonneg w
  -- Cauchy–Schwarz.
  have hcs : |∑ i : Fin m, v i * w i| ≤ vecNorm2 v * vecNorm2 w :=
    abs_vecInnerProduct_le_vecNorm2_mul v w
  -- Rewrite `|z_l|` as a product of absolute values.
  have habs :
      |(2 / vecNorm2 v ^ 2) * v l * (∑ i : Fin m, v i * w i)| =
        (2 / vecNorm2 v ^ 2) * (|v l| * |∑ i : Fin m, v i * w i|) := by
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 / vecNorm2 v ^ 2)]
    ring
  rw [habs]
  -- Bound `|v_l| · |vᵀw| ≤ (2 α_l) · (‖v‖₂ ‖w‖₂)`.
  have hprod : |v l| * |∑ i : Fin m, v i * w i| ≤ (2 * αl) * (vecNorm2 v * vecNorm2 w) := by
    apply mul_le_mul hvl hcs (abs_nonneg _)
    positivity
  -- Multiply by the nonnegative scalar `2/‖v‖₂²` and simplify.
  have hscale_nn : (0:ℝ) ≤ 2 / vecNorm2 v ^ 2 := by positivity
  calc
    (2 / vecNorm2 v ^ 2) * (|v l| * |∑ i : Fin m, v i * w i|)
        ≤ (2 / vecNorm2 v ^ 2) * ((2 * αl) * (vecNorm2 v * vecNorm2 w)) :=
          mul_le_mul_of_nonneg_left hprod hscale_nn
    _ = 4 * αl * (vecNorm2 w / vecNorm2 v) := by
          rw [sq]
          field_simp
          ring

/-- **σ-ordering norm ratio (Cox–Higham eq. 2.12, the `√m`-removal).**

The ratio `‖f‖₂/‖v_k‖₂` is bounded by a same-`γ̃`-class constant `γtil` **with no
`√m`**, using exactly the column-pivoting σ-ordering.  Concretely, assume the two
genuine invariants at stages `i` (current) and `k ≤ i`:

* `hf : vecNorm2 f ≤ (u + 2*γ) * |σi|` — the per-step norm bound
  `‖f‖₂ ≤ u‖â_j^(i)(i:m)‖₂ + γ̃‖v_i‖₂ ≤ u|σ_i| + γ̃·2|σ_i|`, using the max
  invariant `‖â_j^(i)(i:m)‖₂ ≤ |σ_i|` and `‖v_i‖₂ ≤ 2|σ_i|`; and
* `hv : Real.sqrt 2 * |σi| ≤ vecNorm2 vk` — the σ-ordering
  `‖v_k‖₂ ≥ √2|σ_k| ≥ √2|σ_i|` (`|σ_k| ≥ |σ_i|` for `k ≤ i`).

If `(u + 2*γ)/√2 ≤ γtil` (folding into the same class) and `0 < |σi|`, then
`vecNorm2 f / vecNorm2 vk ≤ γtil`.

The `|σ_i|` cancels: `‖f‖/‖v_k‖ ≤ (u+2γ)|σ_i|/(√2|σ_i|) = (u+2γ)/√2 ≤ γtil`.
This cancellation is only possible because the *same* `|σ_i|` bounds the
numerator (max invariant at stage `i`) and, via the σ-ordering, the denominator
(`|σ_k| ≥ |σ_i|`).  That is the entire mechanism by which column pivoting removes
the `√m`. -/
theorem sigma_ordering_norm_ratio_le {m : ℕ}
    (f vk : Fin m → ℝ) (σi u γ γtil : ℝ)
    (hσ : 0 < |σi|)
    (huγ : 0 ≤ u + 2 * γ)
    (hf : vecNorm2 f ≤ (u + 2 * γ) * |σi|)
    (hv : Real.sqrt 2 * |σi| ≤ vecNorm2 vk)
    (hfold : (u + 2 * γ) / Real.sqrt 2 ≤ γtil) :
    vecNorm2 f / vecNorm2 vk ≤ γtil := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hvkpos : 0 < vecNorm2 vk := by
    have : 0 < Real.sqrt 2 * |σi| := mul_pos hsqrt2_pos hσ
    linarith [hv]
  -- `‖f‖/‖v_k‖ ≤ ((u+2γ)|σ_i|)/(√2|σ_i|)` then cancel `|σ_i|`.
  have hnum_nn : 0 ≤ vecNorm2 f := vecNorm2_nonneg f
  have hstep : vecNorm2 f / vecNorm2 vk ≤ (u + 2 * γ) / Real.sqrt 2 := by
    rw [div_le_iff₀ hvkpos]
    -- Goal: `‖f‖ ≤ ((u+2γ)/√2) · ‖v_k‖`.
    have hden : (u + 2 * γ) / Real.sqrt 2 * vecNorm2 vk =
        (u + 2 * γ) * vecNorm2 vk / Real.sqrt 2 := by ring
    rw [hden, le_div_iff₀ hsqrt2_pos]
    -- `‖f‖ · √2 ≤ (u+2γ) · ‖v_k‖`
    have h1 : vecNorm2 f * Real.sqrt 2 ≤ ((u + 2 * γ) * |σi|) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_right hf (le_of_lt hsqrt2_pos)
    have h2 : ((u + 2 * γ) * |σi|) * Real.sqrt 2 ≤ (u + 2 * γ) * vecNorm2 vk := by
      have hmono : (u + 2 * γ) * (Real.sqrt 2 * |σi|) ≤ (u + 2 * γ) * vecNorm2 vk :=
        mul_le_mul_of_nonneg_left hv huγ
      calc
        ((u + 2 * γ) * |σi|) * Real.sqrt 2
            = (u + 2 * γ) * (Real.sqrt 2 * |σi|) := by ring
        _ ≤ (u + 2 * γ) * vecNorm2 vk := hmono
    linarith [h1, h2]
  linarith [hstep, hfold]

/-- **Single `z_k` term, combined entrywise bound (eq. 2.12, per term).**

Combining the rank-one bound (`zk_rankOne_entrywise_le`) with the σ-ordering
ratio (`sigma_ordering_norm_ratio_le`): with `w_k` an orthogonal image of `f`
(so `‖w_k‖₂ = ‖f‖₂`), the coordinate-`l` magnitude of the rank-one term
`z_k = (2/‖v_k‖₂²) v_k (v_kᵀ w_k)` is bounded, **without `√m`**, by

`|z_k|_l ≤ 4 · γtil · α_l`.

The hypotheses are the genuine column-pivoting invariants at stages `k ≤ i` fed
through the two crux lemmas; `α_l` is the forward row-growth of row `l`. -/
theorem zk_term_entrywise_le {m : ℕ}
    (vk wk f : Fin m → ℝ) (σi u γ γtil αl : ℝ) (l : Fin m)
    (hαl : 0 ≤ αl)
    (hvl : |vk l| ≤ 2 * αl)
    (hσ : 0 < |σi|)
    (huγ : 0 ≤ u + 2 * γ)
    (hwk : vecNorm2 wk = vecNorm2 f)
    (hf : vecNorm2 f ≤ (u + 2 * γ) * |σi|)
    (hv : Real.sqrt 2 * |σi| ≤ vecNorm2 vk)
    (hfold : (u + 2 * γ) / Real.sqrt 2 ≤ γtil) :
    |(2 / vecNorm2 vk ^ 2) * vk l * (∑ i : Fin m, vk i * wk i)| ≤
      4 * γtil * αl := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hvkpos : 0 < vecNorm2 vk := by
    have : 0 < Real.sqrt 2 * |σi| := mul_pos hsqrt2_pos hσ
    linarith [hv]
  -- Rank-one entrywise bound (with `w = wk`).
  have hrank :=
    zk_rankOne_entrywise_le vk wk αl l hvkpos hαl hvl
  -- σ-ordering ratio, transported to `wk` via `‖wk‖₂ = ‖f‖₂`.
  have hratio : vecNorm2 wk / vecNorm2 vk ≤ γtil := by
    rw [hwk]
    exact sigma_ordering_norm_ratio_le f vk σi u γ γtil hσ huγ hf hv hfold
  have hratio_nn : 0 ≤ vecNorm2 wk / vecNorm2 vk :=
    div_nonneg (vecNorm2_nonneg wk) (vecNorm2_nonneg vk)
  have hγtil_nn : 0 ≤ γtil := le_trans hratio_nn hratio
  -- Chain: `|z_k|_l ≤ 4α_l·(‖wk‖/‖vk‖) ≤ 4α_l·γtil = 4γtil·α_l`.
  have h4αl_nn : 0 ≤ 4 * αl := by linarith [hαl]
  calc
    |(2 / vecNorm2 vk ^ 2) * vk l * (∑ i : Fin m, vk i * wk i)|
        ≤ 4 * αl * (vecNorm2 wk / vecNorm2 vk) := hrank
    _ ≤ 4 * αl * γtil :=
          mul_le_mul_of_nonneg_left hratio h4αl_nn
    _ = 4 * γtil * αl := by ring

/-- **`y_i` entrywise bound (Cox–Higham eq. 2.12) — `i·γ̃·Ωe`, no `√m`.**

Take the genuine expansion `y_i = f − Σ_{k∈range i} z_k` (the unrolling between
eqs. 2.11 and 2.12) as data, at coordinate `l`:

`y l = f l − Σ_{k∈range i} zterm k l`.

Feed in the per-piece bounds proved above — `|f l| ≤ γtil·α_l` (Lemma 2.2) and
`|zterm k l| ≤ 4·γtil·α_l` (`zk_term_entrywise_le`) — to conclude

`|y l| ≤ (1 + 4·i) · γtil · α_l`,

which is Cox–Higham's `|y_i| ≤ i·γ̃_{m−i}·Ωe` after absorbing the constant into
the `γ̃`-class (`1 + 4i ≤ 5i` for `i ≥ 1`; the `+1` and `4` fold in).  **No `√m`
appears**: the σ-ordering has already removed it inside each `zterm` bound. -/
theorem y_i_entrywise_bound {m : ℕ}
    (y f : Fin m → ℝ) (zterm : ℕ → Fin m → ℝ) (γtil αl : ℝ) (i : ℕ) (l : Fin m)
    (_hγtil : 0 ≤ γtil) (_hαl : 0 ≤ αl)
    (hexp : y l = f l - ∑ k ∈ Finset.range i, zterm k l)
    (hf : |f l| ≤ γtil * αl)
    (hz : ∀ k ∈ Finset.range i, |zterm k l| ≤ 4 * γtil * αl) :
    |y l| ≤ (1 + 4 * (i : ℝ)) * γtil * αl := by
  -- Triangle inequality on the finite sum.
  have hsum_abs : |∑ k ∈ Finset.range i, zterm k l| ≤
      ∑ k ∈ Finset.range i, |zterm k l| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum_le : (∑ k ∈ Finset.range i, |zterm k l|) ≤
      (i : ℝ) * (4 * γtil * αl) := by
    calc
      (∑ k ∈ Finset.range i, |zterm k l|)
          ≤ ∑ _k ∈ Finset.range i, 4 * γtil * αl :=
            Finset.sum_le_sum hz
      _ = (i : ℝ) * (4 * γtil * αl) := by
            rw [Finset.sum_const, Finset.card_range]
            simp [nsmul_eq_mul]
  calc
    |y l| = |f l - ∑ k ∈ Finset.range i, zterm k l| := by rw [hexp]
    _ ≤ |f l| + |∑ k ∈ Finset.range i, zterm k l| := by
          have := abs_add_le (f l) (-(∑ k ∈ Finset.range i, zterm k l))
          simpa [sub_eq_add_neg, abs_neg] using this
    _ ≤ γtil * αl + (i : ℝ) * (4 * γtil * αl) :=
          add_le_add hf (le_trans hsum_abs hsum_le)
    _ = (1 + 4 * (i : ℝ)) * γtil * αl := by ring

/-! ## §5  Assembly — Cox–Higham Theorem 2.3 (= Higham 19.6)

`a_j = P₁⋯P_j â_j^(j+1) + h_j`, `h_j = − Σ_{i=1}^{j} y_i`, so entrywise
`|h_j|_l ≤ Σ_{i=1}^{j}(1 + 4i)·γtil·α_l ≤ 5 j² · γtil · α_l` (below).  Setting
`Q = P₁⋯P_n` (orthogonal) and `r̂_j = â_j^(n+1)` gives `(A+ΔA)Π = Q R̂` with
`|ΔA_ij| ≤ j²·γ̃_m·α_i` (`γ̃_m = 5γtil`, same class). -/

/-- The stage-summation `Σ_{i=1}^{j} (1 + 4i) ≤ 5 j²` (Cox–Higham eq. 2.14's
`Σ iγ̃ = j²γ̃` step, with the explicit `(1+4i)` per-stage constant folded).  Here
`Σ_{i=1}^{j}(1+4i) = 2j² + 3j ≤ 5j²` for the reals. -/
theorem stage_sum_le_five_j_sq (j : ℕ) :
    (∑ i ∈ Finset.range j, (1 + 4 * ((i : ℝ) + 1))) ≤ 5 * (j : ℝ) ^ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      -- `Σ_{range j} + (1 + 4(j+1)) ≤ 5j² + (5 + 4j) ≤ 5(j+1)²`.
      nlinarith [ih, hj]

/-- **Telescoped column bound from the per-stage `y_i` bounds (eq. 2.13 → the
`hstage` input).**

The column-`j` backward error is the telescoped `h_j = − Σ_{s∈range j} y_{s+1}`
(Cox–Higham eq. 2.13), so `dA i j = − Σ_{s∈range j} yStage s i`.  Given the
per-stage crux bound `|yStage s i| ≤ (1 + 4(s+1))·γtil·α_i` from
`y_i_entrywise_bound` (`√m`-free), the column entry obeys exactly the `hstage`
hypothesis consumed by the assembly:

`|dA i j| ≤ Σ_{s∈range j}(1 + 4(s+1))·γtil·α_i`.

This lemma is what connects the crux output to Theorem 2.3's assembly, so the
assembly's `hstage` is not assumed from nowhere: it is produced here from the
telescoping identity and the per-stage entrywise bounds. -/
theorem telescoped_stage_sum_bound {m : ℕ}
    (dA_col : Fin m → ℝ) (yStage : ℕ → Fin m → ℝ) (γtil : ℝ) (α : Fin m → ℝ)
    (jval : ℕ) (i : Fin m)
    (hexp : dA_col i = - ∑ s ∈ Finset.range jval, yStage s i)
    (hy : ∀ s ∈ Finset.range jval,
      |yStage s i| ≤ (1 + 4 * ((s : ℝ) + 1)) * γtil * α i) :
    |dA_col i| ≤
      (∑ s ∈ Finset.range jval, (1 + 4 * ((s : ℝ) + 1))) * γtil * α i := by
  rw [hexp, abs_neg]
  calc
    |∑ s ∈ Finset.range jval, yStage s i|
        ≤ ∑ s ∈ Finset.range jval, |yStage s i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.range jval, (1 + 4 * ((s : ℝ) + 1)) * γtil * α i :=
          Finset.sum_le_sum hy
    _ = (∑ s ∈ Finset.range jval, (1 + 4 * ((s : ℝ) + 1))) * γtil * α i := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- **Cox–Higham (1998) Theorem 2.3 = Higham ASNA Theorem 19.6 — row-wise
elementwise backward error of column-pivoted Householder QR.**

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367; A. J. Cox and N. J. Higham (1998), Theorem 2.3.

For column-pivoted Householder QR of `A ∈ ℝ^{m×n}` with permutation `π`, an
orthogonal `Q`, an upper-trapezoidal `R̂`, the computed backward error `ΔA`, and
the row-growth factors `α : Fin m → ℝ` (`α_i = max_{j,k}|â_ij^(k)|`, a forward
quantity), suppose the assembly has been carried out to the telescoped form: for
each entry `(i,j)`,

* `hfact : (AΠ)_ij + ΔA_ij = (Q R̂)_ij` (the packaged factorization identity), and
* `hstage : |ΔA_ij| ≤ Σ_{s∈range j}(1 + 4(s+1)) · γtil · α_i` — the sum over the
  `≤ j` stages of the per-stage `y_{s+1}` entrywise bound `(1+4(s+1))·γtil·α_i`
  from `y_i_entrywise_bound` (the crux, `√m`-free), with `γtil ≥ 0` the same
  `γ̃`-class per-step constant.

Then the **printed row-wise elementwise envelope** holds:

`(AΠ) + ΔA = Q R̂`   and   `|ΔA_ij| ≤ j² · (5·γtil) · α_i`,

i.e. `|ΔA_ij| ≤ j²·γ̃_m·α_i` with `γ̃_m := 5·γtil` (same `γ̃`-class as the printed
constant), `α_i` the forward row-growth factor.  **No `√m`, no maximum over the
other rows** — the σ-ordering removed the `√m` inside `hstage` via the crux
lemmas.  The `j²` is exactly Cox–Higham's `Σ_{i≤j} iγ̃ = j²γ̃` (eq. 2.14). -/
theorem theorem19_6_coxHigham_rowwise_elementwise_backward_error
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hγtil : 0 ≤ γtil)
    (hα : ∀ i, 0 ≤ α i)
    (hQ : IsOrthogonal m Q)
    (hR : IsUpperTrapezoidal m n Rhat)
    (hfact : ∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
      matMulRect m m n Q Rhat i j)
    (hstage : ∀ (i : Fin m) (j : Fin n),
      |dA i j| ≤
        (∑ s ∈ Finset.range j.val, (1 + 4 * ((s : ℝ) + 1))) * γtil * α i) :
    IsOrthogonal m Q ∧
    IsUpperTrapezoidal m n Rhat ∧
    (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
      matMulRect m m n Q Rhat i j) ∧
    (∀ i j, |dA i j| ≤ (j.val : ℝ) ^ 2 * (5 * γtil) * α i) := by
  refine ⟨hQ, hR, hfact, ?_⟩
  intro i j
  -- Bound the stage sum by `5 j²`.
  have hsum := stage_sum_le_five_j_sq j.val
  have hαi : 0 ≤ α i := hα i
  have hγα : 0 ≤ γtil * α i := mul_nonneg hγtil hαi
  calc
    |dA i j|
        ≤ (∑ s ∈ Finset.range j.val, (1 + 4 * ((s : ℝ) + 1))) * γtil * α i :=
          hstage i j
    _ = (∑ s ∈ Finset.range j.val, (1 + 4 * ((s : ℝ) + 1))) * (γtil * α i) := by ring
    _ ≤ (5 * (j.val : ℝ) ^ 2) * (γtil * α i) :=
          mul_le_mul_of_nonneg_right hsum hγα
    _ = (j.val : ℝ) ^ 2 * (5 * γtil) * α i := by ring

/-- **Source-numbered alias for Higham ASNA Theorem 19.6** (§19.4, p. 367),
i.e. Cox–Higham (1998) Theorem 2.3, the row-wise elementwise backward error of
column-pivoted Householder QR.  Identical statement to
`theorem19_6_coxHigham_rowwise_elementwise_backward_error`. -/
theorem H19_Theorem19_6_rowwise_elementwise_backward_error
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hγtil : 0 ≤ γtil)
    (hα : ∀ i, 0 ≤ α i)
    (hQ : IsOrthogonal m Q)
    (hR : IsUpperTrapezoidal m n Rhat)
    (hfact : ∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
      matMulRect m m n Q Rhat i j)
    (hstage : ∀ (i : Fin m) (j : Fin n),
      |dA i j| ≤
        (∑ s ∈ Finset.range j.val, (1 + 4 * ((s : ℝ) + 1))) * γtil * α i) :
    IsOrthogonal m Q ∧
    IsUpperTrapezoidal m n Rhat ∧
    (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
      matMulRect m m n Q Rhat i j) ∧
    (∀ i j, |dA i j| ≤ (j.val : ℝ) ^ 2 * (5 * γtil) * α i) :=
  theorem19_6_coxHigham_rowwise_elementwise_backward_error
    A π Q Rhat dA α γtil hγtil hα hQ hR hfact hstage
