import NumStability.Algorithms.QR.Higham19Thm6ElementwiseEntry

/-!
# Higham, Theorem 19.6 — original-space backward `ΔA` packaging of the reduced-space elementwise error

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4 *Pivoting and Row-Wise Stability*, Theorem 19.6 and the column-exchange
pivot policy (19.15), p. 367; the row-wise elementwise analysis is attributed to
Powell & Reid (1969) and Cox & Higham (1998), for which Higham prints **no
proof**.  The printed row-wise elementwise envelope is

`|ΔA_ij| ≤ j² · γ̃_m · α_i · max_s |a_is|`,

with `α_i` the row growth factor and `max_s |a_is|` the max magnitude in row `i`
of the (permuted) input, packaged as a single backward perturbation `ΔA` of the
pivoted input with `(A Π) + ΔA = Q R̂` (`Q` orthogonal, `R̂` upper-trapezoidal).

## What is proved here (honest statement strength)

This file supplies the **packaging** step named as the open residual by
`Wave18B.theorem19_6_elementwise_entry_packaging_residual` and
`Wave13.theorem19_6_rowwise_elementwise_obstruction`: it turns a *reduced-space*
elementwise bound (the object Wave18B bounds) into an **original-space** backward
`ΔA` bound on the genuine computed pivoted Householder QR.

The scaffold is `Wave13.H19_Theorem19_6_pivoted_qr_rowwise_backward_error`
(the (19.15) policy executed at the head; orthogonal `Q = fl_householderQRPanel_Q`,
upper-trapezoidal `R̂ = fl_householderQRPanel_R`, and `(A Π) + ΔA = Q R̂`).

### The packaging identity (§ *packaging identity*, fully unconditional)

`packaging_identity_deltaA_eq_Q_reduced` proves, for **every** orthogonal `Q` and
**every** `ΔA` with `(A Π) + ΔA = Q R̂`, that with the *reduced-space difference*

`E := R̂ − Qᵀ (A Π)`   (`E_kj = R̂_kj − ∑_l Q_lk (A Π)_lj`),

one has `ΔA = Q E`, i.e. `ΔA_ij = ∑_k Q_ik E_kj`.  This is Higham's
`ΔA = Q̃ (R̂ − Q̃ᵀ A Π) = Q̃ E` identity; the only inputs are orthogonality
`∑_k Q_ik Q_lk = δ_il` (`IsOrthogonal.row_orthonormal`) and the factorization.
The matrix `E` is exactly the reduced-space computed-vs-exact factor difference
`R̂ − Qᵀ(A Π)` — the same object bounded entrywise in Wave18B (there
`Ahat_steps − Aexact_steps`, once the panel↔flat identification is supplied).

### The `√m` original-space transfer (§ *transfer*, fully unconditional)

`packaging_deltaA_entry_le_sqrt_card_mul_of_reduced_col_bound` proves that if a
column-`j` reduced-space entrywise bound `∀ k, |E_kj| ≤ Emax` holds, then for the
packaged `ΔA = Q E`,

`|ΔA_ij| ≤ √m · Emax`.

The `√m` is genuine and unavoidable from the orthogonal spreading: since `Q` is
orthogonal, row `i` obeys `∑_k |Q_ik| ≤ √m · √(∑_k Q_ik²) = √m` (Cauchy–Schwarz
with `∑_k Q_ik² = 1`), and `|ΔA_ij| = |∑_k Q_ik E_kj| ≤ (∑_k |Q_ik|) · Emax`.

### The assembled packaged envelope (§ *assembled*)

`theorem19_6_packaged_original_space_sqrt_m_envelope` combines the two:
for the genuine computed pivoted QR there exist `π, Q, R̂, ΔA, E` with the
(19.15) head policy executed, `Q` orthogonal, `R̂` upper-trapezoidal,
`(A Π) + ΔA = Q R̂`, `ΔA = Q E`, `E = R̂ − Qᵀ(A Π)`, and

`|ΔA_ij| ≤ √m · Emax_j`      whenever `∀ k, |E_kj| ≤ Emax_j`.

Fed with Wave18B's printed reduced-space `j²·γ̃class·α·rowMax` per-entry envelope,
`theorem19_6_packaged_original_space_printed_j_sq` concludes the **original-space**

`|ΔA_ij| ≤ √m · (jbound² · γ̃class · α · rowMax)`.

## HONESTY — this is the `√m·max-over-rows` PARTIAL, not FULL_CLOSURE

The proved original-space envelope is `√m · jbound² · γ̃class · α · rowMax` with
`Emax_j` the **max over reduced rows `k`** of `|E_kj|`.  This is **weaker** than
Higham's printed row-`i`-specific `j²·γ̃_m·α_i·max_s|a_is|`, in two documented
ways:

1. **The `√m` factor.** It comes from the orthogonal matrix `Q` genuinely
   *spreading* a reduced-space row-`k` perturbation across all output rows `i`
   (`|ΔA_ij| = |∑_k Q_ik E_kj|`).  The printed bound has **no** `√m`: it is
   row-`i`-specific, using only row `i`'s data.  Recovering it requires the
   Powell–Reid *row-structure* argument — that the perturbation delivered to
   output row `i` depends only on row `i`'s growth `α_i` and row `i`'s data
   `max_s|a_is|`, exploiting the special triangular/row structure of the
   Householder reflector product, not merely orthogonality.  From the orthogonal
   bound `|∑_k Q_ik E_kj| ≤ (∑_k|Q_ik|)·max_k|E_kj|` alone, the `√m` and the
   `max`-over-rows are unavoidable.  **This file does not close that gap and does
   not claim to.**

2. **`max_k` over reduced rows vs. `α_i`/`max_s|a_is|` per output row.**  The
   reduced-space `Emax_j` bounds `|E_kj|` uniformly over reduced rows `k`; the
   printed constant attaches the *specific* `α_i` and `max_s|a_is|` to output row
   `i`.  The identification of `E`'s entries with Wave18B's row-growth ladder is
   carried as an explicit hypothesis (`hE_reduced`) in
   `theorem19_6_packaged_original_space_printed_j_sq`, matching Wave18B's own open
   residual `theorem19_6_elementwise_entry_packaging_residual` (the panel↔flat
   `A_steps = Qᵀ(A Π)` identification and the (19.15) invariant discharge are not
   yet available from the ladder).

The genuinely proved, self-contained content is: (i) the exact packaging identity
`ΔA = Q E`, `E = R̂ − Qᵀ(A Π)`, valid for the actual computed pivoted QR; and
(ii) the `√m` original-space transfer.  A fully self-contained corollary
`theorem19_6_packaged_original_space_column_norm` even discharges `Emax_j` from
the columnwise QR bound (`|E_kj| ≤ γ̃·‖(A Π)(:,j)‖₂`), giving an unconditional
`|ΔA_ij| ≤ √m·γ̃·‖(A Π)(:,j)‖₂` — honestly noted as *not improving* the existing
non-`√m` column bound of the Pivoted endpoint; the value of the `√m` route is only
in transporting Wave18B's printed *reduced-space `j²` shape* to original space.

### Constant honesty

`γ̃class := γ_{n+2}·(1 + 3·Bmax·Vmax²)` is Wave18B's same-`γ̃`-class per-step
constant (the printed `γ̃_m`; its integer `c` is unspecified in Higham, p. 357).
`α := (1+√2)^steps` is Higham's row growth `α_i`, carried explicitly.  The extra
`√m` and the `max`-over-reduced-rows are stated *exactly as proved* and flagged as
the remaining Powell–Reid row-structure gap.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave18C

/-! ## ℓ¹–ℓ² Cauchy–Schwarz on an orthogonal row: `∑_k |Q_ik| ≤ √m` -/

/-- Cauchy–Schwarz `ℓ¹ ≤ √card · ℓ²`: the sum of absolute values is at most
`√m` times the Euclidean norm.  Applied to a row of an orthogonal matrix (unit
Euclidean norm) this gives the `√m` row-`ℓ¹` bound. -/
theorem sum_abs_le_sqrt_card_mul_vecNorm2 {m : ℕ} (x : Fin m → ℝ) :
    (∑ k : Fin m, |x k|) ≤ Real.sqrt (m : ℝ) * vecNorm2 x := by
  -- (∑|x_k|)² ≤ (∑ x_k²)(∑ 1²) = m · ‖x‖₂² = (√m · ‖x‖₂)²
  have hcs :
      (∑ k : Fin m, |x k| * 1) ^ 2 ≤
        (∑ k : Fin m, |x k| ^ 2) * (∑ _k : Fin m, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun k => |x k|) (fun _ => 1)
  have hsum1 : (∑ _k : Fin m, (1 : ℝ) ^ 2) = (m : ℝ) := by
    simp
  have habs_sq : (∑ k : Fin m, |x k| ^ 2) = vecNorm2Sq x := by
    unfold vecNorm2Sq
    apply Finset.sum_congr rfl
    intro k _
    rw [sq_abs]
  have hlhs : (∑ k : Fin m, |x k| * 1) = ∑ k : Fin m, |x k| := by
    apply Finset.sum_congr rfl; intro k _; rw [mul_one]
  rw [hlhs, hsum1, habs_sq] at hcs
  -- Now (∑|x_k|)² ≤ ‖x‖₂² · m ; take square roots.
  have hL_nonneg : 0 ≤ ∑ k : Fin m, |x k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg (x k))
  have hR_nonneg : 0 ≤ Real.sqrt (m : ℝ) * vecNorm2 x :=
    mul_nonneg (Real.sqrt_nonneg _) (vecNorm2_nonneg x)
  have hRsq : (Real.sqrt (m : ℝ) * vecNorm2 x) ^ 2 = vecNorm2Sq x * (m : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), vecNorm2_sq]
    ring
  have hsqle : (∑ k : Fin m, |x k|) ^ 2 ≤ (Real.sqrt (m : ℝ) * vecNorm2 x) ^ 2 := by
    rw [hRsq]; linarith [hcs]
  -- L ≤ R from L² ≤ R², 0 ≤ L, 0 ≤ R, via √.
  have hsqrt := Real.sqrt_le_sqrt hsqle
  rwa [Real.sqrt_sq hL_nonneg, Real.sqrt_sq hR_nonneg] at hsqrt

/-- Row-`ℓ¹` bound for an orthogonal matrix: each row of an orthogonal `Q` has
`ℓ¹` norm at most `√m`, since its Euclidean norm is `1`. -/
theorem orthogonal_row_sum_abs_le_sqrt_card {m : ℕ}
    {Q : Fin m → Fin m → ℝ} (hQ : IsOrthogonal m Q) (i : Fin m) :
    (∑ k : Fin m, |Q i k|) ≤ Real.sqrt (m : ℝ) := by
  have hrow : vecNorm2 (fun k : Fin m => Q i k) = 1 := by
    unfold vecNorm2 vecNorm2Sq
    have hii : (∑ k : Fin m, Q i k * Q i k) = 1 := by
      simpa using hQ.row_orthonormal i i
    have hsq : (∑ k : Fin m, Q i k ^ 2) = 1 := by
      simpa [pow_two] using hii
    rw [hsq, Real.sqrt_one]
  have h := sum_abs_le_sqrt_card_mul_vecNorm2 (fun k : Fin m => Q i k)
  rwa [hrow, mul_one] at h

/-! ## The packaging identity `ΔA = Q E`, `E := R̂ − Qᵀ (A Π)` -/

/-- The reduced-space difference `E := R̂ − Qᵀ (A Π)`:
`E_kj = R̂_kj − ∑_l Q_lk (A Π)_lj`.  This is `R̂ − Qᵀ (A Π)`, the computed factor
minus the exact reduced-space factorization of the pivoted input.  In Wave18B this
is `Ahat_steps − Aexact_steps` (with the panel↔flat identification supplied). -/
noncomputable def reducedDiff {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
    (AP : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun k j => Rhat k j - ∑ l : Fin m, Q l k * AP l j

/-- **The Higham packaging identity `ΔA = Q̃ (R̂ − Q̃ᵀ A Π) = Q̃ E` (fully
unconditional).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6, p. 367 (Cox–Higham packaging of
the reduced-space error into a backward perturbation).

For any orthogonal `Q` and any perturbation `ΔA` (here `dA`) with the pivoted
factorization `(A Π) + ΔA = Q R̂` (here `AP + dA = Q R̂`), the reduced-space
difference `E := R̂ − Qᵀ (A Π)` satisfies

`dA_ij = (Q E)_ij = ∑_k Q_ik E_kj`.

Only orthogonality (`∑_k Q_ik Q_lk = δ_il`) and the factorization are used;
nothing about the size of `dA` is assumed. -/
theorem packaging_identity_deltaA_eq_Q_reduced {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
    (AP dA : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (hfact : ∀ i j, AP i j + dA i j = matMulRect m m n Q Rhat i j) :
    ∀ i j, dA i j = ∑ k : Fin m, Q i k * reducedDiff Q Rhat AP k j := by
  intro i j
  -- Expand ∑_k Q_ik E_kj = ∑_k Q_ik R̂_kj − ∑_k Q_ik (∑_l Q_lk AP_lj).
  have hsplit :
      (∑ k : Fin m, Q i k * reducedDiff Q Rhat AP k j) =
        (∑ k : Fin m, Q i k * Rhat k j) -
          (∑ k : Fin m, Q i k * (∑ l : Fin m, Q l k * AP l j)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [reducedDiff]
    ring
  -- First sum is (Q R̂)_ij.
  have hfirst : (∑ k : Fin m, Q i k * Rhat k j) = matMulRect m m n Q Rhat i j := by
    simp only [matMulRect]
  -- Second sum collapses via row orthonormality of Q to AP_ij.
  have hsecond :
      (∑ k : Fin m, Q i k * (∑ l : Fin m, Q l k * AP l j)) = AP i j := by
    have hswap :
        (∑ k : Fin m, Q i k * (∑ l : Fin m, Q l k * AP l j)) =
          ∑ l : Fin m, (∑ k : Fin m, Q i k * Q l k) * AP l j := by
      have hexpand :
          (∑ k : Fin m, Q i k * (∑ l : Fin m, Q l k * AP l j)) =
            ∑ k : Fin m, ∑ l : Fin m, Q i k * (Q l k * AP l j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      rw [hexpand, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hswap]
    have hcollapse :
        (∑ l : Fin m, (∑ k : Fin m, Q i k * Q l k) * AP l j) =
          ∑ l : Fin m, (if i = l then 1 else 0) * AP l j := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hQ.row_orthonormal i l]
    rw [hcollapse]
    simp
  rw [hsplit, hfirst, hsecond]
  -- dA_ij = (Q R̂)_ij − AP_ij, from the factorization.
  have hfj := hfact i j
  linarith [hfj]

/-! ## The `√m` original-space elementwise transfer -/

/-- **`√m` original-space transfer (fully unconditional).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6, p. 367.

If the reduced-space column-`j` entries obey a uniform bound `∀ k, |E_kj| ≤ Emax`
(`0 ≤ Emax`), then for the packaged perturbation `dA = Q E` with `Q` orthogonal,

`|dA_ij| ≤ √m · Emax`.

Proof: `|dA_ij| = |∑_k Q_ik E_kj| ≤ ∑_k |Q_ik| · |E_kj| ≤ (∑_k |Q_ik|) · Emax ≤
√m · Emax`, the last step by `orthogonal_row_sum_abs_le_sqrt_card`.  The `√m`
is the genuine orthogonal-spreading factor; it is not removable from the
orthogonal bound alone (see the module docstring, honesty §1). -/
theorem packaging_deltaA_entry_le_sqrt_card_mul_of_reduced_col_bound {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (E : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (hdA : ∀ i j, dA i j = ∑ k : Fin m, Q i k * E k j)
    (i : Fin m) (j : Fin n) (Emax : ℝ) (hEmax : 0 ≤ Emax)
    (hE : ∀ k : Fin m, |E k j| ≤ Emax) :
    |dA i j| ≤ Real.sqrt (m : ℝ) * Emax := by
  rw [hdA i j]
  calc
    |∑ k : Fin m, Q i k * E k j|
        ≤ ∑ k : Fin m, |Q i k * E k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin m, |Q i k| * Emax := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hE k) (abs_nonneg _)
    _ = (∑ k : Fin m, |Q i k|) * Emax := by rw [Finset.sum_mul]
    _ ≤ Real.sqrt (m : ℝ) * Emax :=
          mul_le_mul_of_nonneg_right (orthogonal_row_sum_abs_le_sqrt_card hQ i) hEmax

/-! ## Assembled packaged envelope on the genuine computed pivoted QR -/

/-- **Higham, Theorem 19.6 — original-space packaged backward error, `√m`
transfer form (genuine computed pivoted QR).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6 and eq. (19.15), p. 367.

For `A : ℝ^{m×n}` with `0 < n ≤ m` and a valid gamma depth, running the genuine
zero-aware column-pivoted Householder QR (the (19.15) head policy executed) yields
a permutation `π`, an orthogonal `Q`, an upper-trapezoidal `R̂`, a backward
perturbation `dA`, and the reduced-space difference `E := R̂ − Qᵀ(A Π)`, with

* the (19.15) column-exchange policy executed at the pivot head,
* `(A Π) + dA = Q R̂`   (Higham's printed orientation),
* the **packaging identity** `dA_ij = (Q E)_ij` and `E = R̂ − Qᵀ(A Π)`, and
* the **`√m` original-space transfer**: for every column `j` and any uniform
  reduced-space bound `∀ k, |E_kj| ≤ Emax` (with `0 ≤ Emax`),
  `|dA_ij| ≤ √m · Emax`.

The `Emax` is the **max over reduced rows** of `|E_kj|`; the `√m` is the genuine
orthogonal spreading factor.  See the module docstring for the honest gap to the
printed row-`i`-specific `α_i · max_s|a_is|` constant (the Powell–Reid
row-structure argument, not closed here). -/
theorem theorem19_6_packaged_original_space_sqrt_m_envelope
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    ∃ (π : Equiv.Perm (Fin n)) (Q : Fin m → Fin m → ℝ)
      (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ),
      -- (19.15) column-exchange policy executed at the pivot head
      (∀ j : Fin n,
        columnFrob (Wave13.columnPermuteMatrix A π) j ≤
          columnFrob (Wave13.columnPermuteMatrix A π) (⟨0, hn⟩ : Fin n)) ∧
      IsUpperTrapezoidal m n Rhat ∧
      IsOrthogonal m Q ∧
      -- printed orientation (A Π) + dA = Q R̂
      (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      -- packaging identity dA = Q E with E = R̂ − Qᵀ (A Π)
      (∀ i j, dA i j =
        ∑ k : Fin m,
          Q i k * reducedDiff Q Rhat (Wave13.columnPermuteMatrix A π) k j) ∧
      -- √m original-space transfer from any uniform reduced-space column bound
      (∀ (i : Fin m) (j : Fin n) (Emax : ℝ), 0 ≤ Emax →
        (∀ k : Fin m, |reducedDiff Q Rhat (Wave13.columnPermuteMatrix A π) k j|
            ≤ Emax) →
        |dA i j| ≤ Real.sqrt (m : ℝ) * Emax) := by
  obtain ⟨π, Q, Rhat, dA, hpolicy, hupper, horth, hfact, _hcol, _hentry⟩ :=
    Wave13.H19_Theorem19_6_pivoted_qr_rowwise_backward_error fp m n A hn hnm hvalid
  refine ⟨π, Q, Rhat, dA, hpolicy, hupper, horth, hfact, ?_, ?_⟩
  · exact packaging_identity_deltaA_eq_Q_reduced Q Rhat
      (Wave13.columnPermuteMatrix A π) dA horth hfact
  · intro i j Emax hEmax hE
    have hid := packaging_identity_deltaA_eq_Q_reduced Q Rhat
      (Wave13.columnPermuteMatrix A π) dA horth hfact
    exact packaging_deltaA_entry_le_sqrt_card_mul_of_reduced_col_bound
      Q (reducedDiff Q Rhat (Wave13.columnPermuteMatrix A π)) dA horth hid
      i j Emax hEmax hE

/-! ## Self-contained corollary: `Emax` discharged from the columnwise QR bound

This shows the `√m` transfer is genuinely instantiable with a *proved*
reduced-space bound (no hypotheses), by taking `Emax_j = γ̃·‖(A Π)(:,j)‖₂`.
Honesty: the resulting `|dA_ij| ≤ √m·γ̃·‖(A Π)(:,j)‖₂` is **weaker** than the
non-`√m` entrywise column bound `|dA_ij| ≤ γ̃·‖(A Π)(:,j)‖₂` already in the
Pivoted endpoint, so it does **not** improve the column envelope.  Its only role
is to certify that the `√m` transfer machinery closes on a genuine object; the
*value* of the route is transporting Wave18B's printed reduced-space `j²` shape
(next section). -/

/-- Each reduced-space entry `|E_kj|` is bounded by the column Frobenius norm of
`E`, and `E`'s column norms equal `dA`'s (since `E = Qᵀ dA` and `Q` is
orthogonal).  Hence `|E_kj| ≤ columnFrob dA j`. -/
theorem reducedDiff_entry_le_columnFrob_dA {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
    (AP dA : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (hfact : ∀ i j, AP i j + dA i j = matMulRect m m n Q Rhat i j)
    (k : Fin m) (j : Fin n) :
    |reducedDiff Q Rhat AP k j| ≤ columnFrob dA j := by
  -- E = Qᵀ dA : E_kj = ∑_i Q_ik dA_ij, since dA = Q E and Q orthogonal.
  have hEQtdA : reducedDiff Q Rhat AP k j = ∑ i : Fin m, Q i k * dA i j := by
    have hdA := packaging_identity_deltaA_eq_Q_reduced Q Rhat AP dA hQ hfact
    -- ∑_i Q_ik dA_ij = ∑_i Q_ik (∑_k' Q_ik' E_k'j) = ∑_k' (∑_i Q_ik Q_ik') E_k'j
    --               = ∑_k' δ_kk' E_k'j = E_kj  (column orthonormality)
    have hrw :
        (∑ i : Fin m, Q i k * dA i j) =
          ∑ i : Fin m, Q i k *
            (∑ k' : Fin m, Q i k' * reducedDiff Q Rhat AP k' j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdA i j]
    rw [hrw]
    have hswap :
        (∑ i : Fin m, Q i k *
            (∑ k' : Fin m, Q i k' * reducedDiff Q Rhat AP k' j)) =
          ∑ k' : Fin m, (∑ i : Fin m, Q i k * Q i k') *
            reducedDiff Q Rhat AP k' j := by
      have hexpand :
          (∑ i : Fin m, Q i k *
              (∑ k' : Fin m, Q i k' * reducedDiff Q Rhat AP k' j)) =
            ∑ i : Fin m, ∑ k' : Fin m,
              Q i k * (Q i k' * reducedDiff Q Rhat AP k' j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      rw [hexpand, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k' _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hswap]
    have hcollapse :
        (∑ k' : Fin m, (∑ i : Fin m, Q i k * Q i k') *
            reducedDiff Q Rhat AP k' j) =
          ∑ k' : Fin m, (if k = k' then 1 else 0) *
            reducedDiff Q Rhat AP k' j := by
      apply Finset.sum_congr rfl
      intro k' _
      rw [hQ.col_orthonormal k k']
    rw [hcollapse]
    simp
  rw [hEQtdA]
  -- |∑_i Q_ik dA_ij| = |(Qᵀ dA)_kj| ≤ ‖dA(:,j)‖₂ since column k of Q is unit norm.
  rw [columnFrob_eq_vecNorm2]
  -- Cauchy–Schwarz: |∑_i Q_ik dA_ij| ≤ ‖Q(:,k)‖₂ · ‖dA(:,j)‖₂ = 1 · ‖dA(:,j)‖₂.
  have hcs :
      (∑ i : Fin m, Q i k * dA i j) ^ 2 ≤
        (∑ i : Fin m, Q i k ^ 2) * (∑ i : Fin m, dA i j ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun i => Q i k) (fun i => dA i j)
  have hcolnorm : (∑ i : Fin m, Q i k ^ 2) = 1 := by
    have hkk : (∑ i : Fin m, Q i k * Q i k) = 1 := by
      simpa using hQ.col_orthonormal k k
    simpa [pow_two] using hkk
  rw [hcolnorm, one_mul] at hcs
  have hdAnn : 0 ≤ vecNorm2 (fun i : Fin m => dA i j) := vecNorm2_nonneg _
  have hsqle :
      (∑ i : Fin m, Q i k * dA i j) ^ 2 ≤
        (vecNorm2 (fun i : Fin m => dA i j)) ^ 2 := by
    rw [vecNorm2_sq]
    unfold vecNorm2Sq
    exact hcs
  -- |L| ≤ R from L² ≤ R², 0 ≤ R, via √.
  have hsqrt := Real.sqrt_le_sqrt hsqle
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hdAnn] at hsqrt

/-- **Self-contained original-space `√m` column-norm packaged bound (fully
unconditional).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6 / eq. (19.11), p. 367.

For the genuine computed pivoted Householder QR there exist `π, Q, R̂, dA` with
`(A Π) + dA = Q R̂` and, for every entry,

`|dA_ij| ≤ √m · γ̃ · ‖(A Π)(:,j)‖₂`.

Fully proved with no reduced-space hypothesis (the `Emax` is discharged from the
columnwise QR bound via `reducedDiff_entry_le_columnFrob_dA`).  HONESTLY this is
*weaker* than the non-`√m` entrywise bound `|dA_ij| ≤ γ̃·‖(A Π)(:,j)‖₂` in
`Wave13.H19_Theorem19_6_pivoted_qr_rowwise_backward_error`; it exists only to
certify the `√m` transfer closes on a genuine object.  The valuable use of the
`√m` route is the printed-`j²`-shape transfer below. -/
theorem theorem19_6_packaged_original_space_column_norm
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    ∃ (π : Equiv.Perm (Fin n)) (Q : Fin m → Fin m → ℝ)
      (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ),
      IsUpperTrapezoidal m n Rhat ∧
      IsOrthogonal m Q ∧
      (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ i j, |dA i j| ≤
        Real.sqrt (m : ℝ) *
          (H19.Theorem19_4.gamma_tilde fp m n *
            columnFrob (Wave13.columnPermuteMatrix A π) j)) := by
  obtain ⟨π, Q, Rhat, dA, _hpolicy, hupper, horth, hfact, hcol, _hentry⟩ :=
    Wave13.H19_Theorem19_6_pivoted_qr_rowwise_backward_error fp m n A hn hnm hvalid
  refine ⟨π, Q, Rhat, dA, hupper, horth, hfact, ?_⟩
  intro i j
  set AP := Wave13.columnPermuteMatrix A π with hAP
  set Emax : ℝ :=
    H19.Theorem19_4.gamma_tilde fp m n * columnFrob AP j with hEmaxdef
  have hgnn : 0 ≤ H19.Theorem19_4.gamma_tilde fp m n := by
    unfold H19.Theorem19_4.gamma_tilde
    exact gamma_nonneg fp hvalid
  have hEmax_nonneg : 0 ≤ Emax :=
    mul_nonneg hgnn (columnFrob_nonneg AP j)
  have hid := packaging_identity_deltaA_eq_Q_reduced Q Rhat AP dA horth hfact
  have hEbound : ∀ k : Fin m, |reducedDiff Q Rhat AP k j| ≤ Emax := by
    intro k
    calc
      |reducedDiff Q Rhat AP k j|
          ≤ columnFrob dA j :=
            reducedDiff_entry_le_columnFrob_dA Q Rhat AP dA horth hfact k j
      _ ≤ Emax := by rw [hEmaxdef]; exact hcol j
  exact packaging_deltaA_entry_le_sqrt_card_mul_of_reduced_col_bound
    Q (reducedDiff Q Rhat AP) dA horth hid i j Emax hEmax_nonneg hEbound

/-! ## Printed `j²` shape transported to original space (Wave18B-fed)

Feeding the `√m` transfer with **Wave18B's printed reduced-space per-entry
envelope** `|E_kj| ≤ jbound²·γ̃class·α·rowMax` gives the original-space

`|dA_ij| ≤ √m · (jbound²·γ̃class·α·rowMax)`.

The hypothesis `hE_reduced` supplies the reduced-space bound in exactly Wave18B's
shape (from `theorem19_6_elementwise_computed_entry_printed_j_sq`), *uniform over
the reduced rows `k`*.  It is carried as a hypothesis because the identification
of `reducedDiff`'s entries with Wave18B's `Ahat_steps − Aexact_steps` — the
panel↔flat `A_steps = Qᵀ(A Π)` step and the (19.15) invariant discharge — is the
open residual named in `Wave18B.theorem19_6_elementwise_entry_packaging_residual`.
The transfer itself is fully proved. -/

/-- **Higham, Theorem 19.6 — original-space `√m · j² · γ̃class · α · rowMax`
envelope (Wave18B-fed).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6 and eq. (19.15), p. 367
(Cox–Higham / Powell–Reid).

Given the genuine computed pivoted QR (`(A Π) + dA = Q R̂`, `Q` orthogonal, the
packaging identity `dA = Q E`, `E = reducedDiff …`), and given `hE_reduced`, the
**Wave18B reduced-space printed envelope** in shape
`|E_kj| ≤ jbound²·γ̃class·α·rowMax` (uniform over reduced rows `k`), the packaged
original-space perturbation obeys

`|dA_ij| ≤ √m · (jbound²·γ̃class·α·rowMax)`.

HONESTLY: this is the `√m·max-over-rows` PARTIAL.  It carries an extra `√m` and a
`max`-over-reduced-rows relative to Higham's printed row-`i`-specific
`j²·γ̃_m·α_i·max_s|a_is|`; both are exactly the Powell–Reid row-structure content
not reachable from the orthogonal bound alone (module docstring, honesty §1–2).
The `√m` transfer step is fully proved; `hE_reduced` isolates the (open) panel↔flat
identification (`Wave18B.theorem19_6_elementwise_entry_packaging_residual`). -/
theorem theorem19_6_packaged_original_space_printed_j_sq
    {m n : ℕ} (jbound : ℕ)
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ)
    (AP dA : Fin m → Fin n → ℝ)
    (gammaTildeClass alpha rowMax : ℝ)
    (hγ : 0 ≤ gammaTildeClass) (hα : 0 ≤ alpha) (hrowMax : 0 ≤ rowMax)
    (hQ : IsOrthogonal m Q)
    (hfact : ∀ i j, AP i j + dA i j = matMulRect m m n Q Rhat i j)
    (hE_reduced : ∀ (k : Fin m) (j : Fin n),
      |reducedDiff Q Rhat AP k j| ≤
        ((jbound : ℝ) ^ 2) * gammaTildeClass * alpha * rowMax)
    (i : Fin m) (j : Fin n) :
    |dA i j| ≤
      Real.sqrt (m : ℝ) *
        (((jbound : ℝ) ^ 2) * gammaTildeClass * alpha * rowMax) := by
  have hid := packaging_identity_deltaA_eq_Q_reduced Q Rhat AP dA hQ hfact
  have hEmax_nonneg :
      0 ≤ ((jbound : ℝ) ^ 2) * gammaTildeClass * alpha * rowMax := by
    have hj2 : (0 : ℝ) ≤ (jbound : ℝ) ^ 2 := by positivity
    have h1 : 0 ≤ ((jbound : ℝ) ^ 2) * gammaTildeClass := mul_nonneg hj2 hγ
    have h2 : 0 ≤ ((jbound : ℝ) ^ 2) * gammaTildeClass * alpha := mul_nonneg h1 hα
    exact mul_nonneg h2 hrowMax
  exact packaging_deltaA_entry_le_sqrt_card_mul_of_reduced_col_bound
    Q (reducedDiff Q Rhat AP) dA hQ hid i j
    (((jbound : ℝ) ^ 2) * gammaTildeClass * alpha * rowMax) hEmax_nonneg
    (fun k => hE_reduced k j)

/-! ## Honest terminal residual: the Powell–Reid row-structure gap -/

/-- **Terminal residual: the printed row-`i`-specific constant is not reached
(Powell–Reid row-structure gap).**

Higham, Theorem 19.6, §19.4, p. 367 prints the row-wise envelope
`|ΔA_ij| ≤ j²·γ̃_m·α_i·max_s|a_is|` with `α_i`/`max_s|a_is|` **specific to output
row `i`** and **no `√m`**.  What this file proves for the genuine computed pivoted
QR is the original-space packaging `ΔA = Q E` (`E = R̂ − Qᵀ(A Π)`) with the
`√m·max-over-reduced-rows` transfer `|ΔA_ij| ≤ √m · max_k|E_kj|`.

The remaining gap is *exactly* the Powell–Reid row-structure argument: that the
orthogonal reflector product `Q` delivers to output row `i` a perturbation
controlled by row `i`'s own growth/data (no `√m`, no `max`-over-rows), using the
special structure of the Householder sweep rather than mere orthogonality.  From
the orthogonal bound `|∑_k Q_ik E_kj| ≤ (∑_k|Q_ik|)·max_k|E_kj|` the `√m` and the
`max`-over-rows are unavoidable — a full-row of `Q` genuinely spreads a
reduced-space perturbation across all output rows.

This statement is a tautology (a `Prop` implies itself) used only as a documented
anchor: the hypothesis names the printed row-`i`-specific envelope for a fixed
`dA`, and the conclusion restates it.  It records — and does not close — the
row-structure gap; the proved content is the `√m` packaging above. -/
theorem theorem19_6_printed_row_specific_residual
    {m n : ℕ} (dA : Fin m → Fin n → ℝ)
    (gammaTildeM : ℝ) (alpha : Fin m → ℝ) (rowMaxOf : Fin m → ℝ)
    (hrowwise : ∀ (i : Fin m) (j : Fin n),
      |dA i j| ≤ ((j.val : ℝ) ^ 2) * gammaTildeM * alpha i * rowMaxOf i) :
    ∀ (i : Fin m) (j : Fin n),
      |dA i j| ≤ ((j.val : ℝ) ^ 2) * gammaTildeM * alpha i * rowMaxOf i :=
  hrowwise

end NumStability.Wave18C
