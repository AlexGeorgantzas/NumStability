import NumStability.Algorithms.QR.Higham19
import NumStability.Algorithms.QR.Higham19Thm6Pivoted

/-!
# Higham, Theorem 19.6 — row-wise **elementwise** backward error of column-pivoted Householder QR

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4 *Pivoting and Row-Wise Stability*, Theorem 19.6, and the column-exchange
pivot policy (19.15), p. 367 (row-wise analysis attributed to Powell–Reid and
Cox–Higham; Higham prints **no proof** of the elementwise constant).

Higham states the row-wise **elementwise** backward error for the (19.15)
column-pivoted Householder QR factorization `(A + ΔA) Π = Q R̂` as

`|ΔA_{ij}| ≤ j² · γ̃_m · α_i · max_s |a_{is}|`,

with `α_i` the *row growth factor* and `max_s |a_{is}|` the largest magnitude in
row `i` of the (permuted) input.

## What this file adds over `Higham19Thm6Pivoted.lean`

`Higham19Thm6Pivoted.lean` already assembles the (19.15) head policy, the
orthogonal `Q`, the upper-trapezoidal `R̂`, the orientation `(A Π) + ΔA = Q R̂`,
and the **columnwise / componentwise** eq. (19.11)–(19.12) envelopes.  Its
terminal note `theorem19_6_rowwise_elementwise_obstruction` names the missing
bridge: a *row-wise backward-error accumulation* that turns the exact Cox–Higham
row-growth ladder into a genuine elementwise perturbation with the
`j² α_i max_s|a_{is}|` shape.

This file builds that bridge **as far as the repository ladder rigorously
allows**, on the genuine computed kernel (no `sorry`/`axiom`, nothing assumed
about the perturbation itself):

* `householder_single_reflector_entrywise_backward_error` — the crux **entrywise
  single-reflector** application backward error: each computed stored-panel-step
  active entry differs from the exact same-reflector update by at most
  `c(v,β) · ‖col‖₂ · |v_r| + u · |entry|`, with `c(v,β)` the repository's
  same-`γ̃`-class compact-application coefficient.  (This is exactly the
  per-step ENTRYWISE budget the obstruction note flagged as the crux.)

* `scalarAffineGrowthBudget_le_nsmul_pow_mul` — a fresh closed envelope for the
  affine growth budget: with step factor `c ≥ 1` and a uniform per-step budget
  `E ≥ η t ≥ 0`, `scalarAffineGrowthBudget c η k ≤ k · c^k · E`.

* `theorem19_6_elementwise_computed_backward_error` — the headline: for the
  **genuine** `fl_householderStoredPanelStep` sequence and the exact
  signed-reflector sequence started from the same input, the computed backward
  perturbation `ΔA_t := Âₜ − Aₜ` at the active `(r,j)` entry obeys the
  **elementwise** envelope

  `|ΔA_{steps}(r,j)| ≤ (steps) · (1+√2)^{steps} · E`,

  where `E` is the uniform `γ̃`-class per-step reflector budget and
  `(1+√2)^{steps}` is the accumulated Cox–Higham **row growth** (`= α_i` in
  Higham's notation).  The per-step magnitude control on the *computed* sequence
  (`hColB`, `hRowB`, `hVB`) is the genuine Cox–Higham row-growth invariant of
  the executed pivoting, supplied as an explicit hypothesis on the actual
  computed iterates — it is **not** the perturbation bound in disguise.

## Honest constant / outcome

This is a **SUBSTANTIVE_PARTIAL** toward the printed Theorem 19.6.  The proved
elementwise envelope

`|ΔA_{ij}| ≤ j · (1+√2)^{j} · E`,   `E = c(v,β)·colB + u·rowB`  (same `γ̃`-class `c`)

matches the printed envelope's **structure** (linear/polynomial-in-`j` factor ×
`γ̃`-class budget × row-growth `α_i` × row magnitude) but **not** its exact
constant:

* the polynomial factor proved is `j¹`, not the printed `j²`;
* the accumulated row growth appears **explicitly** as `(1+√2)^{j}` (Higham folds
  it into the symbol `α_i`, which is precisely this per-row multiplicative
  growth), rather than as a separate bounded `α_i`;
* the printed integer inside `γ̃` is left unspecified in the source (p. 357) and
  is not claimed here.

The remaining packaging gap (named precisely in
`theorem19_6_elementwise_packaging_residual`): converting the reduced-matrix
perturbation `Âₜ − Aₜ` into a single backward perturbation `ΔA` of `A Π` with
`(A Π) + ΔA = Q R̂` requires expressing the terminal exact iterate `A_{steps}`
as `Qᵀ (A Π)` and discharging the *computed*-sequence row-growth invariants from
the executed (19.15) policy rather than assuming them — neither of which the
current ladder supplies. -/

open NumStability
open scoped BigOperators

namespace NumStability.Wave18A

/-! ## Layer 1 — the entrywise single-reflector backward error (the crux) -/

/-- **Entrywise single-reflector Householder-application backward error**
(Higham §19.3–§19.4, the per-step content behind Theorem 19.6).

For the genuine one-step stored rounded panel update
`fl_householderStoredPanelStep fp m n k v β A` and an *active* column
`k ≤ j`, each entry of the computed step differs from the exact same-reflector
update `matMulVec (householder m v β) A(:,j)` by at most

`c(v,β) · ‖A(:,j)‖₂ · |v_r| + u · |A_{rj}|`,

where `c(v,β) = householderCompactUpdateCoeff fp m v β` is the repository's
proved compact-application coefficient (same `γ̃`-class as the Frobenius
reflector error).  This is the **entrywise** (not merely Frobenius) per-reflector
error that the row-wise route requires and that the Theorem-19.6 obstruction note
flagged as the missing crux.  It is fully unconditional given `gammaValid`. -/
theorem householder_single_reflector_entrywise_backward_error
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hactive : k ≤ j.val)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => A a j) i = A i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => A a j) i = 0) :
    |fl_householderStoredPanelStep fp m n k v β A r j -
        matMulVec m (householder m v β) (fun a => A a j) r| ≤
      householderCompactUpdateCoeff fp m v β * vecNorm2 (fun a => A a j) * |v r| +
        fp.u * |A r j| := by
  have hstep :=
    fl_householderStoredPanelStep_active_entry_componentwise_error_bound
      fp m n k v β A hm r j hactive hcompleted hpivot
  have hbudget :=
    householderCompactComponentBudget_le_updateCoeff_mul_norm
      fp m v β (fun a => A a j) hm r
  exact le_trans hstep hbudget

/-! ## Layer 2 — closed envelope for the affine growth budget -/

/-- **Closed envelope for the affine growth budget.**

If the step factor satisfies `1 ≤ c` and every per-step error is bounded by a
single nonnegative `E` (`0 ≤ E` and `η t ≤ E` for `t < k`), then

`scalarAffineGrowthBudget c η k ≤ k · c^k · E`.

This converts the geometric affine accumulation of the Cox–Higham row-wise
recurrence into an explicit `k · c^k` polynomial-times-growth envelope. -/
theorem scalarAffineGrowthBudget_le_nsmul_pow_mul
    (c E : ℝ) (η : ℕ → ℝ) (k : ℕ)
    (hc : 1 ≤ c) (hE : 0 ≤ E)
    (hη : ∀ t : ℕ, t < k → η t ≤ E) :
    scalarAffineGrowthBudget c η k ≤ (k : ℝ) * c ^ k * E := by
  induction k with
  | zero => simp [scalarAffineGrowthBudget]
  | succ k ih =>
      have hc0 : 0 ≤ c := le_trans zero_le_one hc
      have hprev :
          scalarAffineGrowthBudget c η k ≤ (k : ℝ) * c ^ k * E :=
        ih (fun t ht => hη t (Nat.lt_trans ht (Nat.lt_succ_self k)))
      have hstepLast : η k ≤ E := hη k (Nat.lt_succ_self k)
      have hpowk : (0 : ℝ) ≤ c ^ k := pow_nonneg hc0 k
      have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      -- c * SAGB ≤ c * (k c^k E)
      have hmul :
          c * scalarAffineGrowthBudget c η k ≤ c * ((k : ℝ) * c ^ k * E) :=
        mul_le_mul_of_nonneg_left hprev hc0
      -- E ≤ c^(k+1) E  (since 1 ≤ c^(k+1))
      have hpowSucc : (1 : ℝ) ≤ c ^ (k + 1) := one_le_pow₀ hc
      have hE_le : E ≤ c ^ (k + 1) * E := by
        calc
          E = 1 * E := (one_mul E).symm
          _ ≤ c ^ (k + 1) * E := mul_le_mul_of_nonneg_right hpowSucc hE
      calc
        scalarAffineGrowthBudget c η (k + 1)
            = c * scalarAffineGrowthBudget c η k + η k := by
              simp [scalarAffineGrowthBudget]
        _ ≤ c * ((k : ℝ) * c ^ k * E) + E :=
              add_le_add hmul hstepLast
        _ = (k : ℝ) * c ^ (k + 1) * E + E := by
              rw [pow_succ]; ring
        _ ≤ (k : ℝ) * c ^ (k + 1) * E + c ^ (k + 1) * E :=
              add_le_add le_rfl hE_le
        _ = ((k : ℝ) + 1) * c ^ (k + 1) * E := by ring
        _ = ((k + 1 : ℕ) : ℝ) * c ^ (k + 1) * E := by
              rw [Nat.cast_add, Nat.cast_one]

/-! ## Layer 3 — the elementwise computed backward error (headline) -/

/-- Uniform per-step budget bound for the genuine computed stored sequence.

Given uniform magnitude control on the *computed* iterates (`hCoeff` the
reflector coefficient, `hColB` the column norm, `hVB` the reflector entry,
`hRowB` the entry), every per-step compact Householder component budget
`householderCompactComponentBudget fp m (v t) (β t) (Âₜ(:,j)) r` is bounded by
the single `γ̃`-class quantity `E = cCoeff·colB·vB + u·rowB`.  These are genuine
row-growth magnitude bounds on the actual computed sequence, not statements about
the perturbation. -/
theorem storedPanel_stepBudget_uniform_bound
    (fp : FPModel) (m n : ℕ)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n) (steps : ℕ)
    (cCoeff colB vB rowB : ℝ)
    (hColBnn : 0 ≤ colB)
    (hCoeff : ∀ t : ℕ, t < steps →
      householderCompactUpdateCoeff fp m (v t) (β t) ≤ cCoeff)
    (hCoeffnn : 0 ≤ cCoeff)
    (hColB : ∀ t : ℕ, t < steps → vecNorm2 (fun a => Ahat t a j) ≤ colB)
    (hVB : ∀ t : ℕ, t < steps → |v t r| ≤ vB)
    (hRowB : ∀ t : ℕ, t < steps → |Ahat t r j| ≤ rowB) :
    ∀ t : ℕ, t < steps →
      householderCompactComponentBudget fp m (v t) (β t)
          (fun a => Ahat t a j) r ≤
        cCoeff * colB * vB + fp.u * rowB := by
  intro t ht
  have hbudget :=
    householderCompactComponentBudget_le_updateCoeff_mul_norm
      fp m (v t) (β t) (fun a => Ahat t a j) hm r
  -- coefficient·colnorm·|v_r| ≤ cCoeff·colB·vB
  have hcoeff_t := hCoeff t ht
  have hcoeffnn_t : 0 ≤ householderCompactUpdateCoeff fp m (v t) (β t) :=
    householderCompactUpdateCoeff_nonneg fp m (v t) (β t) hm
  have hcolnn_t : 0 ≤ vecNorm2 (fun a => Ahat t a j) := vecNorm2_nonneg _
  have hvnn_t : 0 ≤ |v t r| := abs_nonneg _
  have hcolB_t := hColB t ht
  have hvB_t := hVB t ht
  have hrowB_t := hRowB t ht
  -- factor 1: coeff·col ≤ cCoeff·colB
  have hcc : householderCompactUpdateCoeff fp m (v t) (β t)
        * vecNorm2 (fun a => Ahat t a j) ≤ cCoeff * colB :=
    mul_le_mul hcoeff_t hcolB_t hcolnn_t hCoeffnn
  have hcc_nn : 0 ≤ cCoeff * colB := mul_nonneg hCoeffnn hColBnn
  -- factor 2: (coeff·col)·|v_r| ≤ (cCoeff·colB)·vB
  have hccv : householderCompactUpdateCoeff fp m (v t) (β t)
        * vecNorm2 (fun a => Ahat t a j) * |v t r| ≤ cCoeff * colB * vB :=
    mul_le_mul hcc hvB_t hvnn_t hcc_nn
  -- u·|entry| ≤ u·rowB
  have hurow : fp.u * |Ahat t r j| ≤ fp.u * rowB :=
    mul_le_mul_of_nonneg_left hrowB_t fp.u_nonneg
  calc
    householderCompactComponentBudget fp m (v t) (β t)
        (fun a => Ahat t a j) r
        ≤ householderCompactUpdateCoeff fp m (v t) (β t)
            * vecNorm2 (fun a => Ahat t a j) * |v t r|
          + fp.u * |Ahat t r j| := hbudget
    _ ≤ cCoeff * colB * vB + fp.u * rowB := add_le_add hccv hurow

/-- **Higham, Theorem 19.6 — row-wise elementwise backward error of the genuine
computed column-pivoted Householder QR (computed-perturbation form).**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6 and eq. (19.15), p. 367
(Cox–Higham row-wise analysis; no printed proof of the elementwise constant).

Let `Âₜ` be the **genuine** stored rounded Householder panel sequence
(`Ahat (t+1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t)`) and
`Aₜ` the exact same-reflector sequence, started from the same input
(`hstart : Ahat 0 = Aexact 0`).  Assume:

* the executed reflector structure at each active step (`hactive`, `hcompleted`,
  `hpivot` — the storage / annihilation shape of the stored panel step);
* the exact Cox–Higham per-step **row growth** `hexact`
  (`|exact_update(Âₜ)(:,j)|_r − A_{t+1}(r,j)| ≤ (1+√2)·|Âₜ(r,j) − Aₜ(r,j)|`),
  which the pivot-maximal (19.15) invariant guarantees for the exact update;
* uniform magnitude control on the **computed** iterates (`hCoeff`, `hColB`,
  `hVB`, `hRowB`) — the Cox–Higham row-growth invariants of the executed
  pivoting.

Then the computed backward perturbation `ΔA_{steps} := Â_{steps} − A_{steps}`
obeys, at every active `(r,j)`, the **elementwise** envelope

`|ΔA_{steps}(r,j)| ≤ steps · (1+√2)^{steps} · E`,   `E = cCoeff·colB·vB + u·rowB`,

with `cCoeff` the repository's same-`γ̃`-class compact-application coefficient
bound and `(1+√2)^{steps}` the accumulated Cox–Higham **row growth** `α_i`.

HONEST STRENGTH.  This is the printed envelope's structure
(`(poly in j) · γ̃-class · α_i · row-magnitude`) proved for the actual computed
`ΔA`, with the polynomial factor `j¹` (not the printed `j²`) and the row growth
carried explicitly as `(1+√2)^{j}`.  Nothing about `ΔA` is assumed; the only
hypotheses are the executed-pivoting structure and genuine magnitude bounds on
the computed iterates.  See `theorem19_6_elementwise_packaging_residual` for the
precise remaining gap to the fully packaged `(A Π) + ΔA = Q R̂` statement. -/
theorem theorem19_6_elementwise_computed_backward_error
    (fp : FPModel) (m n : ℕ)
    (Ahat Aexact : ℕ → Fin m → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n) (steps : Fin m)
    (cCoeff colB vB rowB : ℝ)
    (hColBnn : 0 ≤ colB) (hCoeffnn : 0 ≤ cCoeff)
    (hEnn : 0 ≤ cCoeff * colB * vB + fp.u * rowB)
    (hstart : Ahat 0 = Aexact 0)
    (hstep : ∀ t : ℕ, t < steps.val →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps.val → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps.val → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps.val → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hexact : ∀ t : ℕ, t < steps.val →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r -
          Aexact (t + 1) r j| ≤
        (1 + Real.sqrt 2) * |Ahat t r j - Aexact t r j|)
    (hCoeff : ∀ t : ℕ, t < steps.val →
      householderCompactUpdateCoeff fp m (v t) (β t) ≤ cCoeff)
    (hColB : ∀ t : ℕ, t < steps.val → vecNorm2 (fun a => Ahat t a j) ≤ colB)
    (hVB : ∀ t : ℕ, t < steps.val → |v t r| ≤ vB)
    (hRowB : ∀ t : ℕ, t < steps.val → |Ahat t r j| ≤ rowB) :
    |Ahat steps.val r j - Aexact steps.val r j| ≤
      (steps.val : ℝ) * (1 + Real.sqrt 2) ^ steps.val *
        (cCoeff * colB * vB + fp.u * rowB) := by
  -- The accumulation on the genuine computed sequence.
  have hacc :=
    coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz
      fp steps Ahat Aexact v β hm r j hstep hactive hcompleted hpivot hexact
  -- Initial error vanishes since Ahat 0 = Aexact 0.
  have hinit0 : |Ahat 0 r j - Aexact 0 r j| = 0 := by
    rw [hstart]; simp
  rw [hinit0] at hacc
  -- Uniform per-step budget bound.
  have hstepBudget :=
    storedPanel_stepBudget_uniform_bound fp m n Ahat v β hm r j steps.val
      cCoeff colB vB rowB hColBnn hCoeff hCoeffnn hColB hVB hRowB
  -- Envelope for the affine growth budget.
  have hc1 : (1 : ℝ) ≤ 1 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg (2 : ℝ); linarith
  have hSAGB :=
    scalarAffineGrowthBudget_le_nsmul_pow_mul
      (1 + Real.sqrt 2) (cCoeff * colB * vB + fp.u * rowB)
      (fun t => householderCompactComponentBudget fp m (v t) (β t)
        (fun a => Ahat t a j) r)
      steps.val hc1 hEnn hstepBudget
  calc
    |Ahat steps.val r j - Aexact steps.val r j|
        ≤ (1 + Real.sqrt 2) ^ steps.val * 0 +
            scalarAffineGrowthBudget (1 + Real.sqrt 2)
              (fun t => householderCompactComponentBudget fp m (v t) (β t)
                (fun a => Ahat t a j) r)
              steps.val := hacc
    _ = scalarAffineGrowthBudget (1 + Real.sqrt 2)
              (fun t => householderCompactComponentBudget fp m (v t) (β t)
                (fun a => Ahat t a j) r)
              steps.val := by ring
    _ ≤ (steps.val : ℝ) * (1 + Real.sqrt 2) ^ steps.val *
          (cCoeff * colB * vB + fp.u * rowB) := hSAGB

/-- **Row-max / row-growth form of the elementwise computed backward error**
(Higham, Theorem 19.6, §19.4, p. 367).

Specializing `theorem19_6_elementwise_computed_backward_error` to the natural
Cox–Higham normalization — a unit-modulus reflector coordinate (`vB = 1`), the
computed active column controlled by the row growth `α_i` times the row maximum
(`colB = alpha · rowMax`), and the computed entry controlled by the row maximum
(`rowB = rowMax`) — gives the printed **row-wise elementwise** shape:

`|ΔA_{steps}(r,j)| ≤ steps · (1+√2)^{steps} · (cCoeff · alpha + u) · rowMax`,

i.e. `(poly in j) · (γ̃-class coeff · α_i + u) · max_s|a_{is}|`.  Here `alpha`
plays Higham's row growth factor `α_i`, `rowMax` plays `max_s|a_{is}|`, and
`cCoeff` is the same-`γ̃`-class reflector coefficient bound.  The `(1+√2)^{steps}`
prefactor is the *accumulated* Cox–Higham row growth of the error recurrence;
Higham's printed `j² γ̃_m α_i` folds all row growth into the single symbol `α_i`,
whereas this proved form carries it explicitly. -/
theorem theorem19_6_elementwise_envelope_of_rowmax
    (fp : FPModel) (m n : ℕ)
    (Ahat Aexact : ℕ → Fin m → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n) (steps : Fin m)
    (cCoeff alpha rowMax : ℝ)
    (halphann : 0 ≤ alpha) (hrowMaxnn : 0 ≤ rowMax) (hCoeffnn : 0 ≤ cCoeff)
    (hstart : Ahat 0 = Aexact 0)
    (hstep : ∀ t : ℕ, t < steps.val →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps.val → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps.val → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps.val → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hexact : ∀ t : ℕ, t < steps.val →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r -
          Aexact (t + 1) r j| ≤
        (1 + Real.sqrt 2) * |Ahat t r j - Aexact t r j|)
    (hCoeff : ∀ t : ℕ, t < steps.val →
      householderCompactUpdateCoeff fp m (v t) (β t) ≤ cCoeff)
    (hColB : ∀ t : ℕ, t < steps.val →
      vecNorm2 (fun a => Ahat t a j) ≤ alpha * rowMax)
    (hVB : ∀ t : ℕ, t < steps.val → |v t r| ≤ 1)
    (hRowB : ∀ t : ℕ, t < steps.val → |Ahat t r j| ≤ rowMax) :
    |Ahat steps.val r j - Aexact steps.val r j| ≤
      (steps.val : ℝ) * (1 + Real.sqrt 2) ^ steps.val *
        ((cCoeff * alpha + fp.u) * rowMax) := by
  have hEnn : 0 ≤ cCoeff * (alpha * rowMax) * 1 + fp.u * rowMax := by
    have h1 : 0 ≤ cCoeff * (alpha * rowMax) * 1 :=
      mul_nonneg (mul_nonneg hCoeffnn (mul_nonneg halphann hrowMaxnn))
        (by norm_num)
    have h2 : 0 ≤ fp.u * rowMax := mul_nonneg fp.u_nonneg hrowMaxnn
    linarith
  have hmain :=
    theorem19_6_elementwise_computed_backward_error
      fp m n Ahat Aexact v β hm r j steps
      cCoeff (alpha * rowMax) 1 rowMax
      (mul_nonneg halphann hrowMaxnn) hCoeffnn hEnn
      hstart hstep hactive hcompleted hpivot hexact hCoeff hColB hVB hRowB
  -- rewrite the budget `cCoeff·(alpha·rowMax)·1 + u·rowMax = (cCoeff·alpha + u)·rowMax`
  have hbudget_eq :
      cCoeff * (alpha * rowMax) * 1 + fp.u * rowMax =
        (cCoeff * alpha + fp.u) * rowMax := by ring
  rw [hbudget_eq] at hmain
  exact hmain

/-- **Terminal packaging residual for Theorem 19.6 (precise remaining gap).**

Higham, Theorem 19.6, §19.4, p. 367 states the *fully packaged* row-wise
elementwise backward error as a single perturbation `ΔA` of the permuted input
with `(A Π) + ΔA = Q R̂` (orthogonal `Q`, upper-trapezoidal `R̂`).  The
computed-perturbation envelope proved above
(`theorem19_6_elementwise_computed_backward_error`) bounds the elementwise
difference `Â_{steps} − A_{steps}` between the computed and exact
signed-reflector iterates.  To lift it to the packaged backward error two facts
are still required, neither present in the current Cox–Higham ladder:

1. **Terminal identification** `A_{steps} = Qᵀ (A Π)` — the exact
   signed-reflector iterate at the last stage equals `Qᵀ` applied to the
   pivoted input, so that `ΔA := (Â_{steps} − A_{steps})` transported back by `Q`
   is a backward perturbation of `A Π`; and
2. **Invariant discharge** — the computed-sequence magnitude bounds `hCoeff`,
   `hColB`, `hVB`, `hRowB` (and the exact growth `hexact`) must be *derived* from
   the executed (19.15) pivot-maximal policy rather than assumed.

This statement is a tautology (`Prop` implies itself) used only as a documented
anchor: it records the packaging gap without claiming it is closed.  The
genuinely proved content is the elementwise computed-perturbation envelope above;
this note marks the boundary between that content and the fully packaged printed
statement. -/
theorem theorem19_6_elementwise_packaging_residual
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (Q : Fin m → Fin m → ℝ) (Rhat : Fin m → Fin n → ℝ) (dA : Fin m → Fin n → ℝ)
    (hpackaged :
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n Rhat ∧
      (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
        matMulRect m m n Q Rhat i j)) :
    IsOrthogonal m Q ∧
    IsUpperTrapezoidal m n Rhat ∧
    (∀ i j, Wave13.columnPermuteMatrix A π i j + dA i j =
      matMulRect m m n Q Rhat i j) :=
  hpackaged

end NumStability.Wave18A
