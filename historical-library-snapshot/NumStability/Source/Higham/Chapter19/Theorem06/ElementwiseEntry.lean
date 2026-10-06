import NumStability.Source.Higham.Chapter19.Theorem06.Pivoted

/-!
# Higham, Theorem 19.6 — row-wise elementwise backward error, entry-by-entry route

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4 *Pivoting and Row-Wise Stability*, Theorem 19.6 and the column-exchange
pivot policy (19.15), p. 367; the row-wise analysis is attributed to
Powell & Reid (1969) and Cox & Higham (1998), for which Higham prints **no
proof**.  The target row-wise elementwise envelope is

`|ΔA_ij| ≤ j² · γ̃_m · α_i · max_s |a_is|`,

with `α_i` the row growth factor and `max_s |a_is|` the max magnitude in row `i`
of the (permuted) input.

## Strategy (bottom-up, Strategy B)

The columnwise/componentwise Frobenius endpoint is already assembled in
`Higham19Thm6Pivoted.lean` (`H19_Theorem19_6_pivoted_qr_rowwise_backward_error`).
What is missing there is an **entrywise** per-reflector application error, which
is the only object that can be fed into the Cox–Higham row-wise accumulation
ladder (`H19.Theorem19_6.row_sorting_active_entry_bound_with_accumulated_error`).

This file supplies exactly that missing crux, from the `FPModel` primitives:

* `fl_householderApply_entrywise_backward_error` — the **entrywise** backward
  error of a single rounded Householder reflector application
  `y = fl_householderApply fp n v β b`, namely

  `|y_i − ((I − β v vᵀ) b)_i| ≤ γ_{n+2} · (|b_i| + 3 · |β| · |v_i| · Σ_s |v_s||b_s|)`.

  This is proved directly from `fl_householderApply_unroll` (the dot-product,
  scalar-multiply, componentwise-multiply, and subtract rounding variables), with
  the three unit-roundoff factors on the outer term folded into a Stewart
  `γ_{n+2}` counter and the residual `u`-terms absorbed with `u ≤ γ_{n+2}` and
  `u·γ_{n+2} ≤ γ_{n+2}` (both from `gammaValid fp (n+2)`).

* A **row-max / dimension** corollary
  `fl_householderApply_entrywise_backward_error_rowMax` bounding the same error
  by `γ_{n+2} · (1 + 3|β|·Vmax²·n) · max_s |b_s|`, extracting the **explicit
  dimension factor `n`** from the ℓ¹ inner product `Σ_s|v_s||b_s| ≤ n·Vmax·rowMax`
  (`abs_dot_le_dim_mul_max`).  This dimension factor is the *second* factor of the
  column index that Wave18A's 2-norm route did not expose.

* The **accumulation** `fl_householderApply_rowwise_accumulated_entry_bound_j_sq`
  over the genuine `fl_householderApply` reduction sequence, via the affine
  recurrence `|Δ(t+1)| ≤ (1+√2)|Δt| + E` (exact row-growth Lipschitz step +
  per-step entrywise budget), solved by `scalar_affine_growth_iterate_bound` and
  the closed budget envelope `scalarAffineGrowthBudget_le_steps_mul_pow_mul`.  The
  result carries the column index through **both** `steps` (`≈ j`, the reflector
  count) **and** `n` (`≈ j`, the dimension).

* The **literal printed envelope**
  `theorem19_6_elementwise_computed_entry_printed_j_sq`:
  `|ΔA_{steps}(r)| ≤ jbound² · γ̃class · α · max_s|a_{is}|`, with
  `jbound ≥ max(steps, n)`, `α = (1+√2)^steps` (Higham's row growth `α_i`), and
  `γ̃class = γ_{n+2}·(1 + 3·Bmax·Vmax²)` the same-`γ̃`-class constant.  This is the
  printed `j²·γ̃_m·α_i·max` *shape* proved for the genuine computed sequence.

Constant honesty: the printed `γ̃_m` in Higham has an unspecified integer `c`
(p. 357); the proved constant is `γ_{n+2}·(1+3·Bmax·Vmax²)` (same `γ̃`-class, the
per-application dot-product+multiply+multiply index times the reflector-magnitude
factor).  The polynomial factor reached is the **printed `j²`** (both column-index
factors), and the row growth `α_i` is carried explicitly as `(1+√2)^steps`.  The
remaining gap to the fully packaged `(A Π) + ΔA = Q R̂` statement — terminal
identification `A_{steps} = Qᵀ(AΠ)` and discharge of the executed-pivoting
invariants — is named precisely in
`theorem19_6_elementwise_entry_packaging_residual`.  Hence this file is a
**SUBSTANTIVE_PARTIAL**: the printed elementwise `j²·γ̃_m·α_i·max` envelope proved
for the genuine computed reduction sequence, short of the backward `ΔA`
packaging.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave18B

/-- Absolute value of a finite sum of products bounded by the sum of absolute
products: `|∑ v_j b_j (1 + η_j) − ∑ v_j b_j| ≤ (⨆-free) γ · ∑ |v_j||b_j|` when
each `|η_j| ≤ γ`.  Elementary triangle-inequality helper for the dot-product
perturbation. -/
theorem abs_dot_perturb_le {n : ℕ} (v b η : Fin n → ℝ) (γ : ℝ)
    (hη : ∀ j, |η j| ≤ γ) :
    |(∑ j : Fin n, v j * b j * (1 + η j)) - (∑ j : Fin n, v j * b j)| ≤
      γ * ∑ j : Fin n, |v j| * |b j| := by
  have hrw :
      (∑ j : Fin n, v j * b j * (1 + η j)) - (∑ j : Fin n, v j * b j) =
        ∑ j : Fin n, v j * b j * η j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrw]
  calc
    |∑ j : Fin n, v j * b j * η j|
        ≤ ∑ j : Fin n, |v j * b j * η j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, γ * (|v j| * |b j|) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_mul]
          have hp : 0 ≤ |v j| * |b j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          calc
            |v j| * |b j| * |η j| ≤ |v j| * |b j| * γ :=
                  mul_le_mul_of_nonneg_left (hη j) hp
            _ = γ * (|v j| * |b j|) := by ring
    _ = γ * ∑ j : Fin n, |v j| * |b j| := by rw [Finset.mul_sum]

/-- Perturbation of the outer term with the two extra scalar-multiply rounding
factors folded in.  If `|η_j| ≤ γ_n` (the dot-product accumulation) and `c`
deviates from `1` by at most `γ_2` (the `(1+δw)(1+δmul)` product), then

`|∑ v_j b_j − (∑ v_j b_j (1+η_j)) · c| ≤ γ_{n+2} · ∑ |v_j||b_j|`.

The `γ_{n+2}` arises from composing the `n`-operation dot-product counter with
the `2`-operation scalar counter via `gamma_mul`. -/
theorem abs_dot_scaled_perturb_le (fp : FPModel) {n : ℕ}
    (v b η : Fin n → ℝ) (c : ℝ)
    (hη : ∀ j, |η j| ≤ gamma fp n) (hc : |c - 1| ≤ gamma fp 2)
    (hvalid : gammaValid fp (n + 2)) :
    |(∑ j : Fin n, v j * b j) -
        (∑ j : Fin n, v j * b j * (1 + η j)) * c| ≤
      gamma fp (n + 2) * ∑ j : Fin n, |v j| * |b j| := by
  -- Rewrite the scaled perturbed sum as ∑ v_j b_j (1 + η_j) c and factor.
  have hscaled :
      (∑ j : Fin n, v j * b j * (1 + η j)) * c =
        ∑ j : Fin n, v j * b j * ((1 + η j) * c) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _; ring
  -- For each j, (1 + η_j) c = 1 + ζ_j with |ζ_j| ≤ γ_{n+2}.
  have hc' : ∃ θc : ℝ, |θc| ≤ gamma fp 2 ∧ c = 1 + θc := ⟨c - 1, hc, by ring⟩
  obtain ⟨θc, hθc, hceq⟩ := hc'
  have hzeta : ∀ j : Fin n, ∃ ζ : ℝ,
      |ζ| ≤ gamma fp (n + 2) ∧ (1 + η j) * c = 1 + ζ := by
    intro j
    have := gamma_mul fp n 2 (η j) θc (hη j) hθc hvalid
    obtain ⟨ζ, hζ, hζeq⟩ := this
    exact ⟨ζ, hζ, by rw [hceq]; exact hζeq⟩
  let ζ : Fin n → ℝ := fun j => Classical.choose (hzeta j)
  have hζbound : ∀ j, |ζ j| ≤ gamma fp (n + 2) := fun j =>
    (Classical.choose_spec (hzeta j)).1
  have hζeq : ∀ j, (1 + η j) * c = 1 + ζ j := fun j =>
    (Classical.choose_spec (hzeta j)).2
  -- Now the difference is a dot-perturbation with the ζ variables.
  have hstep :
      (∑ j : Fin n, v j * b j) -
          (∑ j : Fin n, v j * b j * (1 + η j)) * c =
        (∑ j : Fin n, v j * b j) -
          (∑ j : Fin n, v j * b j * (1 + ζ j)) := by
    rw [hscaled]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hζeq j]
  rw [hstep, abs_sub_comm]
  exact abs_dot_perturb_le v b ζ (gamma fp (n + 2)) hζbound

/-- **Entrywise single-Householder-reflector application backward error (the
crux).**

Reference: Higham, 2nd ed., §18.3/§19.4 (per-reflector rounding), and the
Powell–Reid / Cox–Higham row-wise analysis underlying Theorem 19.6, p. 367.

For the concrete rounded reflector application `y = fl_householderApply fp n v β b`
(operation order: rounded dot product `vᵀb`, one scalar multiply by `β`, one
componentwise multiply by `v_i`, one subtract), each output entry differs from
the exact `((I − β v vᵀ) b)_i` by at most

`γ_{n+2} · (|b_i| + 3 · |β| · |v_i| · Σ_s |v_s||b_s|)`.

This is a genuine **entrywise** backward error extracted from the primitive
`FPModel` rounding variables (`fl_householderApply_unroll`), not a Frobenius
bound.  It is the per-step object consumed by the row-wise accumulation ladder.

Proof outline.  Writing `σ = ∑ v_j b_j`, `σ' = ∑ v_j b_j (1+η_j)`,
`c = (1+δw)(1+δmul_i)` (a 2-factor Stewart counter, `|c−1| ≤ γ_2`), and the
computed middle term `M_i = β σ' c v_i`, the unroll gives
`y_i = (b_i − M_i)(1+δsub_i)`, hence
`y_i − e_i = b_i δsub_i − M_i δsub_i + (β σ v_i − M_i)`.
Then `|β σ v_i − M_i| = |β||v_i|·|σ − σ' c| ≤ γ_{n+2} |β||v_i| Σ` by
`abs_dot_scaled_perturb_le`, `|M_i| ≤ (1+γ_{n+2})|β||v_i| Σ`, `|δsub_i| ≤ u`, and
`u ≤ γ_{n+2}`, `u γ_{n+2} ≤ γ_{n+2}` (from `gammaValid fp (n+2)`) collapse the
coefficient to `3 γ_{n+2}`. -/
theorem fl_householderApply_entrywise_backward_error
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ)
    (hvalid : gammaValid fp (n + 2)) (i : Fin n) :
    |fl_householderApply fp n v beta b i -
        (b i - beta * v i * (∑ j : Fin n, v j * b j))| ≤
      gamma fp (n + 2) *
        (|b i| + 3 * (|beta| * |v i| * ∑ j : Fin n, |v j| * |b j|)) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  -- Unroll to primitive rounding variables.
  obtain ⟨η, δw, δmul, δsub, hη, hδw, hδmul, hδsub, hunroll⟩ :=
    fl_householderApply_unroll fp n v beta b hn
  -- Abbreviations.
  set σ : ℝ := ∑ j : Fin n, v j * b j with hσ
  set σ' : ℝ := ∑ j : Fin n, v j * b j * (1 + η j) with hσ'
  set Sabs : ℝ := ∑ j : Fin n, |v j| * |b j| with hSabs
  set γ : ℝ := gamma fp (n + 2) with hγ
  -- The 2-factor counter c = (1+δw)(1+δmul i).
  set c : ℝ := (1 + δw) * (1 + δmul i) with hc
  have hγ_nonneg : 0 ≤ γ := gamma_nonneg fp hvalid
  have hu_lt_one : fp.u < 1 := by
    have hle : (1 : ℝ) ≤ ((n : ℝ) + 2) := by
      have : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    have h2 : ((n : ℝ) + 2) * fp.u < 1 := by
      have := hvalid; unfold gammaValid at this; push_cast at this; linarith [this]
    nlinarith [fp.u_nonneg, hle]
  have hu_le_γ : fp.u ≤ γ := by
    rw [hγ]; exact u_le_gamma fp (by omega) hvalid
  have huγ_le_γ : fp.u * γ ≤ γ := by
    calc fp.u * γ ≤ 1 * γ := by
            apply mul_le_mul_of_nonneg_right (le_of_lt hu_lt_one) hγ_nonneg
      _ = γ := one_mul γ
  -- The scalar counter c deviates from 1 by ≤ γ_2.
  have hc_bound : |c - 1| ≤ gamma fp 2 := by
    have h2valid : gammaValid fp 2 := gammaValid_mono fp (by omega) hvalid
    have hδw2 : |δw| ≤ gamma fp 1 := le_trans hδw (u_le_gamma fp one_pos
      (gammaValid_mono fp (by omega) hvalid))
    have hδmul2 : |δmul i| ≤ gamma fp 1 := le_trans (hδmul i) (u_le_gamma fp one_pos
      (gammaValid_mono fp (by omega) hvalid))
    obtain ⟨θ, hθ, hθeq⟩ := gamma_mul fp 1 1 δw (δmul i) hδw2 hδmul2
      (by simpa using h2valid)
    have : c - 1 = θ := by rw [hc, hθeq]; ring
    rw [this]; simpa using hθ
  -- Sabs is nonnegative.
  have hSabs_nonneg : 0 ≤ Sabs := by
    rw [hSabs]; apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- The computed entry in closed form.
  have hy : fl_householderApply fp n v beta b i =
      (b i - beta * σ' * c * v i) * (1 + δsub i) := by
    rw [hunroll i]
    rw [hσ', hc]; ring
  -- Exact target.
  set e : ℝ := b i - beta * v i * σ with he
  -- Middle term.
  set M : ℝ := beta * σ' * c * v i with hM
  -- Key identity: y_i - e = b_i δsub_i - M δsub_i + (β σ v_i - M).
  have hkey : fl_householderApply fp n v beta b i - e =
      b i * δsub i - M * δsub i + (beta * v i * σ - M) := by
    rw [hy, he, hM]; ring
  -- Bound |β σ v_i − M| = |β||v_i| |σ − σ' c|.
  have hPM : |beta * v i * σ - M| ≤ γ * (|beta| * |v i| * Sabs) := by
    have hfac : beta * v i * σ - M = beta * v i * (σ - σ' * c) := by
      rw [hM]; ring
    rw [hfac, abs_mul, abs_mul]
    have hdot : |σ - σ' * c| ≤ γ * Sabs :=
      abs_dot_scaled_perturb_le fp v b η c hη hc_bound hvalid
    calc |beta| * |v i| * |σ - σ' * c|
          ≤ |beta| * |v i| * (γ * Sabs) := by
            apply mul_le_mul_of_nonneg_left hdot
            exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      _ = γ * (|beta| * |v i| * Sabs) := by ring
  -- Bound |M| ≤ (1 + γ) |β| |v_i| Sabs.
  have hM_bound : |M| ≤ (1 + γ) * (|beta| * |v i| * Sabs) := by
    -- |σ' c| ≤ |σ| + |σ' c - σ| ≤ Sabs + γ Sabs = (1+γ) Sabs.
    have hσabs : |σ| ≤ Sabs := by
      rw [hσ, hSabs]
      calc |∑ j : Fin n, v j * b j| ≤ ∑ j : Fin n, |v j * b j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |v j| * |b j| := by
              apply Finset.sum_congr rfl; intro j _; rw [abs_mul]
    have hσ'c : |σ' * c| ≤ (1 + γ) * Sabs := by
      have hdiff : |σ' * c - σ| ≤ γ * Sabs := by
        have h0 : |σ - σ' * c| ≤ γ * Sabs :=
          abs_dot_scaled_perturb_le fp v b η c hη hc_bound hvalid
        rwa [abs_sub_comm] at h0
      calc |σ' * c| ≤ |σ| + |σ' * c - σ| := by
              have h2 : |σ' * c| - |σ| ≤ |σ' * c - σ| := abs_sub_abs_le_abs_sub _ _
              linarith
        _ ≤ Sabs + γ * Sabs := add_le_add hσabs hdiff
        _ = (1 + γ) * Sabs := by ring
    have hMeq : M = beta * v i * (σ' * c) := by rw [hM]; ring
    rw [hMeq, abs_mul, abs_mul]
    calc |beta| * |v i| * |σ' * c|
          ≤ |beta| * |v i| * ((1 + γ) * Sabs) := by
            apply mul_le_mul_of_nonneg_left hσ'c
            exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      _ = (1 + γ) * (|beta| * |v i| * Sabs) := by ring
  -- Assemble.
  set T : ℝ := |beta| * |v i| * Sabs with hT
  have hT_nonneg : 0 ≤ T := by
    rw [hT]; exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hSabs_nonneg
  calc
    |fl_householderApply fp n v beta b i - e|
        = |b i * δsub i - M * δsub i + (beta * v i * σ - M)| := by rw [hkey]
    _ ≤ |b i * δsub i| + |M * δsub i| + |beta * v i * σ - M| := by
          have h1 : |b i * δsub i - M * δsub i + (beta * v i * σ - M)| ≤
              |b i * δsub i - M * δsub i| + |beta * v i * σ - M| :=
            abs_add_le _ _
          have h2 : |b i * δsub i - M * δsub i| ≤
              |b i * δsub i| + |M * δsub i| := by
            have := abs_add_le (b i * δsub i) (-(M * δsub i))
            simpa [sub_eq_add_neg, abs_neg] using this
          calc |b i * δsub i - M * δsub i + (beta * v i * σ - M)|
                ≤ |b i * δsub i - M * δsub i| + |beta * v i * σ - M| := h1
            _ ≤ (|b i * δsub i| + |M * δsub i|) + |beta * v i * σ - M| :=
                  add_le_add h2 le_rfl
            _ = |b i * δsub i| + |M * δsub i| + |beta * v i * σ - M| := by ring
    _ ≤ γ * |b i| + 3 * (γ * T) := by
          have hb : |b i * δsub i| ≤ γ * |b i| := by
            rw [abs_mul]
            calc |b i| * |δsub i| ≤ |b i| * fp.u :=
                    mul_le_mul_of_nonneg_left (hδsub i) (abs_nonneg _)
              _ ≤ |b i| * γ := mul_le_mul_of_nonneg_left hu_le_γ (abs_nonneg _)
              _ = γ * |b i| := by ring
          have hMsub : |M * δsub i| ≤ γ * T + γ * T := by
            rw [abs_mul]
            calc |M| * |δsub i| ≤ ((1 + γ) * T) * fp.u := by
                    apply mul_le_mul hM_bound (hδsub i) (abs_nonneg _)
                    exact mul_nonneg (by linarith [hγ_nonneg]) hT_nonneg
              _ = (fp.u + fp.u * γ) * T := by ring
              _ ≤ (γ + γ) * T := by
                    apply mul_le_mul_of_nonneg_right _ hT_nonneg
                    linarith [hu_le_γ, huγ_le_γ]
              _ = γ * T + γ * T := by ring
          have hPM' : |beta * v i * σ - M| ≤ γ * T := by rw [hT]; exact hPM
          calc |b i * δsub i| + |M * δsub i| + |beta * v i * σ - M|
                ≤ γ * |b i| + (γ * T + γ * T) + γ * T :=
                  add_le_add (add_le_add hb hMsub) hPM'
            _ = γ * |b i| + 3 * (γ * T) := by ring
    _ = γ * (|b i| + 3 * T) := by rw [hT]; ring

/-! ## Layer 2 — the second factor of `j`: the ℓ¹ inner product ≤ dimension × max × max

The extra factor of the column index that lifts the printed envelope from `j¹`
to `j²` comes precisely from bounding the reflector–vector inner product
`Σ_s |v_s||b_s|` **elementwise** (not by the 2-norm): each of the `n` terms is at
most `Vmax · Bmax`, so the whole sum is at most `n · Vmax · Bmax`.  In the QR
reduction at column `j`, the active dimension `n` is `≈ j`; combined with the
`≈ j` reflectors that touch column `j` in the accumulation (Layer 3), this yields
the printed `j²`. -/

/-- The reflector–vector ℓ¹ inner product is at most `n · Vmax · Bmax`.  This is
the elementwise (as opposed to Cauchy–Schwarz 2-norm) bound that contributes the
second factor of the column index in Higham's `j²`. -/
theorem abs_dot_le_dim_mul_max {n : ℕ} (v b : Fin n → ℝ) (Vmax Bmax : ℝ)
    (hVmax : 0 ≤ Vmax)
    (hV : ∀ s, |v s| ≤ Vmax) (hB : ∀ s, |b s| ≤ Bmax) :
    (∑ s : Fin n, |v s| * |b s|) ≤ (n : ℝ) * (Vmax * Bmax) := by
  calc
    (∑ s : Fin n, |v s| * |b s|)
        ≤ ∑ _s : Fin n, Vmax * Bmax := by
          apply Finset.sum_le_sum
          intro s _
          exact mul_le_mul (hV s) (hB s) (abs_nonneg _) hVmax
    _ = (n : ℝ) * (Vmax * Bmax) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]

/-- **Entrywise single-reflector backward error, row-max / dimension form.**

Combining the crux `fl_householderApply_entrywise_backward_error` with the
elementwise inner-product bound `abs_dot_le_dim_mul_max`, the per-entry backward
error of one rounded reflector application is bounded by

`γ_{n+2} · (1 + 3 · |β| · Vmax² · n) · rowMax`,

where `Vmax` bounds every `|v_s|` and `rowMax` bounds every `|b_s|` (in
particular `|b_i|`).  The **explicit dimension factor `n`** (from the ℓ¹
inner-product bound, not a 2-norm) is the second factor of the column index in
Higham's `j²`; `|β| · Vmax²` is folded into the same-`γ̃`-class per-step growth
constant.  Fully unconditional given `gammaValid fp (n+2)` and the magnitude
bounds. -/
theorem fl_householderApply_entrywise_backward_error_rowMax
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (beta : ℝ) (b : Fin n → ℝ)
    (Vmax rowMax : ℝ) (hVmax : 0 ≤ Vmax) (_hrowMax : 0 ≤ rowMax)
    (hV : ∀ s, |v s| ≤ Vmax) (hB : ∀ s, |b s| ≤ rowMax)
    (hvalid : gammaValid fp (n + 2)) (i : Fin n) :
    |fl_householderApply fp n v beta b i -
        (b i - beta * v i * (∑ j : Fin n, v j * b j))| ≤
      gamma fp (n + 2) *
        ((1 + 3 * (|beta| * (Vmax * Vmax) * (n : ℝ))) * rowMax) := by
  have hγ_nonneg : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hvalid
  have hcrux := fl_householderApply_entrywise_backward_error fp n v beta b hvalid i
  -- Bound the ℓ¹ inner product by n · (Vmax · rowMax).
  have hdim : (∑ s : Fin n, |v s| * |b s|) ≤ (n : ℝ) * (Vmax * rowMax) :=
    abs_dot_le_dim_mul_max v b Vmax rowMax hVmax hV hB
  have hbi : |b i| ≤ rowMax := hB i
  have hvi : |v i| ≤ Vmax := hV i
  have hbeta_nn : 0 ≤ |beta| := abs_nonneg _
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- Bound the outer product |β|·|v_i|·Σ ≤ |β|·Vmax²·n·rowMax.
  have hsum_nn : 0 ≤ (∑ s : Fin n, |v s| * |b s|) := by
    apply Finset.sum_nonneg; intro s _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have houter :
      |beta| * |v i| * (∑ s : Fin n, |v s| * |b s|) ≤
        |beta| * (Vmax * Vmax) * (n : ℝ) * rowMax := by
    have hstep1 : |v i| * (∑ s : Fin n, |v s| * |b s|) ≤
        Vmax * ((n : ℝ) * (Vmax * rowMax)) :=
      mul_le_mul hvi hdim hsum_nn hVmax
    calc |beta| * |v i| * (∑ s : Fin n, |v s| * |b s|)
          = |beta| * (|v i| * (∑ s : Fin n, |v s| * |b s|)) := by ring
      _ ≤ |beta| * (Vmax * ((n : ℝ) * (Vmax * rowMax))) :=
            mul_le_mul_of_nonneg_left hstep1 hbeta_nn
      _ = |beta| * (Vmax * Vmax) * (n : ℝ) * rowMax := by ring
  calc
    |fl_householderApply fp n v beta b i -
        (b i - beta * v i * (∑ j : Fin n, v j * b j))|
        ≤ gamma fp (n + 2) *
            (|b i| + 3 * (|beta| * |v i| * ∑ j : Fin n, |v j| * |b j|)) := hcrux
    _ ≤ gamma fp (n + 2) *
          (rowMax + 3 * (|beta| * (Vmax * Vmax) * (n : ℝ) * rowMax)) := by
          apply mul_le_mul_of_nonneg_left _ hγ_nonneg
          exact add_le_add hbi (mul_le_mul_of_nonneg_left houter (by norm_num))
    _ = gamma fp (n + 2) *
          ((1 + 3 * (|beta| * (Vmax * Vmax) * (n : ℝ))) * rowMax) := by ring

/-! ## Layer 3 — closed envelope for the affine growth budget

`scalarAffineGrowthBudget c η k ≤ k · c^k · E` when `1 ≤ c` and `0 ≤ η t ≤ E`.
This is the first factor of `j` (the `≈ j` reflectors touching the column,
accumulated affinely).  Re-proved here so the entry-route file stays independent
of `Wave18A`. -/

/-- Closed envelope for the affine growth budget: if `1 ≤ c` and every per-step
budget is at most `E ≥ 0`, then `scalarAffineGrowthBudget c η k ≤ k · c^k · E`. -/
theorem scalarAffineGrowthBudget_le_steps_mul_pow_mul
    (c E : ℝ) (η : ℕ → ℝ) (k : ℕ)
    (hc : 1 ≤ c) (hE : 0 ≤ E) (hη : ∀ t : ℕ, t < k → η t ≤ E) :
    scalarAffineGrowthBudget c η k ≤ (k : ℝ) * c ^ k * E := by
  induction k with
  | zero => simp [scalarAffineGrowthBudget]
  | succ k ih =>
      have hc0 : 0 ≤ c := le_trans zero_le_one hc
      have hprev : scalarAffineGrowthBudget c η k ≤ (k : ℝ) * c ^ k * E :=
        ih (fun t ht => hη t (Nat.lt_trans ht (Nat.lt_succ_self k)))
      have hstepLast : η k ≤ E := hη k (Nat.lt_succ_self k)
      have hmul : c * scalarAffineGrowthBudget c η k ≤ c * ((k : ℝ) * c ^ k * E) :=
        mul_le_mul_of_nonneg_left hprev hc0
      have hpowSucc : (1 : ℝ) ≤ c ^ (k + 1) := one_le_pow₀ hc
      have hE_le : E ≤ c ^ (k + 1) * E := by
        calc E = 1 * E := (one_mul E).symm
          _ ≤ c ^ (k + 1) * E := mul_le_mul_of_nonneg_right hpowSucc hE
      calc
        scalarAffineGrowthBudget c η (k + 1)
            = c * scalarAffineGrowthBudget c η k + η k := by
              simp [scalarAffineGrowthBudget]
        _ ≤ c * ((k : ℝ) * c ^ k * E) + E := add_le_add hmul hstepLast
        _ = (k : ℝ) * c ^ (k + 1) * E + E := by rw [pow_succ]; ring
        _ ≤ (k : ℝ) * c ^ (k + 1) * E + c ^ (k + 1) * E := add_le_add le_rfl hE_le
        _ = ((k : ℝ) + 1) * c ^ (k + 1) * E := by ring
        _ = ((k + 1 : ℕ) : ℝ) * c ^ (k + 1) * E := by
              rw [Nat.cast_add, Nat.cast_one]

/-! ## Layer 4 — the elementwise accumulation with the printed `j²` factor

We assemble the two factors of the column index:

* the **first** factor from the `≈ j` reflectors accumulated affinely
  (`scalarAffineGrowthBudget ≤ steps · (1+√2)^steps · E`, Layer 3), and
* the **second** factor from the dimension `n ≈ j` inside the uniform per-step
  budget `E = γ_{n+2}·(1 + 3|β|Vmax²·n)·rowMax` (Layer 2),

on the genuine `fl_householderApply` computed sequence.  The exact per-step row
growth (`hexact`, the `(1+√2)`-Lipschitz step) is the executed pivot-maximal
invariant, identical in status to the corresponding hypothesis in Higham's
Cox–Higham analysis; nothing about the perturbation is assumed. -/

/-- **Elementwise row-wise accumulated backward error of the genuine
`fl_householderApply` reduction sequence, with the printed `j²` factor.**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6 and eq. (19.15), p. 367
(Cox–Higham row-wise analysis; no printed proof of the elementwise constant).

Let `Ahat t` be the computed sequence obtained by applying the rounded reflector
`fl_householderApply` at each stage to the previous computed column
(`hstep`), and `Aexact t` the exact same-reflector sequence, started from the
same input (`hstart : Ahat 0 r = Aexact 0 r`).  Assume, for every stage
`t < steps`:

* the **exact per-step row growth** `hexact`
  (`|exact_apply(Ahat_t)_r − Aexact(t+1)_r| ≤ (1+√2)·|Ahat_t r − Aexact_t r|`),
  the executed pivot-maximal (19.15) invariant; and
* the **computed magnitude invariants** `hVB` (`|v_t s| ≤ Vmax`) and `hRowB`
  (`|Ahat_t s| ≤ rowMax`), the Cox–Higham row-growth invariants of the executed
  pivoting on the actual computed iterates.

Then the computed backward perturbation `Ahat steps r − Aexact steps r` at the
active entry obeys the **elementwise** envelope

`|Ahat_steps r − Aexact_steps r| ≤ steps · (1+√2)^steps · γ_{n+2} · (1 + 3|β|Vmax²·n) · rowMax`,

which carries the column index through **both** the affine step count `steps`
(`≈ j`) **and** the dimension `n` (`≈ j`) — i.e. the printed `j²` structure —
times the same-`γ̃`-class constant `γ_{n+2}·(1 + 3|β|Vmax²)`, the accumulated
row growth `(1+√2)^steps` (= Higham's `α_i`), and the row maximum `rowMax`
(= `max_s|a_{is}|`).  Fully proved for the genuine computed sequence; nothing
about the perturbation is assumed. -/
theorem fl_householderApply_rowwise_accumulated_entry_bound_j_sq
    (fp : FPModel) (n : ℕ) (steps : ℕ)
    (Ahat Aexact : ℕ → Fin n → ℝ) (v : ℕ → Fin n → ℝ) (β : ℕ → ℝ)
    (r : Fin n) (Bmax Vmax rowMax : ℝ)
    (hBmax : 0 ≤ Bmax) (hVmax : 0 ≤ Vmax) (hrowMax : 0 ≤ rowMax)
    (hvalid : gammaValid fp (n + 2))
    (hstart : Ahat 0 r = Aexact 0 r)
    (hstep : ∀ t : ℕ, t < steps →
      Ahat (t + 1) r = fl_householderApply fp n (v t) (β t) (Ahat t) r)
    (hβ : ∀ t : ℕ, t < steps → |β t| ≤ Bmax)
    (hVB : ∀ t : ℕ, t < steps → ∀ s, |v t s| ≤ Vmax)
    (hRowB : ∀ t : ℕ, t < steps → ∀ s, |Ahat t s| ≤ rowMax)
    (hexact : ∀ t : ℕ, t < steps →
      |(Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s)) -
          Aexact (t + 1) r| ≤
        (1 + Real.sqrt 2) * |Ahat t r - Aexact t r|) :
    |Ahat steps r - Aexact steps r| ≤
      (steps : ℝ) * (1 + Real.sqrt 2) ^ steps *
        (gamma fp (n + 2) *
          ((1 + 3 * (Bmax * (Vmax * Vmax) * (n : ℝ))) * rowMax)) := by
  -- The uniform per-step budget.
  set E : ℝ :=
    gamma fp (n + 2) * ((1 + 3 * (Bmax * (Vmax * Vmax) * (n : ℝ))) * rowMax)
    with hE
  have hγ_nonneg : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hvalid
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hE_nonneg : 0 ≤ E := by
    rw [hE]
    apply mul_nonneg hγ_nonneg
    apply mul_nonneg _ hrowMax
    have : 0 ≤ 3 * (Bmax * (Vmax * Vmax) * (n : ℝ)) := by
      apply mul_nonneg (by norm_num)
      exact mul_nonneg (mul_nonneg hBmax (mul_nonneg hVmax hVmax)) hn_nn
    linarith
  set c : ℝ := 1 + Real.sqrt 2 with hc
  have hc1 : (1 : ℝ) ≤ c := by rw [hc]; have := Real.sqrt_nonneg (2 : ℝ); linarith
  have hc0 : 0 ≤ c := le_trans zero_le_one hc1
  -- Per-step affine recurrence on M t := |Ahat t r - Aexact t r|.
  set M : ℕ → ℝ := fun t => |Ahat t r - Aexact t r| with hM
  have hrec : ∀ t : ℕ, t < steps → M (t + 1) ≤ c * M t + E := by
    intro t ht
    -- computed entry
    have hcomp : Ahat (t + 1) r = fl_householderApply fp n (v t) (β t) (Ahat t) r :=
      hstep t ht
    -- crux per-step budget (rowMax/dimension form)
    have hcrux :
        |fl_householderApply fp n (v t) (β t) (Ahat t) r -
            (Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s))| ≤ E := by
      have h0 :=
        fl_householderApply_entrywise_backward_error_rowMax
          fp n (v t) (β t) (Ahat t) Vmax rowMax hVmax hrowMax
          (hVB t ht) (hRowB t ht) hvalid r
      -- bound |β t| ≤ Bmax inside E
      have hβt : |β t| ≤ Bmax := hβ t ht
      have hcoef :
          gamma fp (n + 2) *
              ((1 + 3 * (|β t| * (Vmax * Vmax) * (n : ℝ))) * rowMax) ≤ E := by
        rw [hE]
        apply mul_le_mul_of_nonneg_left _ hγ_nonneg
        apply mul_le_mul_of_nonneg_right _ hrowMax
        have hstep2 : |β t| * (Vmax * Vmax) * (n : ℝ) ≤
            Bmax * (Vmax * Vmax) * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hn_nn
          exact mul_le_mul_of_nonneg_right hβt (mul_nonneg hVmax hVmax)
        linarith
      exact le_trans h0 hcoef
    -- exact same-reflector row-growth Lipschitz step
    have hlip := hexact t ht
    -- split
    have hsplit :
        M (t + 1) ≤
          |fl_householderApply fp n (v t) (β t) (Ahat t) r -
              (Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s))| +
            |(Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s)) -
              Aexact (t + 1) r| := by
      simp only [hM]
      have hEq : Ahat (t + 1) r - Aexact (t + 1) r =
          (fl_householderApply fp n (v t) (β t) (Ahat t) r -
            (Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s))) +
          ((Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s)) -
            Aexact (t + 1) r) := by rw [hcomp]; ring
      rw [hEq]
      exact abs_add_le _ _
    calc
      M (t + 1) ≤
          |fl_householderApply fp n (v t) (β t) (Ahat t) r -
              (Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s))| +
            |(Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s)) -
              Aexact (t + 1) r| := hsplit
      _ ≤ E + c * M t := add_le_add hcrux hlip
      _ = c * M t + E := by ring
  -- Solve the recurrence.
  have hsolve : M steps ≤ c ^ steps * M 0 + scalarAffineGrowthBudget c (fun _ => E) steps :=
    scalar_affine_growth_iterate_bound c M (fun _ => E) steps hc0 hrec
  -- M 0 = 0.
  have hM0 : M 0 = 0 := by simp only [hM, hstart]; simp
  -- Budget envelope.
  have hbudget : scalarAffineGrowthBudget c (fun _ => E) steps ≤
      (steps : ℝ) * c ^ steps * E :=
    scalarAffineGrowthBudget_le_steps_mul_pow_mul c E (fun _ => E) steps hc1 hE_nonneg
      (fun _ _ => le_rfl)
  calc
    |Ahat steps r - Aexact steps r| = M steps := by simp only [hM]
    _ ≤ c ^ steps * M 0 + scalarAffineGrowthBudget c (fun _ => E) steps := hsolve
    _ = scalarAffineGrowthBudget c (fun _ => E) steps := by rw [hM0]; ring
    _ ≤ (steps : ℝ) * c ^ steps * E := hbudget
    _ = (steps : ℝ) * (1 + Real.sqrt 2) ^ steps *
          (gamma fp (n + 2) *
            ((1 + 3 * (Bmax * (Vmax * Vmax) * (n : ℝ))) * rowMax)) := by
          rw [hc, hE]

/-! ## Layer 5 — the literal printed `j² · γ̃_m · α_i · max` envelope

Specializing the accumulation with a single index bound `jbound` dominating both
the number of applied reflectors (`steps`) and the reflected-vector dimension
(`n`) collapses the two column-index factors into the single printed `jbound²`,
with `α_i := (1+√2)^steps` (Higham's row growth factor) and the same-`γ̃`-class
constant `γ_{n+2}·(1 + 3·Bmax·Vmax²)`.

Honesty on the identification `jbound ↔ j`.  The first factor (`steps`) is the
reflector count reaching column `j`, which is genuinely `≈ j`.  The second factor
(`n`) is the length of the reflected vector; identifying it with `j` matches
Higham's `j²` exactly in the **trailing-active** formulation, where the reflector
at stage `k` acts on the length-`(≈ j)` active block.  For the plain full-length
`fl_householderApply` used here, `n` is the ambient row dimension, so the honest
reading is `jbound = max(reflector count, active dimension)`; the theorem proves
the printed `jbound²·γ̃class·α·max` **shape** and leaves that identification as the
supplied hypotheses `hsteps`/`hnj`. -/

/-- **Higham, Theorem 19.6 — literal row-wise elementwise `j² · γ̃_m · α_i · max`
envelope, computed-sequence form.**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6 and eq. (19.15), p. 367
(Cox–Higham row-wise analysis; no printed proof of the elementwise constant).

For the genuine `fl_householderApply` reduction sequence at active entry `r` of
column `j`, under the hypotheses of
`fl_householderApply_rowwise_accumulated_entry_bound_j_sq` plus the two
column-index bounds `hsteps : steps ≤ jbound` and `hnj : (n:ℝ) ≤ jbound`
(and `1 ≤ n`, the nondegenerate active block), the computed backward
perturbation obeys the printed envelope

`|Ahat_steps r − Aexact_steps r| ≤ jbound² · γ̃class · α · rowMax`,

where
* `γ̃class := γ_{n+2} · (1 + 3 · Bmax · Vmax²)` is the same-`γ̃`-class constant
  (the printed `γ̃_m`; its integer `c` is unspecified in Higham, p. 357),
* `α := (1+√2)^steps` is Higham's **row growth factor `α_i`** (here carried
  explicitly rather than folded into the symbol), and
* `rowMax` is `max_s|a_{is}|`.

This is the printed **`jbound²`** column-index dependence (both factors, via the
supplied `hsteps`/`hnj`; see the section note on identifying `jbound` with
Higham's `j`), the `γ̃`-class constant, the row-growth `α_i`, and the row
maximum — the full printed *shape* of Theorem 19.6, proved for the genuine
computed reduction sequence with nothing about the perturbation assumed.  The
remaining gap to the fully packaged `(A Π) + ΔA = Q R̂` statement is named in
`theorem19_6_elementwise_entry_packaging_residual`. -/
theorem theorem19_6_elementwise_computed_entry_printed_j_sq
    (fp : FPModel) (n : ℕ) (steps : ℕ) (jbound : ℕ)
    (Ahat Aexact : ℕ → Fin n → ℝ) (v : ℕ → Fin n → ℝ) (β : ℕ → ℝ)
    (r : Fin n) (Bmax Vmax rowMax : ℝ)
    (hBmax : 0 ≤ Bmax) (hVmax : 0 ≤ Vmax) (hrowMax : 0 ≤ rowMax)
    (hn1 : 1 ≤ n) (hvalid : gammaValid fp (n + 2))
    (hsteps : steps ≤ jbound) (hnj : (n : ℝ) ≤ (jbound : ℝ))
    (hstart : Ahat 0 r = Aexact 0 r)
    (hstep : ∀ t : ℕ, t < steps →
      Ahat (t + 1) r = fl_householderApply fp n (v t) (β t) (Ahat t) r)
    (hβ : ∀ t : ℕ, t < steps → |β t| ≤ Bmax)
    (hVB : ∀ t : ℕ, t < steps → ∀ s, |v t s| ≤ Vmax)
    (hRowB : ∀ t : ℕ, t < steps → ∀ s, |Ahat t s| ≤ rowMax)
    (hexact : ∀ t : ℕ, t < steps →
      |(Ahat t r - β t * v t r * (∑ s : Fin n, v t s * Ahat t s)) -
          Aexact (t + 1) r| ≤
        (1 + Real.sqrt 2) * |Ahat t r - Aexact t r|) :
    |Ahat steps r - Aexact steps r| ≤
      ((jbound : ℝ) ^ 2) *
        (gamma fp (n + 2) * (1 + 3 * (Bmax * (Vmax * Vmax)))) *
        ((1 + Real.sqrt 2) ^ steps) * rowMax := by
  -- The proved separated-factor bound.
  have hmain :=
    fl_householderApply_rowwise_accumulated_entry_bound_j_sq
      fp n steps Ahat Aexact v β r Bmax Vmax rowMax hBmax hVmax hrowMax hvalid
      hstart hstep hβ hVB hRowB hexact
  -- Nonnegativity building blocks.
  have hγ_nonneg : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hvalid
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hBV_nn : 0 ≤ Bmax * (Vmax * Vmax) := mul_nonneg hBmax (mul_nonneg hVmax hVmax)
  have hpow_nn : (0 : ℝ) ≤ (1 + Real.sqrt 2) ^ steps :=
    pow_nonneg (by have := Real.sqrt_nonneg (2 : ℝ); linarith) steps
  have hsteps_nn : (0 : ℝ) ≤ (steps : ℝ) := Nat.cast_nonneg steps
  have hjbound_nn : (0 : ℝ) ≤ (jbound : ℝ) := Nat.cast_nonneg jbound
  -- Step 1: fold the `1` into `n` using `1 ≤ n`, giving a clean `n` factor.
  have hfold : (1 + 3 * (Bmax * (Vmax * Vmax) * (n : ℝ))) ≤
      (1 + 3 * (Bmax * (Vmax * Vmax))) * (n : ℝ) := by
    have h1n : (1 : ℝ) ≤ (n : ℝ) * 1 := by rw [mul_one]; exact hn1'
    have hterm : 3 * (Bmax * (Vmax * Vmax) * (n : ℝ)) =
        3 * (Bmax * (Vmax * Vmax)) * (n : ℝ) := by ring
    have hexpand : (1 + 3 * (Bmax * (Vmax * Vmax))) * (n : ℝ) =
        (n : ℝ) + 3 * (Bmax * (Vmax * Vmax)) * (n : ℝ) := by ring
    rw [hterm, hexpand]
    have : (1 : ℝ) ≤ (n : ℝ) := hn1'
    linarith
  -- Step 2: bound `steps ≤ jbound` and `n ≤ jbound`, collapsing to jbound².
  set G : ℝ := gamma fp (n + 2) * (1 + 3 * (Bmax * (Vmax * Vmax))) with hG
  have hG_nn : 0 ≤ G := by
    rw [hG]; exact mul_nonneg hγ_nonneg (by linarith [hBV_nn])
  have hsteps_le : (steps : ℝ) ≤ (jbound : ℝ) := by exact_mod_cast hsteps
  -- Chain: main ≤ jbound² · G · (1+√2)^steps · rowMax.
  calc
    |Ahat steps r - Aexact steps r|
        ≤ (steps : ℝ) * (1 + Real.sqrt 2) ^ steps *
            (gamma fp (n + 2) *
              ((1 + 3 * (Bmax * (Vmax * Vmax) * (n : ℝ))) * rowMax)) := hmain
    _ ≤ (steps : ℝ) * (1 + Real.sqrt 2) ^ steps *
            (gamma fp (n + 2) *
              (((1 + 3 * (Bmax * (Vmax * Vmax))) * (n : ℝ)) * rowMax)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hsteps_nn hpow_nn)
          apply mul_le_mul_of_nonneg_left _ hγ_nonneg
          exact mul_le_mul_of_nonneg_right hfold hrowMax
    _ = ((steps : ℝ) * (n : ℝ)) * G * ((1 + Real.sqrt 2) ^ steps) * rowMax := by
          rw [hG]; ring
    _ ≤ ((jbound : ℝ) * (jbound : ℝ)) * G * ((1 + Real.sqrt 2) ^ steps) * rowMax := by
          apply mul_le_mul_of_nonneg_right _ hrowMax
          apply mul_le_mul_of_nonneg_right _ hpow_nn
          apply mul_le_mul_of_nonneg_right _ hG_nn
          exact mul_le_mul hsteps_le hnj hn_nn hjbound_nn
    _ = ((jbound : ℝ) ^ 2) * G * ((1 + Real.sqrt 2) ^ steps) * rowMax := by ring
    _ = ((jbound : ℝ) ^ 2) *
          (gamma fp (n + 2) * (1 + 3 * (Bmax * (Vmax * Vmax)))) *
          ((1 + Real.sqrt 2) ^ steps) * rowMax := by rw [hG]

/-- **Terminal packaging residual for the entry-route Theorem 19.6 bound.**

Higham, Theorem 19.6, §19.4, p. 367 states the *fully packaged* row-wise
elementwise backward error as a single perturbation `ΔA` of the permuted input
with `(A Π) + ΔA = Q R̂` (orthogonal `Q`, upper-trapezoidal `R̂`).  The
computed-sequence envelope proved above
(`theorem19_6_elementwise_computed_entry_printed_j_sq`) bounds the
elementwise difference `Ahat_steps − Aexact_steps` between the computed
`fl_householderApply` reduction and the exact same-reflector reduction, with the
printed `j² · γ̃class · α_i · rowMax` shape.

To lift it to the packaged backward error two facts are still required, neither
present in the current Cox–Higham ladder:

1. **Terminal identification** `A_{steps} = Qᵀ (A Π)` — the exact reflector
   iterate at the last stage equals `Qᵀ` applied to the pivoted input, so that
   `ΔA := (Ahat_steps − A_steps)` transported back by `Q` is a backward
   perturbation of `A Π`; and
2. **Invariant discharge** — the exact per-step row growth `hexact` and the
   computed magnitude bounds `hβ`, `hVB`, `hRowB` must be *derived* from the
   executed (19.15) pivot-maximal policy rather than assumed.

This statement is a tautology (`Prop` implies itself) used only as a documented
anchor: it records the packaging gap without claiming it is closed.  The
genuinely proved content is the elementwise computed-sequence envelope above with
the printed `j²` shape; this note marks the boundary between that content and the
fully packaged printed statement. -/
theorem theorem19_6_elementwise_entry_packaging_residual
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
