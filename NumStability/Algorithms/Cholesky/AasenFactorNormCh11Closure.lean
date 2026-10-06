import NumStability.Algorithms.HighamChapter11

/-!
# Aasen outer-factor infinity-norm cap (Higham Thm 11.8 structural closure)

Higham's normwise backward-error endpoint for Aasen's method (Thm 11.8), as
formalized in `HighamChapter11.lean`
(`higham11_8_aasen_relative_coeff_le_of_gamma_base_square_bounds` and its two
input caps `hprod_base` / `hprod_rel`), *assumes* the structural product cap

  `κL · κLT ≤ (n − 1)²`,

where `κL ≥ ‖L‖∞` and `κLT ≥ ‖Lᵀ‖∞`, and `L` is the Aasen outer factor: unit
lower triangular, with first column `e₁` (partial pivoting), and `|L i j| ≤ 1`.

This file discharges that structural cap *for the norms themselves*, proving

  `‖L‖∞ · ‖Lᵀ‖∞ ≤ (n − 1)²`

directly from the factor structure, so it is no longer an unproven assumption.

## Main results

* `sum_abs_le_of_exists_zero`   — generic "one guaranteed zero entry" row-sum
  bound: a length-`n` row with entries `≤ 1` in absolute value and at least one
  zero entry sums to at most `n − 1`.
* `aasen_L_infNorm_le`          — `infNorm L ≤ n − 1`.
* `aasen_LT_infNorm_le`         — `infNorm Lᵀ ≤ n − 1`.
* `aasen_L_infNorm_mul_transpose_le_sq`         — `‖L‖∞ · ‖Lᵀ‖∞ ≤ (n − 1)²`.
* `aasen_L_infNorm_mul_transpose_le_natCast_sq` — same, with the RHS written in
  the exact `((n − 1 : ℕ) : ℝ) ^ 2` shape used by the `hprod_base` cap.

All results assume `2 ≤ n`. This hypothesis is *necessary*, not a convenience:
for `n = 1` the outer factor is `L = [1]`, so `‖L‖∞ · ‖Lᵀ‖∞ = 1` while
`(n − 1)² = 0`, and the cap is false. (For `n = 0` both sides are trivial, but
the endpoint is only ever invoked with `n ≥ 2`.)
-/

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenNorm

open NumStability

/-- Generic row-sum bound with one guaranteed vanishing entry.

If every entry of a length-`n` real vector `g` is bounded by `1` in absolute
value and at least one entry `g j₀` is zero, then `∑ⱼ |gⱼ| ≤ n − 1`: dropping
the guaranteed zero entry leaves `n − 1` entries, each contributing at most `1`. -/
lemma sum_abs_le_of_exists_zero {n : ℕ} (hn : 1 ≤ n) (g : Fin n → ℝ)
    (hb : ∀ j, |g j| ≤ 1) (j₀ : Fin n) (hz : g j₀ = 0) :
    ∑ j : Fin n, |g j| ≤ (n : ℝ) - 1 := by
  have hf0 : (fun j => |g j|) j₀ = 0 := by simp [hz]
  -- The full sum equals the sum over `univ \ {j₀}` since the dropped term is 0.
  rw [← Finset.sum_erase (f := fun j => |g j|) Finset.univ hf0]
  have hcard : (Finset.univ.erase j₀).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ,
      Fintype.card_fin]
  calc
    ∑ j ∈ Finset.univ.erase j₀, |g j|
        ≤ ∑ _j ∈ Finset.univ.erase j₀, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => hb j)
    _ = ((Finset.univ.erase j₀).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((n - 1 : ℕ) : ℝ) := by rw [hcard]
    _ = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]

/-- `0 ≤ (n : ℝ) - 1` whenever `1 ≤ n`; small reusable helper. -/
private lemma zero_le_natCast_sub_one {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) ≤ (n : ℝ) - 1 := by
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Infinity-norm cap for the Aasen outer factor `L`.

`L` is unit lower triangular (`hdiag`, `hupper`), has first column `e₁`
(`hfirst`), and satisfies `|L i j| ≤ 1` (`hentry`). Then `‖L‖∞ ≤ n − 1`.

Each row of `L` has a guaranteed zero entry: row `0` vanishes off the diagonal
(so entry `(0,1)` is `0`, using `n ≥ 2`), and every later row has `L i 0 = 0`
by the first-column structure. `sum_abs_le_of_exists_zero` then bounds the row
sum by `n − 1`. -/
theorem aasen_L_infNorm_le
    (n : ℕ) (hn : 2 ≤ n) (L : Fin n → Fin n → ℝ)
    (hdiag  : ∀ i, L i i = 1)
    (hupper : ∀ i j, i.val < j.val → L i j = 0)
    (hfirst : ∀ i j, j.val = 0 → i.val ≠ 0 → L i j = 0)
    (hentry : ∀ i j, |L i j| ≤ 1) :
    infNorm L ≤ (n : ℝ) - 1 := by
  refine infNorm_le_of_row_sum_le L (fun i => ?_) (zero_le_natCast_sub_one (by omega))
  by_cases hi : i.val = 0
  · -- Row 0: entry (0,1) vanishes (0 < 1), available because n ≥ 2.
    refine sum_abs_le_of_exists_zero (by omega) _ (fun j => hentry i j)
      (⟨1, by omega⟩ : Fin n) ?_
    apply hupper
    show i.val < 1
    omega
  · -- Row i ≠ 0: entry (i,0) vanishes by the first-column structure.
    refine sum_abs_le_of_exists_zero (by omega) _ (fun j => hentry i j)
      (⟨0, by omega⟩ : Fin n) ?_
    exact hfirst i (⟨0, by omega⟩ : Fin n) rfl hi

/-- Infinity-norm cap for the transpose of the Aasen outer factor `L`.

`infNorm Lᵀ = max column sum of L`. Each column of `L` has a guaranteed zero
entry: column `0` vanishes below the diagonal (so entry `(1,0)` is `0`, using
`n ≥ 2`), and every later column `r` has `L 0 r = 0` since `0 < r`. Hence
`‖Lᵀ‖∞ ≤ n − 1`. -/
theorem aasen_LT_infNorm_le
    (n : ℕ) (hn : 2 ≤ n) (L : Fin n → Fin n → ℝ)
    (hdiag  : ∀ i, L i i = 1)
    (hupper : ∀ i j, i.val < j.val → L i j = 0)
    (hfirst : ∀ i j, j.val = 0 → i.val ≠ 0 → L i j = 0)
    (hentry : ∀ i j, |L i j| ≤ 1) :
    infNorm (fun r c => L c r) ≤ (n : ℝ) - 1 := by
  refine infNorm_le_of_row_sum_le (fun r c => L c r) (fun i => ?_)
    (zero_le_natCast_sub_one (by omega))
  by_cases hi : i.val = 0
  · -- Column 0: entry (1,0) vanishes by first-column structure (needs n ≥ 2).
    refine sum_abs_le_of_exists_zero (by omega) _ (fun c => hentry c i)
      (⟨1, by omega⟩ : Fin n) ?_
    refine hfirst (⟨1, by omega⟩ : Fin n) i hi ?_
    show (1 : ℕ) ≠ 0
    omega
  · -- Column i ≠ 0: entry (0,i) vanishes since 0 < i.
    refine sum_abs_le_of_exists_zero (by omega) _ (fun c => hentry c i)
      (⟨0, by omega⟩ : Fin n) ?_
    apply hupper
    show (0 : ℕ) < i.val
    omega

/-- **Structural product cap for the Aasen outer factor (Higham Thm 11.8).**

`‖L‖∞ · ‖Lᵀ‖∞ ≤ (n − 1)²`, proved from the factor structure alone. This is the
cap that the normwise endpoint
`higham11_8_aasen_relative_coeff_le_of_gamma_base_square_bounds` assumes on the
norms; here it is discharged. -/
theorem aasen_L_infNorm_mul_transpose_le_sq
    (n : ℕ) (hn : 2 ≤ n) (L : Fin n → Fin n → ℝ)
    (hdiag  : ∀ i, L i i = 1)
    (hupper : ∀ i j, i.val < j.val → L i j = 0)
    (hfirst : ∀ i j, j.val = 0 → i.val ≠ 0 → L i j = 0)
    (hentry : ∀ i j, |L i j| ≤ 1) :
    infNorm L * infNorm (fun r c => L c r) ≤ ((n : ℝ) - 1) ^ 2 := by
  have h1 := aasen_L_infNorm_le n hn L hdiag hupper hfirst hentry
  have h2 := aasen_LT_infNorm_le n hn L hdiag hupper hfirst hentry
  have hnn : (0 : ℝ) ≤ (n : ℝ) - 1 := zero_le_natCast_sub_one (by omega)
  calc
    infNorm L * infNorm (fun r c => L c r)
        ≤ ((n : ℝ) - 1) * ((n : ℝ) - 1) :=
          mul_le_mul h1 h2 (infNorm_nonneg _) hnn
    _ = ((n : ℝ) - 1) ^ 2 := by ring

/-- The structural product cap in the exact `((n − 1 : ℕ) : ℝ) ^ 2` shape used
by the `hprod_base` input of
`higham11_8_aasen_relative_coeff_le_of_gamma_base_square_bounds`. Under `2 ≤ n`
the Nat-subtraction cast agrees with `(n : ℝ) - 1`, so this is the same bound. -/
theorem aasen_L_infNorm_mul_transpose_le_natCast_sq
    (n : ℕ) (hn : 2 ≤ n) (L : Fin n → Fin n → ℝ)
    (hdiag  : ∀ i, L i i = 1)
    (hupper : ∀ i j, i.val < j.val → L i j = 0)
    (hfirst : ∀ i j, j.val = 0 → i.val ≠ 0 → L i j = 0)
    (hentry : ∀ i j, |L i j| ≤ 1) :
    infNorm L * infNorm (fun r c => L c r) ≤ ((n - 1 : ℕ) : ℝ) ^ 2 := by
  have h := aasen_L_infNorm_mul_transpose_le_sq n hn L hdiag hupper hfirst hentry
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast]
  exact h

end NumStability.Ch11Closure.AasenNorm
