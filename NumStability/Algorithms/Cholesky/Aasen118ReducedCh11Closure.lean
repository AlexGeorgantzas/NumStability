-- Algorithms/Cholesky/Aasen118ReducedCh11Closure.lean
--
-- Reduced-assumption assembly of Higham, 2nd ed., Chapter 11, Theorem 11.8
-- (Aasen's method, normwise backward error `‖ΔA‖∞ ≤ (n−1)² γ_{15n+25} ‖T̂‖∞`).
--
-- The repository already carries a full tower of 11.8 wrappers culminating in
-- `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds`
-- (`HighamChapter11.lean`), which derives the componentwise `ΔA`, the printed
-- constant, and the `(A+ΔA)x̂=b` conclusion, but *consumes* seven infinity-norm
-- caps (`hL_norm`, `hLT_norm`, `hLhat_norm`, `hLhatT_norm`, `hT_norm`,
-- `hBT_norm`, `hmiddle_norm`) plus the printed coefficient obligation `hcoeff`
-- as hypotheses.
--
-- This file discharges the four *outer-factor* norm caps and the printed
-- coefficient obligation, **using only the honest partial-pivoting multiplier
-- bounds** `|L i j| ≤ 1` (exact factor) and `|L̂ i j| ≤ 1` (computed factor),
-- via the structural cap `‖L‖∞ = ‖Lᵀ‖∞ ≤ n − 1` proved in
-- `AasenFactorNormCh11Closure`.
--
-- Crucially, this avoids the `(1+γ)²` inflation that forces the existing
-- top-level `AasenSpec_identity_..._endpoint` theorems to assume the *unnatural*
-- inverse entry bound `|L i j| ≤ 1/(1+γ)`.  The solve-side product cap
-- `κL̂·κL̂ᵀ ≤ (n−1)²` is obtained from `‖L̂‖∞ ≤ n−1` **independently** (the
-- computed Aasen multipliers are themselves bounded by `1` under partial
-- pivoting), rather than by inflating the exact-factor cap by `(1+γ)²`.
--
-- The middle-solve cap `hmiddle_norm` is reduced to a tridiagonal LU
-- factor-product bound `‖M̂‖∞·‖Û‖∞ ≤ κmidLU·‖T̂‖∞` (lemma B, `κmidLU ≤ 1`).
--
-- What REMAINS assumed after this reduction (the honest residual foundation):
--   * `h20`         : Chapter 9 eq. (9.20) tridiagonal LU perturbation model for
--                     the computed middle factor `T̂` (cited Ch9 result).
--   * `hLhat_entry` : computed outer-factor relative accuracy
--                     `|L̂ − L| ≤ γ_n |L|` (derivable elsewhere from the Aasen
--                     recurrence + the per-column rounding-closure budget).
--   * `hThat`, `hT_norm`, `hBT_norm` : the accuracy of the computed middle
--                     factor `T̂` — **the large remaining gap**: nothing in the
--                     repository computes `T̂` in floating point, so `|T̂ − T|`
--                     cannot yet be bounded.
--   * `hmiddle_factors` : lemma B, the tridiagonal middle LU product bound.
--   * structural specs for `L̂`, `L_T̂`, `U_T̂` (algorithm-shape hypotheses).

import NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure
import NumStability.Algorithms.Cholesky.AasenFactorNormCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.Aasen118Reduced

open NumStability
open NumStability.Ch11Closure.AasenNorm

/-- **Reduced-assumption Aasen normwise backward error (Higham Thm 11.8).**

From an identity-permutation `AasenSpec` (exact `A = L T Lᵀ`, `L` unit lower
triangular with first column `e₁`), the honest partial-pivoting multiplier
bounds `|L i j| ≤ 1` and `|L̂ i j| ≤ 1`, and the computed-factor structural
shape, this discharges the four outer-factor infinity-norm caps and the printed
`(n−1)²γ_{15n+25}` coefficient obligation of
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds`,
using `‖L‖∞, ‖Lᵀ‖∞, ‖L̂‖∞, ‖L̂ᵀ‖∞ ≤ n − 1` (all four **independently**, so no
`(1+γ)²` inflation).  The middle-solve cap is reduced to the lemma-B tridiagonal
LU product bound `hmiddle_factors`.

The remaining hypotheses (`h20`, `hLhat_entry`, `hThat`, `hT_norm`, `hBT_norm`,
`hmiddle_factors`, and the `L̂/L_T̂/U_T̂` structural specs) constitute the honest
residual foundation; see the module header. -/
theorem higham11_8_aasen_normwise_backward_error_of_reduced
    (fp : FPModel) (n : ℕ) (hn : 2 ≤ n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n)
    (κT κBT κmidLU : ℝ)
    -- exact factorization + partial-pivoting multiplier bound for `L`
    (hspec : higham11_8_AasenSpec n A L T σ)
    (hσ : ∀ i : Fin n, σ i = i)
    (hval : gammaValid fp (15 * n + 25))
    (hL_entry : ∀ i j : Fin n, |L i j| ≤ 1)
    -- computed outer factor: unit lower triangular, first column `e₁`,
    -- multipliers bounded by `1` (the honest partial-pivoting guarantee)
    (hLhat_diag_one : ∀ i : Fin n, L_hat i i = 1)
    (hLhat_upper : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hLhat_first : ∀ i j : Fin n, j.val = 0 → i.val ≠ 0 → L_hat i j = 0)
    (hLhat_entry_le_one : ∀ i j : Fin n, |L_hat i j| ≤ 1)
    -- computed middle tridiagonal LU structural shape
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    -- === residual foundation (see module header) ===
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_entry : ∀ i j : Fin n,
      |L_hat i j - L i j| ≤ gamma fp n * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hκT_nonneg : 0 ≤ κT) (hκT_le_one : κT ≤ 1)
    (hκBT_nonneg : 0 ≤ κBT) (hκBT_le : κBT ≤ gamma fp n)
    (hκmidLU_nonneg : 0 ≤ κmidLU) (hκmidLU_le_one : κmidLU ≤ 1)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_factor L T
        (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat
        U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA)
        (gamma fp (15 * n + 25)) (infNorm T_hat) := by
  -- gamma-validity at the auxiliary radii
  have hn_pos : 0 < n := by omega
  have hnval : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have h2n : gammaValid fp (2 * n) := gammaValid_mono fp (by omega) hval
  have h3n : gammaValid fp (3 * n) := gammaValid_mono fp (by omega) hval
  have h6n : gammaValid fp (6 * n) := gammaValid_mono fp (by omega) hval
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hnval
  have hf_nonneg : 0 ≤ higham9_14_f (gamma fp n) :=
    higham9_14_f_nonneg hγn_nonneg
  -- cast `((n-1 : ℕ) : ℝ) = (n : ℝ) - 1`
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hnm1_nonneg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  have hsq_nonneg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
  -- the four outer-factor infinity-norm caps, from `|L i j| ≤ 1`/`|L̂ i j| ≤ 1`
  have hL_norm : infNorm L ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_L_infNorm_le n hn L hspec.L_diag hspec.L_upper_zero
      hspec.L_first_col hL_entry
  have hLT_norm : infNorm (fun r c => L c r) ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_LT_infNorm_le n hn L hspec.L_diag hspec.L_upper_zero
      hspec.L_first_col hL_entry
  have hLhat_norm : infNorm L_hat ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_L_infNorm_le n hn L_hat hLhat_diag_one hLhat_upper
      hLhat_first hLhat_entry_le_one
  have hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_LT_infNorm_le n hn L_hat hLhat_diag_one hLhat_upper
      hLhat_first hLhat_entry_le_one
  -- the exact product `A = L T Lᵀ`
  have hprod :
      ∀ i j : Fin n,
        (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j :=
    higham11_8_AasenSpec_product_eq_of_identity_perm n A L T σ hspec hσ
  -- lemma B ⇒ middle-solve budget cap, with `κmid = f(γ_n)·κmidLU`
  have hκmid_nonneg :
      (0 : ℝ) ≤ higham9_14_f (gamma fp n) * κmidLU :=
    mul_nonneg hf_nonneg hκmidLU_nonneg
  have hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        (higham9_14_f (gamma fp n) * κmidLU) * infNorm T_hat :=
    higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
      fp n hn_pos L_T_hat U_T_hat T_hat κmidLU hnval hmiddle_factors
  -- gamma-share absorptions
  have h2 : 2 * gamma fp n + (gamma fp n) ^ 2 ≤ gamma fp (2 * n) :=
    higham11_8_two_gamma_plus_sq_le_gamma_2n fp n h2n
  have h3 :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp n ≤
        gamma fp (3 * n) :=
    higham11_8_one_plus_two_gamma_plus_sq_mul_gamma_le_gamma_3n fp n h3n
  have h6 :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * higham9_14_f (gamma fp n) ≤
        gamma fp (6 * n) :=
    higham11_8_one_plus_two_gamma_plus_sq_mul_higham9_14_f_gamma_le_gamma_6n
      fp n h6n
  have hparts :
      gamma fp (2 * n) + gamma fp (3 * n) + gamma fp (2 * n) +
          gamma fp (6 * n) ≤ gamma fp (15 * n + 25) :=
    higham11_8_gamma_2n_plus_3n_plus_2n_plus_6n_le_gamma_15n25 fp n hval
  -- discharge the printed coefficient obligation with the independent
  -- product caps `κL·κLT = κL̂·κL̂ᵀ = (n−1)²`
  have hcoeff :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((n - 1 : ℕ) : ℝ) * κT * ((n - 1 : ℕ) : ℝ)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((n - 1 : ℕ) : ℝ) * κBT * ((n - 1 : ℕ) : ℝ)) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((n - 1 : ℕ) : ℝ) * (higham9_14_f (gamma fp n) * κmidLU) *
            ((n - 1 : ℕ) : ℝ)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (15 * n + 25) := by
    refine
      higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_bounds
        n (gamma fp n) (gamma fp n) (gamma fp (15 * n + 25))
        ((n - 1 : ℕ) : ℝ) ((n - 1 : ℕ) : ℝ) ((n - 1 : ℕ) : ℝ)
        ((n - 1 : ℕ) : ℝ) κT κBT (higham9_14_f (gamma fp n) * κmidLU)
        (((n - 1 : ℕ) : ℝ) ^ 2) (((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp n)
        (((n - 1 : ℕ) : ℝ) ^ 2)
        (((n - 1 : ℕ) : ℝ) ^ 2 * higham9_14_f (gamma fp n))
        (gamma fp (2 * n)) (gamma fp (3 * n)) (gamma fp (2 * n))
        (gamma fp (6 * n)) hγn_nonneg hγn_nonneg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        hparts
    · -- hρFT : κL·κT·κLT ≤ (n−1)²
      nlinarith [mul_nonneg hsq_nonneg (by linarith : (0 : ℝ) ≤ 1 - κT)]
    · -- hρFB : κL·κBT·κLT ≤ (n−1)²·γ_n
      nlinarith [mul_nonneg hsq_nonneg (by linarith : (0 : ℝ) ≤ gamma fp n - κBT)]
    · -- hρST : κL̂·κL̂ᵀ ≤ (n−1)²
      nlinarith [hsq_nonneg]
    · -- hρSB : κL̂·(f(γ_n)·κmidLU)·κL̂ᵀ ≤ (n−1)²·f(γ_n)
      nlinarith [mul_nonneg hsq_nonneg
        (mul_nonneg hf_nonneg (by linarith : (0 : ℝ) ≤ 1 - κmidLU))]
    · -- hFT
      calc
        (2 * gamma fp n + (gamma fp n) ^ 2) * ((n - 1 : ℕ) : ℝ) ^ 2
            = ((n - 1 : ℕ) : ℝ) ^ 2 *
                (2 * gamma fp n + (gamma fp n) ^ 2) := by ring
        _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (2 * n) :=
              mul_le_mul_of_nonneg_left h2 hsq_nonneg
    · -- hFB
      calc
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
              (((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp n)
            = ((n - 1 : ℕ) : ℝ) ^ 2 *
                ((1 + 2 * gamma fp n + (gamma fp n) ^ 2) * gamma fp n) := by
              ring
        _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (3 * n) :=
              mul_le_mul_of_nonneg_left h3 hsq_nonneg
    · -- hST
      calc
        (2 * gamma fp n + (gamma fp n) ^ 2) * ((n - 1 : ℕ) : ℝ) ^ 2
            = ((n - 1 : ℕ) : ℝ) ^ 2 *
                (2 * gamma fp n + (gamma fp n) ^ 2) := by ring
        _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (2 * n) :=
              mul_le_mul_of_nonneg_left h2 hsq_nonneg
    · -- hSB
      calc
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
              (((n - 1 : ℕ) : ℝ) ^ 2 * higham9_14_f (gamma fp n))
            = ((n - 1 : ℕ) : ℝ) ^ 2 *
                ((1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
                  higham9_14_f (gamma fp n)) := by ring
        _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (6 * n) :=
              mul_le_mul_of_nonneg_left h6 hsq_nonneg
  -- assemble the printed endpoint
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      (gamma fp n) (gamma fp (15 * n + 25))
      ((n - 1 : ℕ) : ℝ) ((n - 1 : ℕ) : ℝ) ((n - 1 : ℕ) : ℝ)
      ((n - 1 : ℕ) : ℝ) κT κBT (higham9_14_f (gamma fp n) * κmidLU)
      hγn_nonneg hnm1_nonneg hnm1_nonneg hκT_nonneg hκBT_nonneg hκmid_nonneg
      hBT_factor h20
      (fun i => by rw [hLhat_diag_one i]; exact one_ne_zero)
      hLhat_upper hT_L_diag hT_U_diag hT_L_lower hT_U_upper hnval hprod
      hLhat_entry hThat hL_norm hLT_norm hLhat_norm hLhatT_norm hT_norm
      hBT_norm hmiddle_norm hcoeff

end NumStability.Ch11Closure.Aasen118Reduced
