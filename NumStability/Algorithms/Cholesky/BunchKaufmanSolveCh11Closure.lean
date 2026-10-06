/-
Chapter 11 closure: **Theorem 11.4** (Bunch–Kaufman partial pivoting, normwise
backward stability of the linear-system solve).

Higham, Theorem 11.4:  let `A ∈ ℝⁿˣⁿ` be symmetric and let `x̂` be the computed
solution of `A x = b` obtained by block LDLᵀ factorization with the
**Bunch–Kaufman** partial pivoting strategy, where linear systems involving the
`2×2` pivots are solved by GEPP or by use of the explicit inverse.  Then

    `(A + ΔA) x̂ = b`,   `‖ΔA‖_M ≤ p(n) ρₙ u ‖A‖_M + O(u²)`,

with `p` a **quadratic** and `ρₙ` the growth factor.

Structure of the proof (what is DERIVED vs. what is Higham's own cited input):

  * The block-LDLᵀ *factorization* backward error and the *solve*-side backward
    error are BOTH derived from the floating-point model in the companion
    module `BlockLDLTSolveBackwardCh11Closure`
    (`higham11_7_bunch_tridiagonal_solve_backward_error_normwise`, which is
    generic in the factor-norm coefficient `c₀`): the fl block-LDLᵀ factors
    `L̂ = flMixedL`, `D̂ = flMixedD`, forward/back substitution `fl_forwardSub` /
    `fl_backSub`, the three-substep collapse and the fold against the
    factorization residual are all carried out there with no new axioms and no
    `sorry`.

  * The step SPECIFIC to Bunch–Kaufman (as opposed to a general block LDLᵀ) is
    the growth control of the factor product.  Higham does not prove this in the
    chapter; he cites it — "it can be shown that for every `A` the matrix
    `|L||D||Lᵀ|` satisfies `‖ |L||D||Lᵀ| ‖_M ≤ 36 n ρₙ ‖A‖_M`" [608, 1997].
    We take exactly this — and only this — as the source hypothesis `hgrowth`,
    i.e. `c₀ := 36 n ρₙ`.  This is faithful to Higham: the same result is an
    external citation there.

  * The `2×2`-pivot solve done "by GEPP or by use of the explicit inverse" is
    Higham's stated equation-(11.5) middle solve, isolated as the single
    hypothesis `hmid`/`hΔD` (`|ΔD| ≤ γ_mid |D̂|`), exactly as in
    `BlockLDLTSolveBackwardCh11Closure`.

So the capstone below is NOT a `h : P ⊢ P` conditional-transfer interface: it
runs the actual fl solve and derives `(A + ΔA) x̂ = b` with the printed
`p(n) ρₙ u ‖A‖_M` shape, assuming only what Higham himself assumes/cites for
Theorem 11.4.

`higham11_4_bunch_kaufman_solve_backward_error_of_growth` states the fully
derived two-part componentwise bound (factorization envelope `ΔA₁`, total solve
envelope `ΔA₂`) with `c₀ = 36 n ρₙ`.

`higham11_4_bunch_kaufman_solve_backward_error_printed` collapses that, under the
standard smallness regime `n u ≤ 1/100` and `ρₙ ≥ 1`, to Higham's printed
single-perturbation form `(A + ΔA) x̂ = b`, `|ΔA i j| ≤ p(n) ρₙ u ‖A‖_M` with the
explicit quadratic `p(n) = 1100 n² + 20 n` — the `O(u²)` remainder being absorbed
into the (concrete, larger) coefficient, exactly as in the companion all-`1×1`
printed result.

Note on `A`:  the block-LDLᵀ factorization runs on the (already pivoted) matrix,
so `A` here is the permuted matrix `PAPᵀ`; the permutation is exact and transfers
the bound to the original system, as in Higham's statement.

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.BunchKaufman

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed

/-- The explicit **quadratic** `p(n) = 1100 n² + 20 n` appearing in the printed
Theorem 11.4 backward-error coefficient. -/
def higham11_4_qPoly (n : ℕ) : ℝ := 1100 * (n : ℝ) ^ 2 + 20 * (n : ℝ)

/-- **Theorem 11.4, fully derived form.**  Block-LDLᵀ with Bunch–Kaufman partial
pivoting, `c₀ = 36 n ρₙ` (Higham's cited [608] growth bound `hgrowth`).  The fl
factorization `L̂ D̂ L̂ᵀ = A + ΔA₁` and the fl solve `(A + ΔA₂) x̂ = b` are derived
via `higham11_7_bunch_tridiagonal_solve_backward_error_normwise`; the only source
hypotheses are Higham's cited factor-growth bound `hgrowth` and the (11.5) `2×2`
middle solve `hmid`/`hΔD`.

`|ΔA₁| ≤ p(n) u (1 + 36 n ρₙ) ‖A‖_M`,
`|ΔA₂| ≤ p(n) u (1 + 36 n ρₙ) ‖A‖_M
          + ((2γₙ + γₙ²) + (1 + 2γₙ + γₙ²) γ_mid) · 36 n ρₙ ‖A‖_M`. -/
theorem higham11_4_bunch_kaufman_solve_backward_error_of_growth
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvaln : gammaValid fp n)
    (ρ_n Amax cSolve cStage gammaMid : ℝ)
    (hρ0 : 0 ≤ ρ_n)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ Amax) (hAmax0 : 0 ≤ Amax)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hgammaMid : 0 ≤ gammaMid)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A)
    (hgrowth : ∀ i j : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j
        ≤ 36 * (n : ℝ) * ρ_n * Amax)
    (w_hat : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ)
    (hΔD : ∀ i j : Fin n, |ΔD i j| ≤ gammaMid * |flMixedD fp s A i j|)
    (hmid : ∀ p : Fin n,
      ∑ q : Fin n, (flMixedD fp s A p q + ΔD p q) * w_hat q
        = fl_forwardSub fp n (flMixedL fp s A) b p) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ pPoly n * fp.u * ((1 + 36 * (n : ℝ) * ρ_n) * Amax)) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ pPoly n * fp.u * ((1 + 36 * (n : ℝ) * ρ_n) * Amax)
          + ((2 * gamma fp n + gamma fp n ^ 2)
              + (1 + 2 * gamma fp n + gamma fp n ^ 2) * gammaMid)
            * (36 * (n : ℝ) * ρ_n * Amax)) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          (A i j + ΔA2 i j) * fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat j = b i) :=
  Solve.higham11_7_bunch_tridiagonal_solve_backward_error_normwise
    fp hval s A b hvaln Amax (36 * (n : ℝ) * ρ_n) cSolve cStage gammaMid
    hAmax hAmax0 (mul_nonneg (by positivity) hρ0) hcS0 hcS40 hcSt0 hcSt5 hgammaMid hsmall hp
    hgrowth w_hat ΔD hΔD hmid

set_option maxHeartbeats 1000000 in
/-- **Theorem 11.4, printed normwise form.**  Under the standard smallness
regime `n u ≤ 1/100`, the growth factor bound `ρₙ ≥ 1`, and the natural
`2×2`-solve accuracy `γ_mid ≤ 2 n u` (the middle solve is at least as accurate as
the `n`-depth outer solves), the derived total backward error collapses to
Higham's printed shape:

    `(A + ΔA) x̂ = b`,   `|ΔA i j| ≤ p(n) ρₙ u ‖A‖_M`,   `p(n) = 1100 n² + 20 n`

a quadratic `p`, matching Theorem 11.4 (the `O(u²)` remainder absorbed into the
concrete coefficient). -/
theorem higham11_4_bunch_kaufman_solve_backward_error_printed
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (hn1 : 1 ≤ n) (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvaln : gammaValid fp n)
    (ρ_n Amax cSolve cStage gammaMid : ℝ)
    (hρ1 : 1 ≤ ρ_n)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ Amax) (hAmax0 : 0 ≤ Amax)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hgammaMid : 0 ≤ gammaMid) (hmidsmall : gammaMid ≤ 2 * ((n : ℝ) * fp.u))
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A)
    (hgrowth : ∀ i j : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j
        ≤ 36 * (n : ℝ) * ρ_n * Amax)
    (w_hat : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ)
    (hΔD : ∀ i j : Fin n, |ΔD i j| ≤ gammaMid * |flMixedD fp s A i j|)
    (hmid : ∀ p : Fin n,
      ∑ q : Fin n, (flMixedD fp s A p q + ΔD p q) * w_hat q
        = fl_forwardSub fp n (flMixedL fp s A) b p) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ higham11_4_qPoly n * ρ_n * fp.u * Amax) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          (A i j + ΔA i j) * fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat j = b i) := by
  obtain ⟨ΔA1, ΔA2, hΔA1, hΔA2, hfac, hsolve⟩ :=
    higham11_4_bunch_kaufman_solve_backward_error_of_growth fp hval s A b hvaln ρ_n Amax
      cSolve cStage gammaMid (by linarith) hAmax hAmax0 hcS0 hcS40 hcSt0 hcSt5 hgammaMid hsmall hp
      hgrowth w_hat ΔD hΔD hmid
  refine ⟨ΔA2, ?_, hsolve⟩
  intro i j
  refine le_trans (hΔA2 i j) ?_
  rw [show pPoly n = 20 * (n : ℝ) from rfl,
      show higham11_4_qPoly n = 1100 * (n : ℝ) ^ 2 + 20 * (n : ℝ) from rfl]
  -- record the scalar facts with raw terms first, then abbreviate uniformly
  have hU0 : 0 ≤ fp.u := fp.u_nonneg
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hg0 : 0 ≤ gamma fp n := gamma_nonneg fp hvaln
  have hg : gamma fp n ≤ 2 * ((n : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp n (by linarith)
  have hm : gammaMid ≤ 2 * ((n : ℝ) * fp.u) := hmidsmall
  set N : ℝ := (n : ℝ) with hNdef
  set U : ℝ := fp.u with hUdef
  set R : ℝ := ρ_n with hRdef
  set M : ℝ := Amax with hMdef
  set g : ℝ := gamma fp n with hgdef
  set m : ℝ := gammaMid with hmdef
  -- basic nonnegativities / smallness
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hR1 : (1 : ℝ) ≤ R := hρ1
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hM0 : (0 : ℝ) ≤ M := hAmax0
  have hm0 : (0 : ℝ) ≤ m := hgammaMid
  have hNU : N * U ≤ 1 / 100 := hsmall
  have hNU0 : (0 : ℝ) ≤ N * U := mul_nonneg hN0 hU0
  -- piecewise bounds building `S := (2g+g²)+(1+2g+g²)m ≤ 9 N U`
  have h4t2 : g ^ 2 ≤ 4 * (N * U) ^ 2 := by
    have := mul_le_mul hg hg hg0 (by linarith : (0 : ℝ) ≤ 2 * (N * U))
    nlinarith [this]
  have ht2 : 4 * (N * U) ^ 2 ≤ N * U := by nlinarith [hNU, hNU0, mul_nonneg hNU0 hNU0]
  have hg2 : g ^ 2 ≤ N * U := le_trans h4t2 ht2
  have hgm : g * m ≤ (2 * (N * U)) * (2 * (N * U)) :=
    mul_le_mul hg hm hm0 (by linarith)
  have h2gm : 2 * g * m ≤ N * U := by nlinarith [hgm, hNU, hNU0, mul_nonneg hNU0 hNU0]
  have hg2m : g ^ 2 * m ≤ N * U := by
    have h1 : g ^ 2 * m ≤ (N * U) * m := mul_le_mul_of_nonneg_right hg2 hm0
    have h2 : (N * U) * m ≤ (N * U) * (2 * (N * U)) := mul_le_mul_of_nonneg_left hm hNU0
    nlinarith [h1, h2, hNU, hNU0, mul_nonneg hNU0 hNU0]
  have hS : (2 * g + g ^ 2) + (1 + 2 * g + g ^ 2) * m ≤ 9 * (N * U) := by
    have hexp : (2 * g + g ^ 2) + (1 + 2 * g + g ^ 2) * m
        = 2 * g + g ^ 2 + m + 2 * g * m + g ^ 2 * m := by ring
    rw [hexp]; linarith [hg, hg2, hm, h2gm, hg2m]
  -- T2 = S · (36 N R M) ≤ 324 N² R U M  (no nlinarith on the degree-5 term: bound by hS then ring)
  have hpos36 : (0 : ℝ) ≤ 36 * N * R * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hN0) hR0) hM0
  have hT2 : ((2 * g + g ^ 2) + (1 + 2 * g + g ^ 2) * m) * (36 * N * R * M)
      ≤ 324 * N ^ 2 * R * U * M :=
    le_trans (mul_le_mul_of_nonneg_right hS hpos36) (le_of_eq (by ring))
  -- T1 = 20 N U (1 + 36 N R) M ≤ 740 N² R U M
  have hNR1 : (1 : ℝ) ≤ N * R := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ N - 1 by linarith) (show (0 : ℝ) ≤ R - 1 by linarith)]
  have hNle : N ≤ N ^ 2 * R := by
    nlinarith [mul_nonneg hN0 (show (0 : ℝ) ≤ N * R - 1 by linarith)]
  have hT1a : 20 * N * U * M ≤ 20 * N ^ 2 * R * U * M := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ N ^ 2 * R - N by linarith)
      (mul_nonneg hU0 hM0)]
  have hT1 : 20 * N * U * ((1 + 36 * N * R) * M) ≤ 740 * N ^ 2 * R * U * M := by
    have hexp : 20 * N * U * ((1 + 36 * N * R) * M)
        = 20 * N * U * M + 720 * N ^ 2 * R * U * M := by ring
    rw [hexp]; linarith [hT1a]
  -- combine (add the two proven bounds; final step is degree-4, cheap)
  have hNRUM : (0 : ℝ) ≤ N * R * U * M :=
    mul_nonneg (mul_nonneg (mul_nonneg hN0 hR0) hU0) hM0
  have hN2RUM : (0 : ℝ) ≤ N ^ 2 * R * U * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hR0) hU0) hM0
  refine le_trans (add_le_add hT1 hT2) ?_
  nlinarith [hNRUM, hN2RUM]

end NumStability.Ch11Closure.BunchKaufman
