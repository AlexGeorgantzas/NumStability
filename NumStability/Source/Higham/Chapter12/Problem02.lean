-- Source/Higham/Chapter12/Problem02.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Problem 12.2 and its Appendix A solution (printed pp. 242 and 556).

import NumStability.Source.Higham.Chapter12.IterativeRefinement
import NumStability.Analysis.HighamChapter7

/-!
# Higham Chapter 12, Problem 12.2

Exact finite forms of Problem 12.2 and its Appendix A solution, connecting one
fixed-precision refinement step to a forward-error multiple of
`cond(A,x) * u` without replacing finite gamma factors by asymptotic notation.
-/

namespace NumStability

open scoped BigOperators

/-- **Problem 12.2, Appendix A: exact two-step recurrence.**

Iterating a componentwise one-step bound
`|e_{k+1}| ≤ G |e_k| + g` twice, starting from `|e₀| = |x|`, gives

`|e₂| ≤ G² |x| + (G + I) g`.

This is the exact finite identity/inequality behind the Appendix's first
display.  It deliberately precedes all of the source's `≈` and `≲`
estimates for `G`, so none of those asymptotic comparisons is encoded as an
equality. -/
theorem higham12_problem12_2_two_step_recurrence {n : ℕ}
    (G : Fin n → Fin n → ℝ) (g x e₁ e₂ : Fin n → ℝ)
    (hG : ∀ i j, 0 ≤ G i j)
    (hstep₁ : ∀ i,
      |e₁ i| ≤ ∑ j : Fin n, G i j * |x j| + g i)
    (hstep₂ : ∀ i,
      |e₂ i| ≤ ∑ j : Fin n, G i j * |e₁ j| + g i) :
    ∀ i,
      |e₂ i| ≤
        (∑ j : Fin n, G i j * (∑ k : Fin n, G j k * |x k|)) +
          ((∑ j : Fin n, G i j * g j) + g i) := by
  intro i
  calc
    |e₂ i| ≤ ∑ j : Fin n, G i j * |e₁ j| + g i := hstep₂ i
    _ ≤ ∑ j : Fin n, G i j *
          ((∑ k : Fin n, G j k * |x k|) + g j) + g i := by
        have hsum :
            (∑ j : Fin n, G i j * |e₁ j|) ≤
              ∑ j : Fin n, G i j *
                ((∑ k : Fin n, G j k * |x k|) + g j) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hstep₁ j) (hG i j)
        linarith
    _ = (∑ j : Fin n, G i j * (∑ k : Fin n, G j k * |x k|)) +
          ((∑ j : Fin n, G i j * g j) + g i) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        ring

/-- **Problem 12.2: exact forward-error transfer from the post-refinement
componentwise residual certificate.**

The exact companions to Theorem 12.4 in this repository produce the honest
certificate

`|b - A y| ≤ epsilon (|A| |y| + |b|)`.

Oettli--Prager turns it into a componentwise perturbation certificate, and
Theorem 7.4 then gives the relative forward bound below.  Since `b = A x`, the
Chapter 7 data condition with `f = |b|` is at most twice `cond(A,x)`.  Thus this
theorem retains the exact `+ |b|` qualification while still proving the
substantive claim requested by Problem 12.2. -/
theorem higham12_problem12_2_forward_error_of_residual_certificate
    {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hres : ∀ i,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        epsilon * ((∑ j : Fin n, |A i j| * |y j|) + |b i|))
    (hsmall : epsilon * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - y i) / infNormVec x ≤
      (2 * epsilon) / (1 - epsilon * condSkeel n hn A A_inv) *
        ch7SkeelCondAtSolutionInf n hn A A_inv x := by
  have hOP : ∀ i,
      |residualVec n A y b i| ≤
        epsilon *
          ((∑ j : Fin n, |A i j| * |y j|) + |b i|) := by
    intro i
    simpa [residualVec] using hres i
  obtain ⟨DeltaA, Deltab, hDeltaA, hDeltab, hPerturbed⟩ :=
    oettli_prager_sufficient n A y b (fun i j => |A i j|)
      (fun i => |b i|) epsilon hepsilon
      (fun _ _ => abs_nonneg _) (fun _ => abs_nonneg _) hOP
  have hM : ∀ i,
      ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|) ≤
        condSkeel n hn A A_inv := by
    intro i
    unfold condSkeel
    exact Finset.le_sup'
      (fun i' => ∑ j : Fin n, |A_inv i' j| * ∑ k : Fin n, |A j k|)
      (Finset.mem_univ i)
  have hmain := componentwise_forward_error_exact_relative_infNorm
    n hn A A_inv x y b DeltaA Deltab (fun i j => |A i j|)
      (fun i => |b i|) epsilon hepsilon hDeltaA hDeltab
      (fun _ _ => abs_nonneg _) (fun _ => abs_nonneg _)
      hInv hAx hPerturbed (condSkeel n hn A A_inv) hM hsmall hx
  have hdata_eq :
      ch7CondEFAtSolutionInf n hn A_inv (fun i j => |A i j|)
          (fun i => |b i|) x =
        ch7ComponentwiseDataCondAtSolutionInf n hn A A_inv x := by
    unfold ch7ComponentwiseDataCondAtSolutionInf
    congr 2
    funext i
    simp only [matMulVec, hAx i]
  have hdata_le :
      ch7CondEFAtSolutionInf n hn A_inv (fun i j => |A i j|)
          (fun i => |b i|) x ≤
        2 * ch7SkeelCondAtSolutionInf n hn A A_inv x := by
    rw [hdata_eq]
    exact ch7ComponentwiseDataCondAtSolutionInf_le_two_mul_skeelCondAtSolutionInf
      n hn A A_inv x hx
  have hden : 0 < 1 - epsilon * condSkeel n hn A A_inv := by linarith
  have hcoef : 0 ≤ epsilon / (1 - epsilon * condSkeel n hn A A_inv) :=
    div_nonneg hepsilon hden.le
  calc
    infNormVec (fun i => x i - y i) / infNormVec x
        ≤ epsilon / (1 - epsilon * condSkeel n hn A A_inv) *
            ch7CondEFAtSolutionInf n hn A_inv (fun i j => |A i j|)
              (fun i => |b i|) x := by
          simpa [ch7CondEFAtSolutionInf] using hmain
    _ ≤ epsilon / (1 - epsilon * condSkeel n hn A A_inv) *
          (2 * ch7SkeelCondAtSolutionInf n hn A A_inv x) :=
        mul_le_mul_of_nonneg_left hdata_le hcoef
    _ = (2 * epsilon) / (1 - epsilon * condSkeel n hn A A_inv) *
          ch7SkeelCondAtSolutionInf n hn A A_inv x := by ring

/-- **Problem 12.2, source-facing `multiple of cond(A,x) * u` endpoint.**

Specializing the exact post-refinement certificate to
`epsilon = 2 * gamma_(n+1)` gives an explicit finite multiplier of
`cond(A,x) * u`.  The multiplier keeps all higher-order terms and the
small-denominator guard; no `gamma ≈ (n+1)u` replacement is made. -/
theorem higham12_problem12_2_forward_error_multiple_cond_u
    {n : ℕ} (hn : 0 < n) (fp : FPModel)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hres : ∀ i,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        (2 * gamma fp (n + 1)) *
          ((∑ j : Fin n, |A i j| * |y j|) + |b i|))
    (hn1 : gammaValid fp (n + 1))
    (hsmall : (2 * gamma fp (n + 1)) * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    let C : ℝ :=
      (4 * (n + 1 : ℕ)) /
        ((1 - (n + 1 : ℕ) * fp.u) *
          (1 - (2 * gamma fp (n + 1)) * condSkeel n hn A A_inv))
    0 ≤ C ∧
      infNormVec (fun i => x i - y i) / infNormVec x ≤
        C * ch7SkeelCondAtSolutionInf n hn A A_inv x * fp.u := by
  intro C
  have hgamma : 0 ≤ 2 * gamma fp (n + 1) :=
    mul_nonneg (by norm_num) (gamma_nonneg fp hn1)
  have hmain := higham12_problem12_2_forward_error_of_residual_certificate
    hn A A_inv x y b (2 * gamma fp (n + 1)) hgamma hInv hAx hres hsmall hx
  have hden₁ : 0 < 1 - (n + 1 : ℕ) * fp.u := by
    unfold gammaValid at hn1
    exact sub_pos.mpr hn1
  have hden₂ :
      0 < 1 - (2 * gamma fp (n + 1)) * condSkeel n hn A A_inv := by
    linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨hC, ?_⟩
  have hcoefficient :
      (2 * (2 * gamma fp (n + 1))) /
          (1 - (2 * gamma fp (n + 1)) * condSkeel n hn A A_inv) =
        C * fp.u := by
    dsimp [C]
    unfold gamma
    field_simp [ne_of_gt hden₁, ne_of_gt hden₂]
    ring
  rw [hcoefficient] at hmain
  nlinarith

/-- Existential phrasing of Problem 12.2's requested conclusion. -/
theorem higham12_problem12_2_exists_forward_error_multiple_cond_u
    {n : ℕ} (hn : 0 < n) (fp : FPModel)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hres : ∀ i,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        (2 * gamma fp (n + 1)) *
          ((∑ j : Fin n, |A i j| * |y j|) + |b i|))
    (hn1 : gammaValid fp (n + 1))
    (hsmall : (2 * gamma fp (n + 1)) * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    ∃ C : ℝ, 0 ≤ C ∧
      infNormVec (fun i => x i - y i) / infNormVec x ≤
        C * ch7SkeelCondAtSolutionInf n hn A A_inv x * fp.u := by
  let C : ℝ :=
    (4 * (n + 1 : ℕ)) /
      ((1 - (n + 1 : ℕ) * fp.u) *
        (1 - (2 * gamma fp (n + 1)) * condSkeel n hn A A_inv))
  refine ⟨C, ?_⟩
  exact higham12_problem12_2_forward_error_multiple_cond_u
    hn fp A A_inv x y b hInv hAx hres hn1 hsmall hx

/-- End-to-end composition with the exact solver-derived companion to
Theorem 12.4.  Unlike the certificate-level theorem above, this result derives
the post-refinement residual bound from the correction solver, conventional
residual, rounded update, and Neumann-contraction hypotheses used by
`higham12_4_from_solver`. -/
theorem higham12_problem12_2_from_solver_exists_forward_error_multiple_cond_u
    (n : ℕ) (hn : 0 < n) (fp : FPModel)
    (A Ainv : Fin n → Fin n → ℝ)
    (x x₀ d_hat r_hat b r f₂ y : Fin n → ℝ)
    (DeltaA_solve : Fin n → Fin n → ℝ)
    (hAinv_nn : ∀ i j : Fin n, 0 ≤ Ainv i j)
    (hAinv : ∀ (v w : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i : Fin n, |v i| ≤ ∑ j : Fin n, Ainv i j * |w j|)
    (hInv : IsLeftInverse n A Ainv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i : Fin n, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + DeltaA_solve i j) * d_hat j = r_hat i)
    (hDeltaA : ∀ i j : Fin n,
      |DeltaA_solve i j| ≤ gamma fp (3 * n) * |A i j|)
    (hresidual : ∀ i : Fin n, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j : Fin n,
      |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n)) (hu_lt : fp.u < 1)
    (c : ℝ) (hc_lt : c < 1)
    (hrow : ∀ i : Fin n,
      ∑ k : Fin n, gamma fp (3 * n) *
        (∑ j : Fin n, |A i j| * Ainv j k) ≤ c)
    (m : ℝ) (hm_pos : 0 < m)
    (ht_lb : ∀ i : Fin n,
      m ≤ ∑ j : Fin n, |A i j| * |y j| + |b i|)
    (rho : ℝ) (hrho_nn : 0 ≤ rho)
    (hcond : (infNormVec (fun i => ∑ k : Fin n,
        (∑ j : Fin n, |A i j| * Ainv j k) * |r_hat k|)) /
          (1 - c) ≤ rho * m)
    (hrho_cond : (gamma fp (n + 1) + fp.u) +
        ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
          (1 - fp.u) * (gamma fp (3 * n) + fp.u)) * rho ≤
        (1 - fp.u) * (2 * gamma fp (n + 1)))
    (hsmall : (2 * gamma fp (n + 1)) * condSkeel n hn A Ainv < 1)
    (hx : 0 < infNormVec x) :
    ∃ C : ℝ, 0 ≤ C ∧
      infNormVec (fun i => x i - y i) / infNormVec x ≤
        C * ch7SkeelCondAtSolutionInf n hn A Ainv x * fp.u := by
  have hpost := higham12_4_from_solver n hn fp A Ainv x₀ d_hat r_hat b r
    f₂ y DeltaA_solve hAinv_nn hAinv hr hy hsolve hDeltaA hresidual hf₂
    hn1 hn3 hu_lt c hc_lt hrow m hm_pos ht_lb rho hrho_nn hcond hrho_cond
  exact higham12_problem12_2_exists_forward_error_multiple_cond_u
    hn fp A Ainv x y b hInv hAx hpost hn1 hsmall hx

end NumStability
