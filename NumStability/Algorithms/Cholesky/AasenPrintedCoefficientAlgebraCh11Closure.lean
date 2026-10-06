/-
Algorithms/Cholesky/AasenPrintedCoefficientAlgebraCh11Closure.lean

Exact scalar folds used in Higham Theorem 11.8.  They keep the source
operation counts visible:

* the computed Aasen factorization contributes `gamma_(n+3)`;
* the two outer unit-triangular solves contribute `gamma_(n-1)` each;
* the adjacent-pivot tridiagonal factor/solve contributes `gamma_6`.

The resulting two componentwise coefficients are exactly the printed
`gamma_(3*n+1)` and `gamma_(2*n+4)`.  The final infinity-norm fold uses the
direct operational middle-envelope constant six and reaches
`gamma_(15*n+25)`.
-/
import NumStability.Algorithms.Cholesky.AasenDirectTridiagGEPPSolveCh11Closure

namespace NumStability.Ch11Closure.AasenPrinted

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.AasenDirectGEPP

/-- The factorization coefficient and both outer-solve perturbations fold to
the first printed Theorem 11.8 coefficient. -/
theorem factor_outer_coeff_le_gamma_3n1 (fp : FPModel) (n : ℕ)
    (hn : 2 ≤ n) (hval : gammaValid fp (3 * n + 1)) :
    gamma fp (n + 3) +
        (2 * gamma fp (n - 1) + (gamma fp (n - 1)) ^ 2) ≤
      gamma fp (3 * n + 1) := by
  have h2pred : gammaValid fp (2 * (n - 1)) :=
    gammaValid_mono fp (by omega) hval
  have hfactor : gammaValid fp (n + 3) :=
    gammaValid_mono fp (by omega) hval
  have houter :
      2 * gamma fp (n - 1) + (gamma fp (n - 1)) ^ 2 ≤
        gamma fp (2 * (n - 1)) :=
    higham11_8_two_gamma_plus_sq_le_gamma_2n fp (n - 1) h2pred
  have hsum :
      gamma fp (n + 3) + gamma fp (2 * (n - 1)) +
          gamma fp (n + 3) * gamma fp (2 * (n - 1)) ≤
        gamma fp ((n + 3) + 2 * (n - 1)) :=
    gamma_sum_le fp (n + 3) (2 * (n - 1)) (by
      simpa [show (n + 3) + 2 * (n - 1) = 3 * n + 1 by omega] using hval)
  have hcross :
      0 ≤ gamma fp (n + 3) * gamma fp (2 * (n - 1)) :=
    mul_nonneg (gamma_nonneg fp hfactor) (gamma_nonneg fp h2pred)
  calc
    gamma fp (n + 3) +
          (2 * gamma fp (n - 1) + (gamma fp (n - 1)) ^ 2)
        ≤ gamma fp (n + 3) + gamma fp (2 * (n - 1)) :=
          add_le_add (le_refl _) houter
    _ ≤ gamma fp (n + 3) + gamma fp (2 * (n - 1)) +
          gamma fp (n + 3) * gamma fp (2 * (n - 1)) := by linarith
    _ ≤ gamma fp ((n + 3) + 2 * (n - 1)) := hsum
    _ = gamma fp (3 * n + 1) := by congr 1; omega

/-- The two outer-solve multipliers surrounding the operational middle
`gamma_6` perturbation fold to the second printed coefficient. -/
theorem outer_middle_coeff_le_gamma_2n4 (fp : FPModel) (n : ℕ)
    (hn : 2 ≤ n) (hval : gammaValid fp (2 * n + 4)) :
    (1 + 2 * gamma fp (n - 1) + (gamma fp (n - 1)) ^ 2) *
        gamma fp 6 ≤ gamma fp (2 * n + 4) := by
  have h :=
    higham11_8_one_plus_two_gamma_plus_sq_mul_gamma_k_le_gamma_2nk
      fp (n - 1) 6 (by
        simpa [show 2 * (n - 1) + 6 = 2 * n + 4 by omega] using hval)
  simpa [show 2 * (n - 1) + 6 = 2 * n + 4 by omega] using h

/-- With the direct operational envelope bound
`||P^T |M| |U|||_inf ≤ 6 ||T||_inf`, the two printed componentwise
coefficients fit inside the printed normwise `gamma_(15*n+25)` radius. -/
theorem printed_norm_coeff_le_gamma_15n25 (fp : FPModel) (n : ℕ)
    (hval : gammaValid fp (15 * n + 25)) :
    gamma fp (3 * n + 1) + 6 * gamma fp (2 * n + 4) ≤
      gamma fp (15 * n + 25) := by
  have hmidValid : gammaValid fp (6 * (2 * n + 4)) :=
    gammaValid_mono fp (by omega) hval
  have hfirstValid : gammaValid fp (3 * n + 1) :=
    gammaValid_mono fp (by omega) hval
  have hmid : 6 * gamma fp (2 * n + 4) ≤
      gamma fp (6 * (2 * n + 4)) :=
    gamma_nsmul_le fp 6 (2 * n + 4) (by omega) hmidValid
  have hsum :
      gamma fp (3 * n + 1) + gamma fp (6 * (2 * n + 4)) +
          gamma fp (3 * n + 1) * gamma fp (6 * (2 * n + 4)) ≤
        gamma fp ((3 * n + 1) + 6 * (2 * n + 4)) :=
    gamma_sum_le fp (3 * n + 1) (6 * (2 * n + 4)) (by
      simpa [show (3 * n + 1) + 6 * (2 * n + 4) = 15 * n + 25 by omega]
        using hval)
  have hcross :
      0 ≤ gamma fp (3 * n + 1) * gamma fp (6 * (2 * n + 4)) :=
    mul_nonneg (gamma_nonneg fp hfirstValid) (gamma_nonneg fp hmidValid)
  calc
    gamma fp (3 * n + 1) + 6 * gamma fp (2 * n + 4)
        ≤ gamma fp (3 * n + 1) + gamma fp (6 * (2 * n + 4)) :=
          add_le_add (le_refl _) hmid
    _ ≤ gamma fp (3 * n + 1) + gamma fp (6 * (2 * n + 4)) +
          gamma fp (3 * n + 1) * gamma fp (6 * (2 * n + 4)) := by linarith
    _ ≤ gamma fp ((3 * n + 1) + 6 * (2 * n + 4)) := hsum
    _ = gamma fp (15 * n + 25) := by congr 1; omega

/-- Entrywise algebraic assembly of the exact printed two-term perturbation
budget.  This theorem intentionally receives only the already-produced
middle envelope `B`; operational modules supply that envelope and its source
equation separately. -/
theorem factor_plus_chain_le_printed (fp : FPModel) (n : ℕ)
    (hn : 2 ≤ n) (hval : gammaValid fp (15 * n + 25))
    (L T U B : Fin n → Fin n → ℝ)
    (hB : ∀ p q : Fin n, 0 ≤ B p q) (i j : Fin n) :
    gamma fp (n + 3) *
          (∑ p : Fin n, ∑ q : Fin n,
            |L i p| * |T p q| * |U q j|) +
        higham11_15_aasenChainDeltaABound n (gamma fp (n - 1))
          (fun p q => gamma fp 6 * B p q) L T U i j ≤
      gamma fp (3 * n + 1) *
          (∑ p : Fin n, ∑ q : Fin n,
            |L i p| * |T p q| * |U q j|) +
        gamma fp (2 * n + 4) *
          (∑ p : Fin n, ∑ q : Fin n,
            |L i p| * B p q * |U q j|) := by
  let ST : ℝ := ∑ p : Fin n, ∑ q : Fin n,
    |L i p| * |T p q| * |U q j|
  let SB : ℝ := ∑ p : Fin n, ∑ q : Fin n,
    |L i p| * B p q * |U q j|
  let cT : ℝ := 2 * gamma fp (n - 1) + (gamma fp (n - 1)) ^ 2
  let cB : ℝ := 1 + 2 * gamma fp (n - 1) + (gamma fp (n - 1)) ^ 2
  have hST : 0 ≤ ST := by
    dsimp [ST]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by positivity
  have hSB : 0 ≤ SB := by
    dsimp [SB]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (hB p q)) (abs_nonneg _)
  have hchain :
      higham11_15_aasenChainDeltaABound n (gamma fp (n - 1))
          (fun p q => gamma fp 6 * B p q) L T U i j =
        cT * ST + (cB * gamma fp 6) * SB := by
    unfold higham11_15_aasenChainDeltaABound
    calc
      (∑ p : Fin n, ∑ q : Fin n,
          ((2 * gamma fp (n - 1) + gamma fp (n - 1) ^ 2) *
              |L i p| * |T p q| * |U q j| +
            (1 + 2 * gamma fp (n - 1) + gamma fp (n - 1) ^ 2) *
              |L i p| * (gamma fp 6 * B p q) * |U q j|)) =
          ∑ p : Fin n,
            (cT * (∑ q : Fin n, |L i p| * |T p q| * |U q j|) +
              (cB * gamma fp 6) *
                (∑ q : Fin n, |L i p| * B p q * |U q j|)) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro q _
              simp only [cT]
              ring
            · apply Finset.sum_congr rfl
              intro q _
              simp only [cB]
              ring
      _ = cT * ST + (cB * gamma fp 6) * SB := by
             rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hfirstValid : gammaValid fp (3 * n + 1) :=
    gammaValid_mono fp (by omega) hval
  have hmiddleValid : gammaValid fp (2 * n + 4) :=
    gammaValid_mono fp (by omega) hval
  have hfirst : gamma fp (n + 3) + cT ≤ gamma fp (3 * n + 1) := by
    simpa [cT] using factor_outer_coeff_le_gamma_3n1 fp n hn hfirstValid
  have hmiddle : cB * gamma fp 6 ≤ gamma fp (2 * n + 4) := by
    simpa [cB] using outer_middle_coeff_le_gamma_2n4 fp n hn hmiddleValid
  change gamma fp (n + 3) * ST +
      higham11_15_aasenChainDeltaABound n (gamma fp (n - 1))
        (fun p q => gamma fp 6 * B p q) L T U i j ≤
    gamma fp (3 * n + 1) * ST + gamma fp (2 * n + 4) * SB
  rw [hchain]
  calc
    gamma fp (n + 3) * ST + (cT * ST + (cB * gamma fp 6) * SB)
        = (gamma fp (n + 3) + cT) * ST + (cB * gamma fp 6) * SB := by ring
    _ ≤ gamma fp (3 * n + 1) * ST + gamma fp (2 * n + 4) * SB :=
      add_le_add
        (mul_le_mul_of_nonneg_right hfirst hST)
        (mul_le_mul_of_nonneg_right hmiddle hSB)

end NumStability.Ch11Closure.AasenPrinted
