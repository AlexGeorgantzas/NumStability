/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Computed solve for the literal rounded Bunch--Kaufman execution

This module composes the actual forward substitution, an equation-(11.5)
block-diagonal middle-solve certificate, and the actual back substitution for
the concrete flat factors produced by `Higham11RoundedBunchKaufmanExecution`.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal
import NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure

open scoped BigOperators

namespace NumStability

open Ch11Closure.Solve

namespace Higham11RoundedBunchKaufmanExecution

/-! ## Structural facts required by the two outer triangular solves -/

theorem flatL_diag {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    forall i : Fin n, exec.flatL i i = 1 := by
  induction exec with
  | nil => intro I; exact Fin.elim0 I
  | noAction A hA hbranch tail ih =>
      intro I
      refine Fin.cases (by rfl) (fun i => ?_) I
      exact ih i
  | case1 A hA hbranch tail ih =>
      intro I
      refine Fin.cases (by rfl) (fun i => ?_) I
      exact ih i
  | case2 A hA hbranch tail ih =>
      intro I
      refine Fin.cases (by rfl) (fun i => ?_) I
      exact ih i
  | case3 A hA hbranch tail ih =>
      intro I
      refine Fin.cases (by rfl) (fun i => ?_) I
      exact ih i
  | case4 A hA hbranch hsecond tail ih =>
      intro I
      refine Fin.cases (by rfl) (fun K => ?_) I
      refine Fin.cases (by rfl) (fun i => ?_) K
      exact ih i
  | case4Breakdown A hA hbranch hsecond =>
      intro I
      simp [flatL]

theorem flatL_lower {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    forall i j : Fin n, i.val < j.val -> exec.flatL i j = 0 := by
  induction exec with
  | nil => intro I; exact Fin.elim0 I
  | noAction A hA hbranch tail ih =>
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun _ => ?_) J
        · intro h; omega
        · intro _; rfl
      · refine Fin.cases ?_ (fun j => ?_) J
        · intro h
          exact absurd h (by rw [Fin.val_zero]; omega)
        · intro h
          exact ih i j (by simp only [Fin.val_succ] at h ⊢; omega)
  | case1 A hA hbranch tail ih =>
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun _ => ?_) J
        · intro h; omega
        · intro _; rfl
      · refine Fin.cases ?_ (fun j => ?_) J
        · intro h
          exact absurd h (by rw [Fin.val_zero]; omega)
        · intro h
          exact ih i j (by simp only [Fin.val_succ] at h ⊢; omega)
  | case2 A hA hbranch tail ih =>
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun _ => ?_) J
        · intro h; omega
        · intro _; rfl
      · refine Fin.cases ?_ (fun j => ?_) J
        · intro h
          exact absurd h (by rw [Fin.val_zero]; omega)
        · intro h
          exact ih i j (by simp only [Fin.val_succ] at h ⊢; omega)
  | case3 A hA hbranch tail ih =>
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun _ => ?_) J
        · intro h; omega
        · intro _; rfl
      · refine Fin.cases ?_ (fun j => ?_) J
        · intro h
          exact absurd h (by rw [Fin.val_zero]; omega)
        · intro h
          exact ih i j (by simp only [Fin.val_succ] at h ⊢; omega)
  | case4 A hA hbranch hsecond tail ih =>
      intro I J
      refine Fin.cases ?_ (fun K => ?_) I
      · refine Fin.cases ?_ (fun L => ?_) J
        · intro h; omega
        · refine Fin.cases ?_ (fun _ => ?_) L
          · intro _; rfl
          · intro _; rfl
      · refine Fin.cases ?_ (fun i => ?_) K
        · refine Fin.cases ?_ (fun L => ?_) J
          · intro h
            exact absurd h (by rw [Fin.val_zero]; omega)
          · refine Fin.cases ?_ (fun _ => ?_) L
            · intro h; omega
            · intro _; rfl
        · refine Fin.cases ?_ (fun L => ?_) J
          · intro h
            exact absurd h (by rw [Fin.val_zero]; omega)
          · refine Fin.cases ?_ (fun j => ?_) L
            · intro h
              exact absurd h (by simp only [Fin.val_succ, Fin.val_zero]; omega)
            · intro h
              exact ih i j (by simp only [Fin.val_succ] at h ⊢; omega)
  | case4Breakdown A hA hbranch hsecond =>
      intro I J h
      simp [flatL, show I ≠ J by omega]

/-! ## The actual computed solve (Theorem 11.3, second conclusion) -/

/-- Solve-side finite-precision coefficient contributed by the two rounded
outer triangular solves and the equation-(11.5) middle block solve. -/
noncomputable def solveResidualCoefficient (fp : FPModel) (n : Nat)
    (gammaMid : Real) : Real :=
  (2 * gamma fp n + gamma fp n ^ 2) +
    (1 + 2 * gamma fp n + gamma fp n ^ 2) * gammaMid

/-- **Theorem 11.3, computed-solve half for the literal rounded execution.**

`b` is expressed in final pivot coordinates.  The outer vectors are the
actual `fl_forwardSub` and `fl_backSub` results.  The only solve-specific input
is the ordinary equation-(11.5) certificate for the block-diagonal middle
solve: `(Dhat + DeltaD) what = fl_forwardSub Lhat b` and
`|DeltaD| <= gammaMid |Dhat|`.

The resulting perturbation contains both the already-proved factorization
error and the fully derived solve-chain error; it contains no factorization
target or residual premise. -/
theorem computedSolve_backward_error
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (b : Fin n -> Real)
    (hvaln : gammaValid fp n) (gammaMid : Real)
    (hgammaMid : 0 <= gammaMid)
    (w_hat : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real)
    (hDeltaD : forall i j : Fin n,
      |DeltaD i j| <= gammaMid * |exec.flatD i j|)
    (hmiddle : forall p : Fin n,
      (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
        fl_forwardSub fp n exec.flatL b p) :
    exists DeltaA2 : Fin n -> Fin n -> Real,
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              (|exec.permutedInput i j| + exec.flatAbsProduct i j) +
            solveResidualCoefficient fp n gammaMid *
              exec.flatAbsProduct i j) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (exec.permutedInput i j + DeltaA2 i j) *
              fl_backSub fp n (fun r c => exec.flatL c r) w_hat j = b i) := by
  let L : Fin n -> Fin n -> Real := exec.flatL
  let D : Fin n -> Fin n -> Real := exec.flatD
  let U : Fin n -> Fin n -> Real := fun r c => exec.flatL c r
  let A_fact : Fin n -> Fin n -> Real := exec.flatProduct
  let A_source : Fin n -> Fin n -> Real := exec.permutedInput
  let BT : Fin n -> Fin n -> Real := fun i j => gammaMid * |D i j|
  let B_solve : Fin n -> Fin n -> Real :=
    higham11_15_aasenChainDeltaABound n (gamma fp n) BT L D U
  let B_factor : Fin n -> Fin n -> Real := fun i j =>
    exec.finiteResidualCoefficient *
      (|exec.permutedInput i j| + exec.flatAbsProduct i j)
  have hLdiag : forall i : Fin n, L i i ≠ 0 := fun i => by
    show exec.flatL i i ≠ 0
    rw [flatL_diag exec i]
    exact one_ne_zero
  have hLlower : forall i j : Fin n, i.val < j.val -> L i j = 0 :=
    fun i j h => flatL_lower exec i j h
  have hUdiag : forall i : Fin n, U i i ≠ 0 := fun i => by
    show exec.flatL i i ≠ 0
    rw [flatL_diag exec i]
    exact one_ne_zero
  have hUupper : forall i j : Fin n, j.val < i.val -> U i j = 0 :=
    fun i j h => flatL_lower exec j i h
  obtain ⟨DeltaL, hDeltaL, hforward⟩ :=
    forwardSub_backward_error fp n L b hLdiag hLlower hvaln
  obtain ⟨DeltaU, hDeltaU, hback⟩ :=
    backSub_backward_error fp n U w_hat hUdiag hUupper hvaln
  have hBT : forall p q : Fin n, 0 <= BT p q := fun p q =>
    mul_nonneg hgammaMid (abs_nonneg _)
  have hchainBound : forall i j : Fin n,
      |higham11_15_aasenChainDeltaA n L D U
          DeltaL DeltaD DeltaU i j| <= B_solve i j :=
    higham11_15_aasenChainDeltaA_abs_bound_gamma
      n L D U DeltaL DeltaD DeltaU BT (gamma fp n)
        (gamma_nonneg fp hvaln) hBT hDeltaL (by
          intro i j
          simpa [BT, D] using hDeltaD i j) hDeltaU
  obtain ⟨DeltaS, hDeltaS, hchainEquation⟩ :=
    higham11_15_aasen_chain_source_backward_error_of_components
      n A_fact L D U DeltaL DeltaD DeltaU
      b (fl_forwardSub fp n L b) w_hat (fl_backSub fp n U w_hat)
      B_solve (by intro i j; rfl) hforward (by
        intro p
        simpa [D, L] using hmiddle p) hback hchainBound
  have hfactor : forall i j : Fin n,
      |A_fact i j - A_source i j| <= B_factor i j := by
    intro i j
    simpa [A_fact, A_source, B_factor, backwardError] using
      backwardError_abs_le_finiteResidualCoefficient
        hval3 hval9 hsmall9 exec hcompleted i j
  obtain ⟨DeltaA2, hDeltaA2, hsourceEquation⟩ :=
    higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
      n A_source A_fact DeltaS B_factor B_solve b
      (fl_backSub fp n U w_hat) hfactor hDeltaS hchainEquation
  refine ⟨DeltaA2, ?_, ?_⟩
  · intro i j
    have h := hDeltaA2 i j
    have hsolveEq :
        B_solve i j = solveResidualCoefficient fp n gammaMid *
          exec.flatAbsProduct i j := by
      dsimp [B_solve, BT, U, L, D]
      rw [aasenChainDeltaABound_eq_coeff_mul_productEntry]
      rfl
    rw [hsolveEq] at h
    simpa [B_factor] using h
  · simpa [A_source, U] using hsourceEquation

/-! ## Exact transport back to the original source coordinates -/

noncomputable def unpermutedMatrix {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (M : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => M (exec.permutation.symm i) (exec.permutation.symm j)

noncomputable def unpermutedVector {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (x : Fin n -> Real) : Fin n -> Real :=
  fun i => x (exec.permutation.symm i)

noncomputable def sourceFlatAbsProduct {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    Fin n -> Fin n -> Real :=
  exec.unpermutedMatrix exec.flatAbsProduct

theorem unpermuted_solve_equation {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (b x : Fin n -> Real) (Delta : Fin n -> Fin n -> Real)
    (hpivot : forall i : Fin n,
      ∑ j : Fin n,
        (exec.permutedInput i j + Delta i j) * x j =
          b (exec.permutation i)) :
    forall i : Fin n,
      ∑ j : Fin n,
        (A i j + exec.unpermutedMatrix Delta i j) *
          exec.unpermutedVector x j = b i := by
  intro i
  let f : Fin n -> Real := fun j =>
    (exec.permutedInput (exec.permutation.symm i) j +
      Delta (exec.permutation.symm i) j) * x j
  calc
    (∑ j : Fin n,
        (A i j + exec.unpermutedMatrix Delta i j) *
          exec.unpermutedVector x j) =
        ∑ j : Fin n, f (exec.permutation.symm j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [f, unpermutedMatrix, unpermutedVector, permutedInput]
    _ = ∑ j : Fin n, f j := by
      simpa using (Equiv.sum_comp exec.permutation.symm f)
    _ = b i := by
      simpa [f] using hpivot (exec.permutation.symm i)

/-- Source-coordinate form of the second conclusion of Theorem 11.3.
The right-hand side and returned solution are in the original ordering, and
the perturbation is explicitly unpermuted from the pivot-coordinate solve. -/
theorem computedSolve_backward_error_source
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (b : Fin n -> Real)
    (hvaln : gammaValid fp n) (gammaMid : Real)
    (hgammaMid : 0 <= gammaMid)
    (w_hat : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real)
    (hDeltaD : forall i j : Fin n,
      |DeltaD i j| <= gammaMid * |exec.flatD i j|)
    (hmiddle : forall p : Fin n,
      (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
        fl_forwardSub fp n exec.flatL
          (fun i => b (exec.permutation i)) p) :
    exists DeltaA2 : Fin n -> Fin n -> Real,
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              (|A i j| + exec.sourceFlatAbsProduct i j) +
            solveResidualCoefficient fp n gammaMid *
              exec.sourceFlatAbsProduct i j) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  let bPivot : Fin n -> Real := fun i => b (exec.permutation i)
  obtain ⟨DeltaPivot, hDeltaPivot, hsolvePivot⟩ :=
    computedSolve_backward_error hval3 hval9 hsmall9 exec hcompleted
      bPivot hvaln gammaMid hgammaMid w_hat DeltaD hDeltaD (by
        intro p
        simpa [bPivot] using hmiddle p)
  refine ⟨exec.unpermutedMatrix DeltaPivot, ?_, ?_⟩
  · intro i j
    simpa [unpermutedMatrix, sourceFlatAbsProduct, permutedInput] using
      hDeltaPivot (exec.permutation.symm i) (exec.permutation.symm j)
  · apply unpermuted_solve_equation exec b
      (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) DeltaPivot
    intro i
    simpa [bPivot] using hsolvePivot i

theorem solveResidualCoefficient_nonneg
    (hvaln : gammaValid fp n) (hgammaMid : 0 <= gammaMid) :
    0 <= solveResidualCoefficient fp n gammaMid := by
  have hg : 0 <= gamma fp n := gamma_nonneg fp hvaln
  unfold solveResidualCoefficient
  positivity

/-- **Theorem 11.4, honest finite-`u` normwise form for the literal rounded
execution.**  Higham cites, rather than proves in Chapter 11, the
Bunch--Kaufman product-growth estimate
`|Lhat||Dhat||Lhat^T| <= 36 n rho_n ||A||_M`; `hgrowth` is exactly that cited
input, now applied to the concrete factors assembled by the executor.

The conclusion is the actual computed solve, with all higher-order terms kept
in `finiteResidualCoefficient` and `solveResidualCoefficient`. -/
theorem computedSolve_backward_error_normwise_of_growth
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (b : Fin n -> Real)
    (hvaln : gammaValid fp n) (gammaMid rho_n Amax : Real)
    (hgammaMid : 0 <= gammaMid) (hrho : 0 <= rho_n)
    (hAmax : forall i j : Fin n, |exec.permutedInput i j| <= Amax)
    (hAmax0 : 0 <= Amax)
    (hgrowth : forall i j : Fin n,
      exec.flatAbsProduct i j <= 36 * (n : Real) * rho_n * Amax)
    (w_hat : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real)
    (hDeltaD : forall i j : Fin n,
      |DeltaD i j| <= gammaMid * |exec.flatD i j|)
    (hmiddle : forall p : Fin n,
      (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
        fl_forwardSub fp n exec.flatL b p) :
    exists DeltaA2 : Fin n -> Fin n -> Real,
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 36 * (n : Real) * rho_n) * Amax) +
            solveResidualCoefficient fp n gammaMid *
              (36 * (n : Real) * rho_n * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (exec.permutedInput i j + DeltaA2 i j) *
              fl_backSub fp n (fun r c => exec.flatL c r) w_hat j = b i) := by
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ := computedSolve_backward_error
    hval3 hval9 hsmall9 exec hcompleted b hvaln gammaMid hgammaMid
      w_hat DeltaD hDeltaD hmiddle
  refine ⟨DeltaA2, ?_, hsolve⟩
  have hC : 0 <= exec.finiteResidualCoefficient :=
    finiteResidualCoefficient_nonneg hval3 exec
  have hS : 0 <= solveResidualCoefficient fp n gammaMid :=
    solveResidualCoefficient_nonneg hvaln hgammaMid
  intro i j
  have hfactorInput :
      |exec.permutedInput i j| + exec.flatAbsProduct i j <=
        (1 + 36 * (n : Real) * rho_n) * Amax := by
    calc
      |exec.permutedInput i j| + exec.flatAbsProduct i j <=
          Amax + 36 * (n : Real) * rho_n * Amax :=
        add_le_add (hAmax i j) (hgrowth i j)
      _ = (1 + 36 * (n : Real) * rho_n) * Amax := by ring
  exact le_trans (hDeltaA2 i j)
    (add_le_add
      (mul_le_mul_of_nonneg_left hfactorInput hC)
      (mul_le_mul_of_nonneg_left (hgrowth i j) hS))

/-- Source-coordinate normwise corollary of Theorem 11.4.  The cited growth
bound is expressed after exact unpermutation, so both `Amax` and the solve
equation refer to the original matrix and right-hand side. -/
theorem computedSolve_backward_error_normwise_of_growth_source
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (b : Fin n -> Real)
    (hvaln : gammaValid fp n) (gammaMid rho_n Amax : Real)
    (hgammaMid : 0 <= gammaMid)
    (hAmax : forall i j : Fin n, |A i j| <= Amax)
    (hgrowth : forall i j : Fin n,
      exec.sourceFlatAbsProduct i j <=
        36 * (n : Real) * rho_n * Amax)
    (w_hat : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real)
    (hDeltaD : forall i j : Fin n,
      |DeltaD i j| <= gammaMid * |exec.flatD i j|)
    (hmiddle : forall p : Fin n,
      (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
        fl_forwardSub fp n exec.flatL
          (fun i => b (exec.permutation i)) p) :
    exists DeltaA2 : Fin n -> Fin n -> Real,
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 36 * (n : Real) * rho_n) * Amax) +
            solveResidualCoefficient fp n gammaMid *
              (36 * (n : Real) * rho_n * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ := computedSolve_backward_error_source
    hval3 hval9 hsmall9 exec hcompleted b hvaln gammaMid hgammaMid
      w_hat DeltaD hDeltaD hmiddle
  refine ⟨DeltaA2, ?_, hsolve⟩
  have hC : 0 <= exec.finiteResidualCoefficient :=
    finiteResidualCoefficient_nonneg hval3 exec
  have hS : 0 <= solveResidualCoefficient fp n gammaMid :=
    solveResidualCoefficient_nonneg hvaln hgammaMid
  intro i j
  have hfactorInput :
      |A i j| + exec.sourceFlatAbsProduct i j <=
        (1 + 36 * (n : Real) * rho_n) * Amax := by
    calc
      |A i j| + exec.sourceFlatAbsProduct i j <=
          Amax + 36 * (n : Real) * rho_n * Amax :=
        add_le_add (hAmax i j) (hgrowth i j)
      _ = (1 + 36 * (n : Real) * rho_n) * Amax := by ring
  exact le_trans (hDeltaA2 i j)
    (add_le_add
      (mul_le_mul_of_nonneg_left hfactorInput hC)
      (mul_le_mul_of_nonneg_left (hgrowth i j) hS))

end Higham11RoundedBunchKaufmanExecution

end NumStability
