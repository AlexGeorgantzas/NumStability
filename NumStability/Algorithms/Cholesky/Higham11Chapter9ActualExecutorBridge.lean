import NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure
import NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure

namespace NumStability

open scoped BigOperators

open Ch11Closure
open Ch11Closure.Mixed
open Ch11Closure.Solve

/-!
# Higham (11.7) for the actual block-LDLT solve executor

`Higham11Chapter9BridgeClosure` proves the exact denominator form of (11.7)
from a total componentwise backward error.  This module supplies the missing
implementation-facing handoff: the total perturbation is obtained from the
literal Theorem 11.3 mixed-pivot factorization and triangular-solve executor,
and its two proven budgets are combined into the source envelope.

No forward-error or target-shaped estimate is assumed.  The only solve-side
input retained by Theorem 11.3 is the sanctioned (11.5) backward-error
certificate for the block-diagonal middle solve.  The returned vector is
literally `fl_backSub` applied to that middle-solve result.
-/

/-- The coefficient multiplying `|L_hat||D_hat||L_hat^T|` in the solve-chain
part of the concrete Theorem 11.3 residual. -/
noncomputable def higham11_7_actualSolveCoefficient
    (fp : FPModel) (n : ℕ) (gammaMid : ℝ) : ℝ :=
  (2 * gamma fp n + gamma fp n ^ 2) +
    (1 + 2 * gamma fp n + gamma fp n ^ 2) * gammaMid

/-- A common componentwise backward-error coefficient for the factorization
and solve-chain parts of the concrete Theorem 11.3 result. -/
noncomputable def higham11_7_actualTotalEta
    (fp : FPModel) (n : ℕ) (gammaMid : ℝ) : ℝ :=
  pPoly n * fp.u + higham11_7_actualSolveCoefficient fp n gammaMid

/-- In unpermuted coordinates the product envelope used by the Chapter 11 / 9
bridge is definitionally the product entry used by the mixed block-LDLT
executor. -/
theorem higham11_7_permutedAbsLDLT_refl_eq_productEntry {n : ℕ}
    (L D : Fin n → Fin n → ℝ) (i j : Fin n) :
    higham11_7_permutedAbsLDLT (Equiv.refl (Fin n)) L D i j =
      higham11_4_bunchKaufmanProductEntry n L D i j := by
  rfl

/-- Product-conditioning transfer when the computed product factors
`A + Delta` and the actual factor residual has the total Theorem 11.3
envelope `eta * (|A| + |B| Cenv)`.

Compared with `higham11_7_perturbed_product_envelopeCondition_le`, the
additional `|A|` term is retained rather than silently discarded.  It creates
the linear correction
`eta * (condSkeel(A) + F) * cond(C)`, which becomes quadratic only after the
outer first-order factor in equation (11.7) is applied. -/
theorem higham11_7_perturbed_product_envelopeCondition_le_totalEnvelope
    {n : ℕ} (hn : 0 < n)
    (A A_inv B C C_inv Cenv Delta : Fin n → Fin n → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hprod : matMul n B C = fun i j => A i j + Delta i j)
    (hCright : IsRightInverse n C C_inv)
    (hCenv_nonneg : ∀ i j, 0 ≤ Cenv i j)
    (hDelta : ∀ i j, |Delta i j| ≤ eta *
      (|A i j| + matMul n (absMatrix n B) Cenv i j)) :
    higham11_7_envelopeCondition hn A_inv
        (matMul n (absMatrix n B) Cenv) ≤
      condSkeel n hn A A_inv *
          higham11_7_envelopeCondition hn C_inv Cenv +
        eta *
          (condSkeel n hn A A_inv +
            higham11_7_envelopeCondition hn A_inv
              (matMul n (absMatrix n B) Cenv)) *
          higham11_7_envelopeCondition hn C_inv Cenv := by
  let H := matMul n (absMatrix n B) Cenv
  let E : Fin n → Fin n → ℝ := fun i j => |A i j| + H i j
  let F := higham11_7_envelopeCondition hn A_inv H
  let Ccond := higham11_7_envelopeCondition hn C_inv Cenv
  have hEcond : higham11_7_envelopeCondition hn A_inv E ≤
      condSkeel n hn A A_inv + F := by
    unfold higham11_7_envelopeCondition
    apply Finset.sup'_le
    intro i _
    have hArow :
        (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|)) ≤
          condSkeel n hn A A_inv := by
      unfold condSkeel
      exact Finset.le_sup'
        (fun r : Fin n =>
          ∑ j : Fin n, |A_inv r j| * (∑ k : Fin n, |A j k|))
        (Finset.mem_univ i)
    have hHrow :
        (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k)) ≤ F := by
      exact higham11_7_envelopeCondition_row_le hn A_inv H i
    calc
      (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, E j k)) =
          (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|)) +
            ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, H j k) := by
              simp [E, Finset.sum_add_distrib, mul_add]
      _ ≤ condSkeel n hn A A_inv + F := add_le_add hArow hHrow
  have hprodBound := higham11_7_product_envelopeCondition_le hn
    (fun i j => A i j + Delta i j) A_inv B C C_inv Cenv
    hprod hCright hCenv_nonneg
  have hcondAdd := higham11_7_condSkeel_add_perturbation_le hn
    A A_inv Delta E eta heta (by simpa [E, H] using hDelta)
  have hcondRelax :
      condSkeel n hn (fun i j => A i j + Delta i j) A_inv ≤
        condSkeel n hn A A_inv + eta *
          (condSkeel n hn A A_inv + F) := by
    exact hcondAdd.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hEcond heta))
  have hCcond : 0 ≤ Ccond := by
    dsimp [Ccond]
    exact higham11_7_envelopeCondition_nonneg hn C_inv Cenv hCenv_nonneg
  calc
    higham11_7_envelopeCondition hn A_inv
        (matMul n (absMatrix n B) Cenv) ≤
        condSkeel n hn (fun i j => A i j + Delta i j) A_inv * Ccond := by
          simpa [H, F, Ccond] using hprodBound
    _ ≤ (condSkeel n hn A A_inv + eta *
          (condSkeel n hn A A_inv + F)) * Ccond :=
      mul_le_mul_of_nonneg_right hcondRelax hCcond
    _ = condSkeel n hn A A_inv * Ccond +
        eta * (condSkeel n hn A A_inv + F) * Ccond := by ring
    _ = condSkeel n hn A A_inv *
          higham11_7_envelopeCondition hn C_inv Cenv +
        eta *
          (condSkeel n hn A A_inv +
            higham11_7_envelopeCondition hn A_inv
              (matMul n (absMatrix n B) Cenv)) *
          higham11_7_envelopeCondition hn C_inv Cenv := by
      rfl

/-- **Implementation-facing equation (11.7).**

Run the concrete mixed-pivot block-LDLT factorization and its rounded outer
triangular solves.  Given the source (11.5) certificate for the middle block
solve, Theorem 11.3 derives a total perturbation for the literal result

`fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat`.

The total perturbation is relaxed, explicitly, to

`eta * (|A| + |L_hat||D_hat||L_hat^T|)`,

where `eta = p(n)u + ((2 gamma_n + gamma_n^2) +
(1 + 2 gamma_n + gamma_n^2) gammaMid)`.  The exact Chapter 9 perturbation
theorem then derives the displayed denominator bound. -/
theorem higham11_7_forwardError_of_actual_block_ldlt_executor
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (hn : 0 < n)
    (s : PivotSchedule n) (A A_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ) (hvaln : gammaValid fp n)
    (cSolve cStage gammaMid : ℝ)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hgammaMid : 0 ≤ gammaMid)
    (hsmallFactor : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A)
    (w_hat : Fin n → ℝ) (DeltaD : Fin n → Fin n → ℝ)
    (hDeltaD : ∀ i j : Fin n,
      |DeltaD i j| ≤ gammaMid * |flMixedD fp s A i j|)
    (hmiddle : ∀ p : Fin n,
      ∑ q : Fin n, (flMixedD fp s A p q + DeltaD p q) * w_hat q =
        fl_forwardSub fp n (flMixedL fp s A) b p)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hsmallForward :
      higham11_7_actualTotalEta fp n gammaMid *
        higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
          (flMixedL fp s A) (flMixedD fp s A) < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i -
        fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat i) /
        infNormVec x ≤
      higham11_7_actualTotalEta fp n gammaMid /
          (1 - higham11_7_actualTotalEta fp n gammaMid *
            higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
              (flMixedL fp s A) (flMixedD fp s A)) *
        (ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_factorCondition hn A_inv (Equiv.refl (Fin n))
            (flMixedL fp s A) (flMixedD fp s A)) := by
  obtain ⟨_, DeltaTotal, _, hDeltaTotal, _, hsolve⟩ :=
    higham11_3_block_ldlt_solve_backward_error fp hval s A b hvaln
      cSolve cStage gammaMid hcS0 hcS40 hcSt0 hcSt5 hgammaMid
      hsmallFactor hp w_hat DeltaD hDeltaD hmiddle
  let coeff : ℝ := higham11_7_actualSolveCoefficient fp n gammaMid
  let eta : ℝ := higham11_7_actualTotalEta fp n gammaMid
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hvaln
  have hpu : 0 ≤ pPoly n * fp.u := by
    exact mul_nonneg (by unfold pPoly; positivity) fp.u_nonneg
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff, higham11_7_actualSolveCoefficient]
    positivity
  have heta : 0 ≤ eta := by
    dsimp [eta, higham11_7_actualTotalEta]
    exact add_nonneg hpu hcoeff
  have hTotal : ∀ i j : Fin n,
      |DeltaTotal i j| ≤ eta *
        higham11_7_totalBackwardEnvelope A (Equiv.refl (Fin n))
          (flMixedL fp s A) (flMixedD fp s A) i j := by
    intro i j
    have hraw := hDeltaTotal i j
    rw [aasenChainDeltaABound_eq_coeff_mul_productEntry] at hraw
    have hA : 0 ≤ |A i j| := abs_nonneg _
    calc
      |DeltaTotal i j| ≤
          pPoly n * fp.u *
              (|A i j| + higham11_4_bunchKaufmanProductEntry n
                (flMixedL fp s A) (flMixedD fp s A) i j) +
            coeff * higham11_4_bunchKaufmanProductEntry n
              (flMixedL fp s A) (flMixedD fp s A) i j := by
                simpa [higham11_3_printedFirstOrderBound, coeff,
                  higham11_7_actualSolveCoefficient] using hraw
      _ ≤ pPoly n * fp.u *
              (|A i j| + higham11_4_bunchKaufmanProductEntry n
                (flMixedL fp s A) (flMixedD fp s A) i j) +
            coeff *
              (|A i j| + higham11_4_bunchKaufmanProductEntry n
                (flMixedL fp s A) (flMixedD fp s A) i j) := by
                exact add_le_add le_rfl
                  (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) hcoeff)
      _ = eta *
          higham11_7_totalBackwardEnvelope A (Equiv.refl (Fin n))
            (flMixedL fp s A) (flMixedD fp s A) i j := by
              rw [higham11_7_totalBackwardEnvelope,
                higham11_7_permutedAbsLDLT_refl_eq_productEntry]
              dsimp [eta, higham11_7_actualTotalEta]
              ring
  exact higham11_7_forwardError_exact_from_total_backward_error
    hn A A_inv (Equiv.refl (Fin n)) (flMixedL fp s A) (flMixedD fp s A)
    x (fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat) b
    DeltaTotal eta heta hTotal hInv hAx hsolve
    (by simpa [eta] using hsmallForward) hx

/-! ## Vanishing-roundoff family form

The fixed-precision theorem above is not, by itself, an interpretation of the
printed `O(u^2)`.  The next theorem indexes the actual executor by a genuine
roundoff family.  One coefficient and the two local condition bounds work for
every family member, so the quadratic remainder has one Landau constant.
-/

/-- **Actual-executor family form of (11.7).**

For every family index, the factors and the returned solution are the literal
outputs of the corresponding `FPModel`.  `heta_le` is a uniform linear bound
on the *derived* backward-error coefficient, while `hMbound` and `hDbound` are
ordinary local condition boundedness assumptions.  The conclusion is the
genuine family predicate `FamilyFirstOrderLe`, not a pointwise existential
remainder. -/
theorem higham11_7_forwardError_family_of_actual_block_ldlt_executor
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (fp : ι → FPModel) (hunit : ∀ t, (fp t).u = U.unit t)
    {n : ℕ} (hn : 0 < n)
    (s : PivotSchedule n) (A A_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hval : ∀ t, gammaValid (fp t) 3)
    (hvaln : ∀ t, gammaValid (fp t) n)
    (cSolve cStage : ℝ) (gammaMid : ι → ℝ)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hgammaMid : ∀ t, 0 ≤ gammaMid t)
    (hsmallFactor : ∀ t, (n : ℝ) * (fp t).u ≤ 1 / 100)
    (hpiv : ∀ t, FlMixedPivots (fp t) cSolve cStage s A)
    (w_hat : ι → Fin n → ℝ)
    (DeltaD : ι → Fin n → Fin n → ℝ)
    (hDeltaD : ∀ (t : ι) (i j : Fin n),
      |DeltaD t i j| ≤ gammaMid t * |flMixedD (fp t) s A i j|)
    (hmiddle : ∀ (t : ι) (p : Fin n),
      ∑ q : Fin n,
          (flMixedD (fp t) s A p q + DeltaD t p q) * w_hat t q =
        fl_forwardSub (fp t) n (flMixedL (fp t) s A) b p)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hx : 0 < infNormVec x)
    (pEta Mmax Dmax : ℝ)
    (hpEta : 0 ≤ pEta) (hMmax : 0 ≤ Mmax) (hDmax : 0 ≤ Dmax)
    (heta_le : ∀ t,
      pPoly n * U.unit t +
          higham11_7_actualSolveCoefficient (fp t) n (gammaMid t) ≤
        pEta * U.unit t)
    (hhalf : ∀ t,
      (pPoly n * U.unit t +
          higham11_7_actualSolveCoefficient (fp t) n (gammaMid t)) *
        higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
          (flMixedL (fp t) s A) (flMixedD (fp t) s A) ≤ (1 : ℝ) / 2)
    (hMbound : ∀ t,
      higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
          (flMixedL (fp t) s A) (flMixedD (fp t) s A) ≤ Mmax)
    (hDbound : ∀ t,
      ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_factorCondition hn A_inv (Equiv.refl (Fin n))
            (flMixedL (fp t) s A) (flMixedD (fp t) s A) ≤ Dmax) :
    FamilyFirstOrderLe l U.unit
      (fun t => pEta * U.unit t *
        (ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_factorCondition hn A_inv (Equiv.refl (Fin n))
            (flMixedL (fp t) s A) (flMixedD (fp t) s A)))
      (fun t => infNormVec (fun i => x i -
          fl_backSub (fp t) n (fun r c => flMixedL (fp t) s A c r)
            (w_hat t) i) / infNormVec x) := by
  let eta : ι → ℝ := fun t =>
    pPoly n * U.unit t +
      higham11_7_actualSolveCoefficient (fp t) n (gammaMid t)
  let M : ι → ℝ := fun t =>
    higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
      (flMixedL (fp t) s A) (flMixedD (fp t) s A)
  let D : ι → ℝ := fun t =>
    ch7SkeelCondAtSolutionInf n hn A A_inv x +
      higham11_7_factorCondition hn A_inv (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A)
  let err : ι → ℝ := fun t =>
    infNormVec (fun i => x i -
      fl_backSub (fp t) n (fun r c => flMixedL (fp t) s A c r)
        (w_hat t) i) / infNormVec x
  have heta : ∀ t, 0 ≤ eta t := by
    intro t
    dsimp [eta]
    exact add_nonneg
      (mul_nonneg (by unfold pPoly; positivity) (U.unit_nonneg t))
      (by
        unfold higham11_7_actualSolveCoefficient
        have hgamma : 0 ≤ gamma (fp t) n := gamma_nonneg (fp t) (hvaln t)
        exact add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hgamma) (sq_nonneg _))
          (mul_nonneg
            (add_nonneg
              (add_nonneg zero_le_one (mul_nonneg (by norm_num) hgamma))
              (sq_nonneg _))
            (hgammaMid t)))
  have hM : ∀ t, 0 ≤ M t := by
    intro t
    dsimp [M]
    exact higham11_7_totalGlobalCondition_nonneg hn A A_inv
      (Equiv.refl (Fin n)) (flMixedL (fp t) s A) (flMixedD (fp t) s A)
  have hfixed : 0 ≤ ch7SkeelCondAtSolutionInf n hn A A_inv x := by
    unfold ch7SkeelCondAtSolutionInf ch7CondEFAtSolutionInf
    exact div_nonneg
      (ch7ForwardBoundEF_nonneg n hn A_inv (fun i j => |A i j|)
        (fun _ => 0) x (fun _ _ => abs_nonneg _) (fun _ => le_rfl))
      (le_of_lt hx)
  have hD : ∀ t, 0 ≤ D t := by
    intro t
    dsimp [D]
    exact add_nonneg hfixed
      (higham11_7_factorCondition_nonneg hn A_inv (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A))
  have hexact : ∀ t,
      err t ≤ eta t / (1 - eta t * M t) * D t := by
    intro t
    have hsmallEta : eta t * M t < 1 := by
      exact lt_of_le_of_lt (by simpa [eta, M] using hhalf t)
        (by norm_num : (1 : ℝ) / 2 < 1)
    have hsmallActual :
        higham11_7_actualTotalEta (fp t) n (gammaMid t) *
          higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
            (flMixedL (fp t) s A) (flMixedD (fp t) s A) < 1 := by
      simpa [eta, M, higham11_7_actualTotalEta, hunit t] using hsmallEta
    have hactual := higham11_7_forwardError_of_actual_block_ldlt_executor
      (fp t) (hval t) hn s A A_inv x b (hvaln t)
      cSolve cStage (gammaMid t) hcS0 hcS40 hcSt0 hcSt5
      (hgammaMid t) (hsmallFactor t) (hpiv t) (w_hat t) (DeltaD t)
      (hDeltaD t) (hmiddle t) hInv hAx hsmallActual hx
    simpa [err, eta, M, D, higham11_7_actualTotalEta, hunit t] using hactual
  exact higham11_7_familyFirstOrderLe_of_denominator U
    pEta Mmax Dmax hpEta hMmax hDmax eta M D err heta hM hD
    (by simpa [eta] using heta_le) (by simpa [eta, M] using hhalf)
    (by simpa [M] using hMbound) (by simpa [D] using hDbound) hexact

/-- **Both displayed family lines of equation (11.7) for the actual
block-LDLT executor.**

The first line is supplied by
`higham11_7_forwardError_family_of_actual_block_ldlt_executor`.  For the
second, this theorem destructs the concrete Theorem 11.3 factorization
certificate at every family index and applies the total-envelope product
transfer proved above.  A right inverse of the literal factor
`D_hat L_hat^T` and uniform local bounds on its condition and the displayed
factor condition are regularity data; no forward-error or condition-product
target is assumed. -/
theorem higham11_7_forwardError_family_condition_product_of_actual_block_ldlt_executor
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (fp : ι → FPModel) (hunit : ∀ t, (fp t).u = U.unit t)
    {n : ℕ} (hn : 0 < n)
    (s : PivotSchedule n) (A A_inv : Fin n → Fin n → ℝ)
    (C_inv : ι → Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hval : ∀ t, gammaValid (fp t) 3)
    (hvaln : ∀ t, gammaValid (fp t) n)
    (cSolve cStage : ℝ) (gammaMid : ι → ℝ)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hgammaMid : ∀ t, 0 ≤ gammaMid t)
    (hsmallFactor : ∀ t, (n : ℝ) * (fp t).u ≤ 1 / 100)
    (hpiv : ∀ t, FlMixedPivots (fp t) cSolve cStage s A)
    (w_hat : ι → Fin n → ℝ)
    (DeltaD : ι → Fin n → Fin n → ℝ)
    (hDeltaD : ∀ (t : ι) (i j : Fin n),
      |DeltaD t i j| ≤ gammaMid t * |flMixedD (fp t) s A i j|)
    (hmiddle : ∀ (t : ι) (p : Fin n),
      ∑ q : Fin n,
          (flMixedD (fp t) s A p q + DeltaD t p q) * w_hat t q =
        fl_forwardSub (fp t) n (flMixedL (fp t) s A) b p)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hx : 0 < infNormVec x)
    (pEta Mmax Dmax Fmax Cmax : ℝ)
    (hpEta : 0 ≤ pEta) (hMmax : 0 ≤ Mmax) (hDmax : 0 ≤ Dmax)
    (hFmax : 0 ≤ Fmax) (hCmax : 0 ≤ Cmax)
    (heta_le : ∀ t,
      pPoly n * U.unit t +
          higham11_7_actualSolveCoefficient (fp t) n (gammaMid t) ≤
        pEta * U.unit t)
    (hhalf : ∀ t,
      (pPoly n * U.unit t +
          higham11_7_actualSolveCoefficient (fp t) n (gammaMid t)) *
        higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
          (flMixedL (fp t) s A) (flMixedD (fp t) s A) ≤ (1 : ℝ) / 2)
    (hMbound : ∀ t,
      higham11_7_totalGlobalCondition hn A A_inv (Equiv.refl (Fin n))
          (flMixedL (fp t) s A) (flMixedD (fp t) s A) ≤ Mmax)
    (hDbound : ∀ t,
      ch7SkeelCondAtSolutionInf n hn A A_inv x +
          higham11_7_factorCondition hn A_inv (Equiv.refl (Fin n))
            (flMixedL (fp t) s A) (flMixedD (fp t) s A) ≤ Dmax)
    (hCright : ∀ t, IsRightInverse n
      (higham11_7_permutedRightFactor (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A)) (C_inv t))
    (hFbound : ∀ t,
      higham11_7_factorCondition hn A_inv (Equiv.refl (Fin n))
          (flMixedL (fp t) s A) (flMixedD (fp t) s A) ≤ Fmax)
    (hCbound : ∀ t,
      higham11_7_envelopeCondition hn (C_inv t)
          (higham11_7_permutedRightEnvelope (Equiv.refl (Fin n))
            (flMixedL (fp t) s A) (flMixedD (fp t) s A)) ≤ Cmax) :
    FamilyFirstOrderLe l U.unit
      (fun t => (2 * pEta) * U.unit t * condSkeel n hn A A_inv *
        higham11_7_envelopeCondition hn (C_inv t)
          (higham11_7_permutedRightEnvelope (Equiv.refl (Fin n))
            (flMixedL (fp t) s A) (flMixedD (fp t) s A)))
      (fun t => infNormVec (fun i => x i -
          fl_backSub (fp t) n (fun r c => flMixedL (fp t) s A c r)
            (w_hat t) i) / infNormVec x) := by
  let fixed : ℝ := ch7SkeelCondAtSolutionInf n hn A A_inv x
  let F : ι → ℝ := fun t =>
    higham11_7_factorCondition hn A_inv (Equiv.refl (Fin n))
      (flMixedL (fp t) s A) (flMixedD (fp t) s A)
  let Ccond : ι → ℝ := fun t =>
    higham11_7_envelopeCondition hn (C_inv t)
      (higham11_7_permutedRightEnvelope (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A))
  let err : ι → ℝ := fun t =>
    infNormVec (fun i => x i -
      fl_backSub (fp t) n (fun r c => flMixedL (fp t) s A c r)
        (w_hat t) i) / infNormVec x
  have hfirstRaw :=
    higham11_7_forwardError_family_of_actual_block_ldlt_executor
      U fp hunit hn s A A_inv x b hval hvaln cSolve cStage gammaMid
      hcS0 hcS40 hcSt0 hcSt5 hgammaMid hsmallFactor hpiv w_hat DeltaD
      hDeltaD hmiddle hInv hAx hx pEta Mmax Dmax hpEta hMmax hDmax
      heta_le hhalf hMbound hDbound
  have hfirst : FamilyFirstOrderLe l U.unit
      (fun t => pEta * U.unit t * (fixed + F t)) err := by
    simpa [fixed, F, err] using hfirstRaw
  have hcondA : 0 ≤ condSkeel n hn A A_inv :=
    higham9_23_condSkeel_nonneg n hn A A_inv
  have hF : ∀ t, 0 ≤ F t := by
    intro t
    dsimp [F]
    exact higham11_7_factorCondition_nonneg hn A_inv (Equiv.refl (Fin n))
      (flMixedL (fp t) s A) (flMixedD (fp t) s A)
  have hC : ∀ t, 0 ≤ Ccond t := by
    intro t
    dsimp [Ccond]
    exact higham11_7_envelopeCondition_nonneg hn (C_inv t)
      (higham11_7_permutedRightEnvelope (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A))
      (fun i j => Finset.sum_nonneg fun q _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have htransfer : FamilyLinearRemainderLe l U.unit
      (fun t => condSkeel n hn A A_inv * Ccond t) F := by
    refine ⟨fun t =>
        pEta * (condSkeel n hn A A_inv + Fmax) * Cmax * U.unit t,
      ?_, ?_, ?_⟩
    · intro t
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hpEta (add_nonneg hcondA hFmax)) hCmax)
        (U.unit_nonneg t)
    · intro t
      obtain ⟨DeltaFactor, _, hFactor, _, hfactorEq, _⟩ :=
        higham11_3_block_ldlt_solve_backward_error
          (fp t) (hval t) s A b (hvaln t) cSolve cStage (gammaMid t)
          hcS0 hcS40 hcSt0 hcSt5 (hgammaMid t) (hsmallFactor t)
          (hpiv t) (w_hat t) (DeltaD t) (hDeltaD t) (hmiddle t)
      let B := higham11_7_permutedLeftFactor (Equiv.refl (Fin n))
        (flMixedL (fp t) s A)
      let C := higham11_7_permutedRightFactor (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A)
      let Cenv := higham11_7_permutedRightEnvelope (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A)
      have hprod : matMul n B C = fun i j => A i j + DeltaFactor i j := by
        ext i j
        simpa [B, C, matMul, higham11_7_permutedLeftFactor,
          higham11_7_permutedRightFactor, Finset.mul_sum, mul_assoc] using
          hfactorEq i j
      have hH : matMul n (absMatrix n B) Cenv =
          higham11_7_permutedAbsLDLT (Equiv.refl (Fin n))
            (flMixedL (fp t) s A) (flMixedD (fp t) s A) := by
        simpa [B, Cenv] using
          higham11_7_permutedLeft_mul_rightEnvelope_eq_permutedAbsLDLT
            (Equiv.refl (Fin n)) (flMixedL (fp t) s A) (flMixedD (fp t) s A)
      have hsolveCoeff : 0 ≤
          higham11_7_actualSolveCoefficient (fp t) n (gammaMid t) := by
        unfold higham11_7_actualSolveCoefficient
        have hgamma : 0 ≤ gamma (fp t) n := gamma_nonneg (fp t) (hvaln t)
        exact add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hgamma) (sq_nonneg _))
          (mul_nonneg
            (add_nonneg
              (add_nonneg zero_le_one (mul_nonneg (by norm_num) hgamma))
              (sq_nonneg _))
            (hgammaMid t))
      have hscale : pPoly n * U.unit t ≤ pEta * U.unit t :=
        (le_add_of_nonneg_right hsolveCoeff).trans (heta_le t)
      have hfactorTotal : ∀ i j, |DeltaFactor i j| ≤
          (pEta * U.unit t) *
            (|A i j| + matMul n (absMatrix n B) Cenv i j) := by
        intro i j
        have hraw : |DeltaFactor i j| ≤ pPoly n * U.unit t *
            (|A i j| + higham11_4_bunchKaufmanProductEntry n
              (flMixedL (fp t) s A) (flMixedD (fp t) s A) i j) := by
          simpa [higham11_3_printedFirstOrderBound, hunit t] using hFactor i j
        have henv : 0 ≤ |A i j| +
            higham11_4_bunchKaufmanProductEntry n
              (flMixedL (fp t) s A) (flMixedD (fp t) s A) i j :=
          add_nonneg (abs_nonneg _)
            (higham11_4_bunchKaufmanProductEntry_nonneg n
              (flMixedL (fp t) s A) (flMixedD (fp t) s A) i j)
        calc
          |DeltaFactor i j| ≤ pPoly n * U.unit t *
              (|A i j| + higham11_4_bunchKaufmanProductEntry n
                (flMixedL (fp t) s A) (flMixedD (fp t) s A) i j) := hraw
          _ ≤ pEta * U.unit t *
              (|A i j| + higham11_4_bunchKaufmanProductEntry n
                (flMixedL (fp t) s A) (flMixedD (fp t) s A) i j) :=
            mul_le_mul_of_nonneg_right hscale henv
          _ = (pEta * U.unit t) *
              (|A i j| + matMul n (absMatrix n B) Cenv i j) := by
            rw [hH, higham11_7_permutedAbsLDLT_refl_eq_productEntry]
      have hpert :=
        higham11_7_perturbed_product_envelopeCondition_le_totalEnvelope
          hn A A_inv B C (C_inv t) Cenv DeltaFactor (pEta * U.unit t)
          (mul_nonneg hpEta (U.unit_nonneg t)) hprod (hCright t)
          (fun i j => Finset.sum_nonneg fun q _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)) hfactorTotal
      rw [hH] at hpert
      change F t ≤ condSkeel n hn A A_inv * Ccond t +
        (pEta * U.unit t) * (condSkeel n hn A A_inv + F t) * Ccond t at hpert
      have hFC : (condSkeel n hn A A_inv + F t) * Ccond t ≤
          (condSkeel n hn A A_inv + Fmax) * Cmax := by
        calc
          (condSkeel n hn A A_inv + F t) * Ccond t ≤
              (condSkeel n hn A A_inv + Fmax) * Ccond t :=
            mul_le_mul_of_nonneg_right
              (add_le_add le_rfl (by simpa [F] using hFbound t)) (hC t)
          _ ≤ (condSkeel n hn A A_inv + Fmax) * Cmax :=
            mul_le_mul_of_nonneg_left (by simpa [Ccond] using hCbound t)
              (add_nonneg hcondA hFmax)
      have hcorrection :
          (pEta * U.unit t) * (condSkeel n hn A A_inv + F t) * Ccond t ≤
            pEta * (condSkeel n hn A A_inv + Fmax) * Cmax * U.unit t := by
        calc
          (pEta * U.unit t) * (condSkeel n hn A A_inv + F t) * Ccond t =
              (pEta * U.unit t) *
                ((condSkeel n hn A A_inv + F t) * Ccond t) := by ring
          _ ≤ (pEta * U.unit t) *
                ((condSkeel n hn A A_inv + Fmax) * Cmax) :=
            mul_le_mul_of_nonneg_left hFC
              (mul_nonneg hpEta (U.unit_nonneg t))
          _ = pEta * (condSkeel n hn A A_inv + Fmax) * Cmax * U.unit t := by
            ring
      exact hpert.trans (add_le_add le_rfl hcorrection)
    · simpa [mul_assoc] using
        (Asymptotics.isBigO_refl U.unit l).const_mul_left
          (pEta * (condSkeel n hn A A_inv + Fmax) * Cmax)
  have hsecond := FamilyFirstOrderLe.coefficient_of_linear_transfer_to
    hpEta U.unit_nonneg hfirst htransfer
  apply hsecond.mono_leading
  intro t
  have hfixed_le : fixed ≤ condSkeel n hn A A_inv := by
    dsimp [fixed]
    exact ch7SkeelCondAtSolutionInf_le_condSkeel n hn A A_inv x hx
  have hCone : 1 ≤ Ccond t := by
    dsimp [Ccond]
    exact higham11_7_one_le_envelopeCondition_of_inverse hn
      (higham11_7_permutedRightFactor (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A)) (C_inv t)
      (higham11_7_permutedRightEnvelope (Equiv.refl (Fin n))
        (flMixedL (fp t) s A) (flMixedD (fp t) s A))
      (hCright t)
      (higham11_7_permutedRightFactor_abs_le_envelope
        (Equiv.refl (Fin n)) (flMixedL (fp t) s A) (flMixedD (fp t) s A))
  have hA_le : condSkeel n hn A A_inv ≤
      condSkeel n hn A A_inv * Ccond t := by
    calc
      condSkeel n hn A A_inv = condSkeel n hn A A_inv * 1 := by ring
      _ ≤ condSkeel n hn A A_inv * Ccond t :=
        mul_le_mul_of_nonneg_left hCone hcondA
  have hbase : fixed + condSkeel n hn A A_inv * Ccond t ≤
      2 * condSkeel n hn A A_inv * Ccond t := by
    linarith
  calc
    pEta * U.unit t *
        (fixed + condSkeel n hn A A_inv * Ccond t) ≤
      pEta * U.unit t *
        (2 * condSkeel n hn A A_inv * Ccond t) :=
      mul_le_mul_of_nonneg_left hbase
        (mul_nonneg hpEta (U.unit_nonneg t))
    _ = (2 * pEta) * U.unit t * condSkeel n hn A A_inv * Ccond t := by
      ring

end NumStability
