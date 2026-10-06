import NumStability.Algorithms.HighamChapter9
import NumStability.Analysis.InstabilityWithoutCancellation

/-!
# Higham Chapter 9: computed-GEPP correction

Higham explicitly notes after Theorem 9.5 that its derivation uses exact
partial-pivoting facts for computed factors.  This module records the mismatch
on the concrete rounded two-by-two trace from Chapter 1 and gives the rigorous
replacement bound in terms of the *computed* multiplier and growth bounds.
-/

namespace NumStability

open scoped BigOperators

/-- The concrete rounded partial-pivoting upper factor cannot simultaneously
be the exact GEPP upper-factor trace used by the printed proof of Theorem 9.5.
This is the formal witness for the exact/computed substitution acknowledged in
the source. -/
theorem higham9_5_roundedU_not_exactGEPPUTrace
    {epsilon : Real} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    ¬ higham9_7_PartialPivotGEPPUTrace 2
        (noPivotExampleA epsilon) noPivotPartialPivotRoundedU := by
  intro htrace
  generalize hUeq : noPivotPartialPivotRoundedU = U at htrace
  cases htrace with
  | step hchoice hpivot hnext =>
      rename_i r U1
      have hr : r = (1 : Fin 2) := by
        fin_cases r
        · have hmax := hchoice.2 (1 : Fin 2) (by norm_num)
          simp [noPivotExampleA, abs_of_pos hepsilon_pos] at hmax
          linarith
        · rfl
      subst r
      cases hnext with
      | step hchoice1 hpivot1 hnext0 =>
          rename_i r1 U0
          fin_cases r1
          have hentry := congrFun (congrFun hUeq (1 : Fin 2)) (1 : Fin 2)
          change noPivotPartialPivotRoundedU 1 1 = _ at hentry
          simp [noPivotPartialPivotRoundedU, luFirstStepU,
            higham9_2_rowPermutedMatrix, higham9_7_firstPivotRowSwap,
            luFirstSchurComplement, noPivotExampleA] at hentry
          linarith

/-- Concrete IEEE-binary32 instance of the source's exact/computed GEPP
mismatch.  The same `Uhat` has an actual rounded backward-error certificate in
`noPivotIeeeSinglePartialPivotRoundedLUBackwardError`. -/
theorem higham9_5_ieeeSingle_roundedU_not_exactGEPPUTrace :
    ¬ higham9_7_PartialPivotGEPPUTrace 2
        (noPivotExampleA noPivotIeeeSingleSmallEpsilon)
        noPivotPartialPivotIeeeSingleRoundedU := by
  simpa [noPivotPartialPivotIeeeSingleRoundedU,
    noPivotPartialPivotRoundedU] using
    (higham9_5_roundedU_not_exactGEPPUTrace
      (epsilon := noPivotIeeeSingleSmallEpsilon)
      (by norm_num [noPivotIeeeSingleSmallEpsilon])
      (by norm_num [noPivotIeeeSingleSmallEpsilon]))

/-- A single source-discrepancy certificate: these are genuine rounded
partial-pivoting factors, yet their computed upper factor is not the exact
GEPP trace required by the printed proof maneuver. -/
theorem higham9_5_ieeeSingle_source_discrepancy :
    PermutedLUBackwardError 2
        (noPivotExampleA noPivotIeeeSingleSmallEpsilon)
        (noPivotPartialPivotL noPivotIeeeSingleSmallEpsilon)
        noPivotPartialPivotIeeeSingleRoundedU
        noPivotPartialPivotSwap noPivotIeeeSingleSmallEpsilon /\
      ¬ higham9_7_PartialPivotGEPPUTrace 2
        (noPivotExampleA noPivotIeeeSingleSmallEpsilon)
        noPivotPartialPivotIeeeSingleRoundedU :=
  ⟨noPivotIeeeSinglePartialPivotRoundedLUBackwardError,
    higham9_5_ieeeSingle_roundedU_not_exactGEPPUTrace⟩

/-- A computed multiplier bound `|Lhat_ik| <= lambda` gives the exact row-sum
factor used in the corrected Wilkinson argument. -/
theorem higham9_5_computedMultiplier_row_sum_le
    (n : Nat) (Lhat : Fin n -> Fin n -> Real) (lambda : Real)
    (hL : forall i k, |Lhat i k| <= lambda) :
    forall i, (Finset.univ.sum fun k : Fin n => |Lhat i k|) <=
      (n : Real) * lambda := by
  intro i
  calc
    (Finset.univ.sum fun k : Fin n => |Lhat i k|) <=
        Finset.univ.sum (fun _k : Fin n => lambda) := by
      exact Finset.sum_le_sum (fun k _hk => hL i k)
    _ = (n : Real) * lambda := by simp

/-- Correct normwise conversion with a computed multiplier envelope.  Unlike
the printed argument, this lemma does not replace computed factors by exact
ones. -/
theorem higham9_5_computedMultiplier_infNorm
    (n : Nat) (hn : 0 < n)
    (Lhat Uhat DeltaA : Fin n -> Fin n -> Real)
    (epsilon lambda : Real) (hepsilon : 0 <= epsilon)
    (hDelta : forall i j,
      |DeltaA i j| <= epsilon *
        Finset.univ.sum (fun k : Fin n => |Lhat i k| * |Uhat k j|))
    (hL : forall i k, |Lhat i k| <= lambda) :
    infNorm DeltaA <= epsilon * ((n : Real) * lambda) * infNorm Uhat := by
  apply infNorm_le_of_row_sum_le
  · intro i
    have hcomponent :=
      componentwise_to_normwise_bound n hn Lhat Uhat DeltaA epsilon
        hepsilon hDelta i
    have hrow := higham9_5_computedMultiplier_row_sum_le n Lhat lambda hL i
    calc
      Finset.univ.sum (fun j : Fin n => |DeltaA i j|) <=
          epsilon * (Finset.univ.sum fun k : Fin n => |Lhat i k|) *
            infNorm Uhat := hcomponent
      _ <= epsilon * ((n : Real) * lambda) * infNorm Uhat := by
        apply mul_le_mul_of_nonneg_right _ (infNorm_nonneg Uhat)
        exact mul_le_mul_of_nonneg_left hrow hepsilon
  · let i0 : Fin n := ⟨0, hn⟩
    have hlambda : 0 <= lambda :=
      le_trans (abs_nonneg (Lhat i0 i0)) (hL i0 i0)
    exact mul_nonneg
      (mul_nonneg hepsilon
        (mul_nonneg (Nat.cast_nonneg' n) hlambda))
      (infNorm_nonneg Uhat)

/-- Rigorous correction of Theorem 9.5 in the quantities described in the
book's post-theorem caveat: `rhohat` bounds the growth of the computed `Uhat`,
and computed multipliers are bounded by `1+u`. -/
theorem higham9_5_computed_wilkinson_source_correction
    (fp : FPModel) (n : Nat) (hn_pos : 0 < n)
    (A Lhat Uhat : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (u rhohat : Real) (hu : 0 <= u) (hrho : 0 <= rhohat)
    (hAmax : 0 < maxEntryNorm hn_pos A)
    (hcomputedGrowth :
      growthFactorEntry hn_pos A Uhat hAmax <= rhohat)
    (hLdiag : forall i : Fin n, Lhat i i ≠ 0)
    (hUdiag : forall i : Fin n, Uhat i i ≠ 0)
    (hLU : LUBackwardError n A Lhat Uhat (gamma fp n))
    (hn : gammaValid fp n) (hn3 : gammaValid fp (3 * n))
    (hcomputedMultipliers : forall i k : Fin n, |Lhat i k| <= 1 + u) :
    let yhat := fl_forwardSub fp n Lhat b
    let xhat := fl_backSub fp n Uhat yhat
    exists DeltaA : Fin n -> Fin n -> Real,
      infNorm DeltaA <=
          (n : Real) ^ 2 * (1 + u) * gamma fp (3 * n) * rhohat *
            infNorm A /\
      (forall i, Finset.univ.sum (fun j : Fin n =>
        (A i j + DeltaA i j) * xhat j) = b i) := by
  dsimp
  obtain ⟨DeltaA, hDelta, hsolve⟩ :=
    lu_solve_backward_error_tight fp n A Lhat Uhat b
      hLdiag hUdiag hLU hn hn3
  refine ⟨DeltaA, ?_, hsolve⟩
  have hnorm :=
    higham9_5_computedMultiplier_infNorm n hn_pos Lhat Uhat DeltaA
      (gamma fp (3 * n)) (1 + u) (gamma_nonneg fp hn3) hDelta
      hcomputedMultipliers
  have hUgrowth :
      infNorm Uhat <= (n : Real) * rhohat * infNorm A :=
    infNorm_le_card_mul_growthFactorEntry_bound hn_pos A Uhat rhohat
      hAmax hrho hcomputedGrowth
  have hcoef :
      0 <= gamma fp (3 * n) * ((n : Real) * (1 + u)) := by
    exact mul_nonneg (gamma_nonneg fp hn3)
      (mul_nonneg (Nat.cast_nonneg' n) (by linarith))
  calc
    infNorm DeltaA <=
        gamma fp (3 * n) * ((n : Real) * (1 + u)) * infNorm Uhat := hnorm
    _ <= gamma fp (3 * n) * ((n : Real) * (1 + u)) *
          ((n : Real) * rhohat * infNorm A) :=
      mul_le_mul_of_nonneg_left hUgrowth hcoef
    _ = (n : Real) ^ 2 * (1 + u) * gamma fp (3 * n) * rhohat *
          infNorm A := by ring

end NumStability
