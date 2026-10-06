import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Source.Higham.Chapter04.Equation08.ModelStrength

namespace NumStability

/-!
# Higham equation (4.9): bare-model strength limitations

These source audits derive the corresponding forward-error obstruction from
the shared equation-(4.8) biased countermodel.  They concern the abstract
`FPModel`, not concrete correctly rounded finite formats.
-/

/-- Pointwise forward-error obstruction corresponding to the biased Kahan
countermodel.  Its returned error has leading coefficient 3, so a proposed
leading-2 bound plus C*u^2 fails whenever C*u is at most one half. -/
theorem
    not_fl_kahanSum_biasedSmallCounterexample_twoStep_forward_bound_of_Cu_le_half
    {u C : Real} (hu : 0 <= u) (hu_pos : 0 < u) (hu_lt_one : u < 1)
    (hCu : C * u <= 1 / 2) :
    Not
      (|fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
            kahanBiasedTwoStepInput -
          Finset.univ.sum (fun i : Fin 2 => kahanBiasedTwoStepInput i)| <=
        (2 * u + C * u ^ 2) *
          Finset.univ.sum (fun i : Fin 2 => |kahanBiasedTwoStepInput i|)) := by
  intro hbound
  have hsum_closed :
      fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
          kahanBiasedTwoStepInput =
        1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 :=
    fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one
      hu hu_pos hu_lt_one
  have hsum_exact :
      Finset.univ.sum (fun i : Fin 2 => kahanBiasedTwoStepInput i) = 1 := by
    norm_num [kahanBiasedTwoStepInput]
  have habs_exact :
      Finset.univ.sum (fun i : Fin 2 => |kahanBiasedTwoStepInput i|) = 1 := by
    norm_num [kahanBiasedTwoStepInput]
  rw [hsum_closed, hsum_exact, habs_exact, mul_one] at hbound
  have hu2 : 0 <= u ^ 2 := sq_nonneg u
  have hu3 : 0 <= u ^ 3 := by nlinarith [hu, hu2]
  have hu4 : 0 <= u ^ 4 := by nlinarith [hu2]
  have herror_nonneg :
      0 <= 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    nlinarith
  have herror :
      3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 <=
        2 * u + C * u ^ 2 := by
    rw [show
      1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 - 1 =
        3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 by ring,
      abs_of_nonneg herror_nonneg] at hbound
    exact hbound
  have hCu_sq : C * u ^ 2 <= (1 / 2) * u := by
    have hmul := mul_le_mul_of_nonneg_right hCu hu
    nlinarith
  have htail : 0 <= 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    nlinarith
  nlinarith [herror, hCu_sq, htail, hu_pos]

/-- Uniform two-term formulation of the printed first-order content of
Higham (4.9) over the bare floating-point model. -/
def Higham49BareFPModelTwoTermSecondOrderBound
    (C epsilon : Real) : Prop :=
  forall (fp : FPModel), 0 < fp.u -> fp.u <= epsilon ->
    |fl_kahanSum fp 2 kahanBiasedTwoStepInput -
        Finset.univ.sum (fun i : Fin 2 => kahanBiasedTwoStepInput i)| <=
      (2 * fp.u + C * fp.u ^ 2) *
        Finset.univ.sum (fun i : Fin 2 => |kahanBiasedTwoStepInput i|)

/-- Model-strength discrepancy terminal for Higham (4.9) in the repository's bare
floating-point model: no fixed second-order constant repairs the printed
leading-2*u forward bound near u=0, already for the two-term input [1,0].

As above, this is a limitation theorem for FPModel, not a finite-format
counterexample to the source statement. -/
theorem not_exists_higham49BareFPModelTwoTermSecondOrderBound :
    Not (exists C epsilon : Real,
      0 <= C /\ 0 < epsilon /\
        Higham49BareFPModelTwoTermSecondOrderBound C epsilon) := by
  rintro ⟨C, epsilon, hC, hepsilon, hclaim⟩
  obtain ⟨u, hu, hu_pos, hu_lt_one, hu_le_epsilon, hCu⟩ :=
    exists_kahanBiasedSmallCounterexample_unitRoundoff hC hepsilon
  let fp := kahanBiasedSmallCounterexampleFPModel u hu
  have hfp_pos : 0 < fp.u := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_pos
  have hfp_le : fp.u <= epsilon := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_le_epsilon
  have hbound := hclaim fp hfp_pos hfp_le
  apply
    not_fl_kahanSum_biasedSmallCounterexample_twoStep_forward_bound_of_Cu_le_half
      hu hu_pos hu_lt_one hCu
  simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hbound


end NumStability
