import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Compensated.Kahan.Coefficients.Affine
import NumStability.Algorithms.Summation.Compensated.Kahan.Core

namespace NumStability

/-!
# Higham equation (4.8): bare-model strength limitations

These source audits isolate why the printed leading-`2u` backward-error
shape cannot follow from the repository's bare relative-error `FPModel`
alone.  They do not refute correctly rounded finite arithmetic.
-/

/-- A small-unit-roundoff abstract model that is useful for auditing attempted
bare-`FPModel` Kahan routes.  Addition from the left zero is exact, as required
by `FPModel`; every other addition rounds upward by `u`, while subtraction rounds
downward by `u`.

This model is not intended as a concrete finite format.  It records that the
abstract relative-error contract alone permits independent operation-level signs
that finite round-to-even coherence would rule out. -/
noncomputable def kahanBiasedSmallCounterexampleFPModel (u : ℝ) (hu : 0 ≤ u) :
    FPModel where
  u := u
  u_nonneg := hu
  fl_add := fun x y => if x = 0 then y else (x + y) * (1 + u)
  fl_sub := fun x y => (x - y) * (1 - u)
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · refine ⟨0, ?_, ?_⟩
      · simpa using hu
      · simp [hx]
    · refine ⟨u, ?_, ?_⟩
      · rw [abs_of_nonneg hu]
      · simp [hx]
  model_sub := by
    intro x y
    refine ⟨-u, ?_, ?_⟩
    · rw [abs_neg, abs_of_nonneg hu]
    · ring
  model_mul := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using hu
    · ring
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, ?_⟩
    · simpa using hu
    · ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, ?_, ?_⟩
    · simpa using hu
    · ring

/-- Two-term audit input for the small-unit-roundoff Kahan route-elimination
example.  The second term is zero, so any source-weight representation has a
unique coefficient for the first term. -/
def kahanBiasedTwoStepInput : Fin 2 → ℝ :=
  fun i => if i.val = 0 then 1 else 0













/-- One-input obstruction to closing the current input-majorant affine
residual-budget route with a fixed second-order constant.

For exact arithmetic advertised with unit roundoff `u`, one input of magnitude
`1` has zero propagated indexed correction budget, but the final
input-majorant retained-correction term is
`u * (1 + u)^2 * (2 + u)`.  This cannot be bounded by `C*u^2` whenever
`C*u <= 1`. -/
theorem not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one
    (C u : ℝ) (hu_pos : 0 < u) (hCu_le_one : C * u ≤ 1) :
    let fp : FPModel := FPModel.exactWithUnitRoundoff u (le_of_lt hu_pos)
    let v : Fin 1 → ℝ := fun _ => 1
    ¬
      (let steps := kahanAffineCoeffSteps fp v 1 (Nat.le_refl 1)
       kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < 1 then
              (kahanInputAbsMajorant fp v j (Nat.le_of_lt hj)).e
            else 0)
          steps +
          (kahanInputAbsMajorant fp v 1 (Nat.le_refl 1)).e ≤
        (C * (1 : ℝ) * fp.u ^ 2) *
          (∑ j : Fin steps.length, |(steps.get j).x|)) := by
  dsimp
  intro h
  norm_num [FPModel.exactWithUnitRoundoff, kahanAffineCoeffSteps,
    kahanAffineCoeffStepOfIndex, kahanAffineCorrectionIndexedBudget,
    kahanInputAbsMajorant] at h
  have hleft_lower :
      2 * u ≤ u * (1 + u) ^ 2 * (2 + u) := by
    have h1 : 1 ≤ (1 + u) ^ 2 := by
      nlinarith [hu_pos, sq_nonneg u]
    have h2 : 2 ≤ 2 + u := by
      linarith
    have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
    calc
      2 * u = u * 1 * 2 := by ring
      _ ≤ u * (1 + u) ^ 2 * (2 + u) := by
          exact
            mul_le_mul
              (mul_le_mul_of_nonneg_left h1 hu_nonneg) h2
              (by norm_num)
              (mul_nonneg hu_nonneg
                (by nlinarith [hu_pos, sq_nonneg u]))
  have hrhs_le_u : C * u ^ 2 ≤ u := by
    have hmul :=
      mul_le_mul_of_nonneg_right hCu_le_one (le_of_lt hu_pos)
    nlinarith
  have htwo_le_one : 2 * u ≤ u :=
    hleft_lower.trans (h.trans hrhs_le_u)
  nlinarith

/-- No nonnegative fixed constant can make the current input-majorant affine
residual budget imply a second-order source-scaled estimate uniformly in small
advertised unit roundoffs.

This is a route-elimination theorem for the remaining Higham Chapter 4
equation (4.8) bottleneck.  The existing conditional wrapper
`fl_kahanSum_backward_error_source_bound_of_affine_residualBudget` is still
valid, but its residual-budget hypothesis cannot be discharged by the present
input-only majorant with a fixed `C*n*u^2*sum |x_i|` estimate. -/
theorem not_exists_kahanAffine_residualBudget_inputMajorant_fixed_C :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, ∀ (hu_pos : 0 < u), C * u ≤ 1 →
        let fp : FPModel := FPModel.exactWithUnitRoundoff u (le_of_lt hu_pos)
        let v : Fin 1 → ℝ := fun _ => 1
        let steps := kahanAffineCoeffSteps fp v 1 (Nat.le_refl 1)
        kahanAffineCorrectionIndexedBudget
            (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
            (fun j =>
              if hj : j < 1 then
                (kahanInputAbsMajorant fp v j (Nat.le_of_lt hj)).e
              else 0)
            steps +
            (kahanInputAbsMajorant fp v 1 (Nat.le_refl 1)).e ≤
          (C * (1 : ℝ) * fp.u ^ 2) *
            (∑ j : Fin steps.length, |(steps.get j).x|) := by
  rintro ⟨C, hC_nonneg, hall⟩
  let u : ℝ := 1 / (C + 1)
  have hden : 0 < C + 1 := by
    linarith
  have hu_pos : 0 < u := by
    dsimp [u]
    exact one_div_pos.mpr hden
  have hCu_le_one : C * u ≤ 1 := by
    dsimp [u]
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith
  have hineq := hall u hu_pos hCu_le_one
  exact
    not_kahanAffine_residualBudget_inputMajorant_one_of_Cu_le_one
      C u hu_pos hCu_le_one hineq

/-- Closed form for the biased small-unit-roundoff model on the two-term audit
input.  The returned-sum deviation is about `3u`, not `2u`, which is the formal
obstruction to proving the printed returned-Kahan coefficient theorem from the
bare `FPModel` axioms alone. -/
theorem fl_kahanSum_biasedSmallCounterexample_twoStep :
    fl_kahanSum
        (kahanBiasedSmallCounterexampleFPModel (1 / 1000) (by norm_num)) 2
        kahanBiasedTwoStepInput =
      (1003004003001 : ℝ) / 1000000000000 := by
  unfold fl_kahanSum fl_kahanState kahanPrefixState
  rw [Fin.foldl_succ_last]
  rw [Fin.foldl_succ_last]
  norm_num [kahanStep,
    kahanStepTrace, KahanStepTrace.nextState, KahanState.zero,
    kahanBiasedSmallCounterexampleFPModel, kahanBiasedTwoStepInput]

/-- Parametric closed form for the biased small-unit-roundoff model on the
two-term audit input.  For `0 < u < 1`, the unique returned coefficient has
first-order deviation `3*u`. -/
theorem fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one
    {u : ℝ} (hu : 0 ≤ u) (hu_pos : 0 < u) (hu_lt_one : u < 1) :
    fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
        kahanBiasedTwoStepInput =
      1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
  have h_one_ne : (1 : ℝ) ≠ 0 := by norm_num
  have h_one_add_pos : 0 < 1 + u := by nlinarith
  have h_one_add_ne : 1 + u ≠ 0 := ne_of_gt h_one_add_pos
  have h_one_sub_pos : 0 < 1 - u := by nlinarith
  have h_one_sub_ne : 1 - u ≠ 0 := ne_of_gt h_one_sub_pos
  have h_neg_one_sub_ne : -1 - u ≠ 0 := by nlinarith
  have h_e_add_branch : ¬ (-1 - u = 0 ∨ 1 - u = 0) := by
    intro h
    rcases h with h | h
    · exact h_neg_one_sub_ne h
    · exact h_one_sub_ne h
  have h_e_add_branch' : ¬ (-u + -1 = 0 ∨ 1 - u = 0) := by
    intro h
    rcases h with h | h
    · have : -1 - u = 0 := by nlinarith
      exact h_neg_one_sub_ne this
    · exact h_one_sub_ne h
  have hsub_ne : (0 - (1 + u)) * (1 - u) ≠ 0 := by
    have hprod_pos : 0 < (1 + u) * (1 - u) :=
      mul_pos h_one_add_pos h_one_sub_pos
    nlinarith
  unfold fl_kahanSum fl_kahanState kahanPrefixState
  rw [Fin.foldl_succ_last]
  rw [Fin.foldl_succ_last]
  norm_num [kahanStep, kahanStepTrace, KahanStepTrace.nextState,
    KahanState.zero, kahanBiasedSmallCounterexampleFPModel,
    kahanBiasedTwoStepInput, h_one_ne, h_one_add_ne, hsub_ne,
    h_e_add_branch]
  rw [if_neg h_e_add_branch']
  ring_nf

/-- Generic version of the biased small-`u` returned-cap obstruction.

For any proposed second-order constant `C`, whenever `C*u <= 1/2`, the model's
returned value on `[1,0]` cannot be represented with all source weights bounded
by `2*u + C*u^2`.  This records the first-order obstruction independently of
the particular exact-subtraction constants used below. -/
theorem not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half
    {u C : ℝ} (hu : 0 ≤ u) (hu_pos : 0 < u) (hu_lt_one : u < 1)
    (hCu : C * u ≤ 1 / 2) :
    ¬ ∃ μ : Fin 2 → ℝ,
      (∀ i, |μ i| ≤ 2 * u + C * u ^ 2) ∧
      fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
          kahanBiasedTwoStepInput =
        ∑ i : Fin 2, kahanBiasedTwoStepInput i * (1 + μ i) := by
  intro h
  rcases h with ⟨μ, hμ, hsum⟩
  have hsum_closed :
      fl_kahanSum (kahanBiasedSmallCounterexampleFPModel u hu) 2
        kahanBiasedTwoStepInput =
        1 + 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 :=
    fl_kahanSum_biasedSmallCounterexample_twoStep_of_pos_lt_one
      hu hu_pos hu_lt_one
  have hsource :
      (∑ i : Fin 2, kahanBiasedTwoStepInput i * (1 + μ i)) =
        1 + μ ⟨0, by decide⟩ := by
    norm_num [kahanBiasedTwoStepInput]
  have hmu_eq :
      μ ⟨0, by decide⟩ =
        3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    nlinarith [hsum, hsum_closed, hsource]
  have hupper :
      μ ⟨0, by decide⟩ ≤ 2 * u + C * u ^ 2 :=
    (abs_le.mp (hμ ⟨0, by decide⟩)).2
  have hmu0 :
      μ 0 = 3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    simpa using hmu_eq
  have hupper' :
      3 * u + 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 ≤
        2 * u + C * u ^ 2 := by
    simpa [hmu0] using hupper
  have hCu_sq : C * u ^ 2 ≤ (1 / 2) * u := by
    have hmul := mul_le_mul_of_nonneg_right hCu hu
    nlinarith
  have hpos_tail : 0 ≤ 4 * u ^ 2 + 3 * u ^ 3 + u ^ 4 := by
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    have hu3 : 0 ≤ u ^ 3 := by nlinarith [hu, hu2]
    have hu4 : 0 ≤ u ^ 4 := by nlinarith [hu2]
    nlinarith
  nlinarith [hupper', hCu_sq, hpos_tail, hu_pos]

/-- For every nonnegative proposed second-order constant and every positive
unit-roundoff neighbourhood, there is a positive unit roundoff in that
neighbourhood for which C*u is at most one half.  This packages the
quantifier step needed to turn the parametric Kahan counterexample into a
genuine first-order source discrepancy. -/
theorem exists_kahanBiasedSmallCounterexample_unitRoundoff
    {C epsilon : Real} (hC : 0 <= C) (hepsilon : 0 < epsilon) :
    exists u : Real,
      0 <= u /\ 0 < u /\ u < 1 /\ u <= epsilon /\ C * u <= 1 / 2 := by
  let d : Real := 4 * (C + 1) * (epsilon + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hepsilon1 : 0 < epsilon + 1 := by linarith
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hd_one : 1 <= d := by
    dsimp [d]
    nlinarith [mul_nonneg hC (le_of_lt hepsilon)]
  let u : Real := epsilon / d
  have hu_pos : 0 < u := by
    dsimp [u]
    exact div_pos hepsilon hd
  have hu : 0 <= u := le_of_lt hu_pos
  have hu_lt_one : u < 1 := by
    dsimp [u]
    rw [div_lt_one hd]
    dsimp [d]
    nlinarith [mul_nonneg hC (le_of_lt hepsilon)]
  have hu_le_epsilon : u <= epsilon := by
    dsimp [u]
    rw [div_le_iff₀ hd]
    have hmul :=
      mul_le_mul_of_nonneg_left hd_one (le_of_lt hepsilon)
    simpa using hmul
  have hCu : C * u <= 1 / 2 := by
    dsimp [u]
    rw [← mul_div_assoc]
    rw [div_le_iff₀ hd]
    dsimp [d]
    nlinarith [mul_nonneg hC (le_of_lt hepsilon)]
  exact ⟨u, hu, hu_pos, hu_lt_one, hu_le_epsilon, hCu⟩

/-- Uniform two-term formulation of the printed first-order content of
Higham (4.8) over the bare floating-point model.  A fixed C is allowed to
absorb the O(u^2) term, and the assertion is required only in a positive
neighbourhood of zero. -/
def Higham48BareFPModelTwoTermSecondOrderBound
    (C epsilon : Real) : Prop :=
  forall (fp : FPModel), 0 < fp.u -> fp.u <= epsilon ->
    exists mu : Fin 2 -> Real,
      (forall i, |mu i| <= 2 * fp.u + C * fp.u ^ 2) /\
      fl_kahanSum fp 2 kahanBiasedTwoStepInput =
        Finset.univ.sum
          (fun i : Fin 2 => kahanBiasedTwoStepInput i * (1 + mu i))

/-- Model-strength discrepancy terminal for Higham (4.8) in the repository's bare
floating-point model: even for n=2, no fixed second-order constant makes the
printed leading-2*u backward-error assertion true on any neighbourhood of
u=0.  The countermodels have arbitrarily small positive unit roundoff.

This result concerns only the abstract FPModel contract.  In particular, it
does not by itself refute the printed claim for correctly rounded finite
arithmetic, whose representable-result coherence excludes this family. -/
theorem not_exists_higham48BareFPModelTwoTermSecondOrderBound :
    Not (exists C epsilon : Real,
      0 <= C /\ 0 < epsilon /\
        Higham48BareFPModelTwoTermSecondOrderBound C epsilon) := by
  rintro ⟨C, epsilon, hC, hepsilon, hclaim⟩
  obtain ⟨u, hu, hu_pos, hu_lt_one, hu_le_epsilon, hCu⟩ :=
    exists_kahanBiasedSmallCounterexample_unitRoundoff hC hepsilon
  let fp := kahanBiasedSmallCounterexampleFPModel u hu
  have hfp_pos : 0 < fp.u := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_pos
  have hfp_le : fp.u <= epsilon := by
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hu_le_epsilon
  rcases hclaim fp hfp_pos hfp_le with ⟨mu, hmu, hsum⟩
  apply
    not_exists_fl_kahanSum_biasedSmallCounterexample_twoStep_source_bound_of_Cu_le_half
      hu hu_pos hu_lt_one hCu
  refine ⟨mu, ?_, ?_⟩
  · intro i
    simpa [fp, kahanBiasedSmallCounterexampleFPModel] using hmu i
  · simpa [fp] using hsum

/-- The small-unit-roundoff biased model rejects the common false shortcut
that the source-shaped returned-Kahan theorem follows from the bare `FPModel`
contract with the exact-subtraction-route constants.

For `u = 1/1000`, the returned value on `[1,0]` has the unique source
coefficient `1 + μ` with
`μ = 3u + 4u^2 + 3u^3 + u^4`, exceeding
`2u + 2*(3+40*2)*u^2`.  Thus the remaining Eq. (4.8) proof must use genuine
finite-format/coherence structure or a stronger coefficient argument; it cannot
be discharged by the abstract model and a loose second-order constant alone. -/
theorem not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants :
    ¬ ∀ (fp : FPModel) (n : ℕ) (v : Fin n → ℝ),
      fp.u ≤ 1 / 64 →
      (3 + 40 * (n : ℝ)) * fp.u ≤ 1 →
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤
          2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
        fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  intro h
  let u : ℝ := 1 / 1000
  have hu : 0 ≤ u := by norm_num [u]
  let fp := kahanBiasedSmallCounterexampleFPModel u hu
  let v := kahanBiasedTwoStepInput
  have huSmall : fp.u ≤ 1 / 64 := by
    norm_num [fp, u, kahanBiasedSmallCounterexampleFPModel]
  have hBudget : (3 + 40 * (2 : ℝ)) * fp.u ≤ 1 := by
    norm_num [fp, u, kahanBiasedSmallCounterexampleFPModel]
  rcases h fp 2 v huSmall hBudget with ⟨μ, hμ, hsum⟩
  have hsum_closed :
      fl_kahanSum fp 2 v =
        (1003004003001 : ℝ) / 1000000000000 := by
    simpa [fp, v, u] using fl_kahanSum_biasedSmallCounterexample_twoStep
  have hsource :
      (∑ i : Fin 2, v i * (1 + μ i)) = 1 + μ ⟨0, by decide⟩ := by
    norm_num [v, kahanBiasedTwoStepInput]
  have hmu_eq :
      μ ⟨0, by decide⟩ = (3004003001 : ℝ) / 1000000000000 := by
    nlinarith [hsum, hsum_closed, hsource]
  have hbound' :
      μ ⟨0, by decide⟩ ≤
        2 * fp.u + 2 * (3 + 40 * (2 : ℝ)) * fp.u ^ 2 := by
    exact (abs_le.mp (hμ ⟨0, by decide⟩)).2
  have hmu0 : μ 0 = (3004003001 : ℝ) / 1000000000000 := by
    simpa using hmu_eq
  have hfalse :
      ((3004003001 : ℝ) / 1000000000000) ≤
        2 * fp.u + 2 * (3 + 40 * (2 : ℝ)) * fp.u ^ 2 := by
    simpa [hmu0] using hbound'
  norm_num [fp, u, kahanBiasedSmallCounterexampleFPModel] at hfalse

end NumStability
