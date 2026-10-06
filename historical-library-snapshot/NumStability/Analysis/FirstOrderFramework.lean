-- Analysis/FirstOrderFramework.lean

import Mathlib.Tactic.Linarith
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# First-order rounding-error framework

Higham Chapter 3, Section 3.8 is an explanatory framework rather than a
specific algorithm.  It says that, after linearizing the stages of a computation
around the exact data, forward error is obtained by propagating local rounding
errors through products of stage Jacobians, while backward error asks for a
data perturbation whose problem Jacobian produces the observed forward error.

This file records that first-order algebra in finite-dimensional real vector
form.  The differentiability/Taylor remainder hypotheses that justify a
particular Jacobian linearization remain visible to the caller; the theorems
below prove the finite linearized propagation and backward-equation surfaces.
-/

/-- One linearized stage-error update:

`e_{k+1} = J_k e_k + localErr_k`.

The matrix `J` is the Jacobian of the exact stage map at the nominal trajectory,
and `localErr` is the first-order local rounding-error vector for that stage. -/
noncomputable def firstOrderStageError {d : ℕ}
    (J : Fin d → Fin d → ℝ) (e localErr : Fin d → ℝ) : Fin d → ℝ :=
  fun i => rectMatMulVec J e i + localErr i

/-- Error after `p` first-order stages, starting from zero input error. -/
noncomputable def firstOrderForwardError : (p d : ℕ) →
    (Fin p → Fin d → Fin d → ℝ) → (Fin p → Fin d → ℝ) → Fin d → ℝ
  | 0, _d, _J, _localErr => fun _ => 0
  | p + 1, d, J, localErr =>
      firstOrderStageError (J (Fin.last p))
        (firstOrderForwardError p d
          (fun k => J k.castSucc) (fun k => localErr k.castSucc))
        (localErr (Fin.last p))

/-- Scalar recurrence for a normwise forward-error budget:

`b_{k+1} = c_k b_k + eps_k`,

where `c_k` bounds the stage Jacobian as an operator in the chosen norm and
`eps_k` bounds the local rounding-error vector. -/
noncomputable def firstOrderForwardBudget : (p : ℕ) →
    (Fin p → ℝ) → (Fin p → ℝ) → ℝ
  | 0, _c, _eps => 0
  | p + 1, c, eps =>
      c (Fin.last p) *
        firstOrderForwardBudget p
          (fun k => c k.castSucc) (fun k => eps k.castSucc) +
        eps (Fin.last p)

/-- Normwise first-order forward-error propagation.

If each Jacobian stage has Euclidean operator budget `c k` and each local
rounding-error vector has norm at most `eps k`, then the linearized accumulated
forward error is bounded by the scalar recurrence in
`firstOrderForwardBudget`. -/
theorem firstOrderForwardError_vecNorm2_le_budget (p d : ℕ)
    (J : Fin p → Fin d → Fin d → ℝ) (localErr : Fin p → Fin d → ℝ)
    (c eps : Fin p → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hJ : ∀ k e, vecNorm2 (rectMatMulVec (J k) e) ≤ c k * vecNorm2 e)
    (hlocal : ∀ k, vecNorm2 (localErr k) ≤ eps k) :
    vecNorm2 (firstOrderForwardError p d J localErr) ≤
      firstOrderForwardBudget p c eps := by
  induction p with
  | zero =>
      simp [firstOrderForwardError, firstOrderForwardBudget, vecNorm2_zero]
  | succ p ih =>
      have hprefix :
          vecNorm2
              (firstOrderForwardError p d
                (fun k => J k.castSucc) (fun k => localErr k.castSucc)) ≤
            firstOrderForwardBudget p
              (fun k => c k.castSucc) (fun k => eps k.castSucc) :=
        ih (fun k => J k.castSucc) (fun k => localErr k.castSucc)
          (fun k => c k.castSucc) (fun k => eps k.castSucc)
          (fun k => hc k.castSucc)
          (fun k e => hJ k.castSucc e)
          (fun k => hlocal k.castSucc)
      have hstage :=
        hJ (Fin.last p)
          (firstOrderForwardError p d
            (fun k => J k.castSucc) (fun k => localErr k.castSucc))
      have hloc := hlocal (Fin.last p)
      calc
        vecNorm2 (firstOrderForwardError (p + 1) d J localErr)
            ≤
              vecNorm2
                (rectMatMulVec (J (Fin.last p))
                  (firstOrderForwardError p d
                    (fun k => J k.castSucc) (fun k => localErr k.castSucc))) +
              vecNorm2 (localErr (Fin.last p)) := by
                simpa [firstOrderForwardError, firstOrderStageError] using
                  vecNorm2_add_le
                    (rectMatMulVec (J (Fin.last p))
                      (firstOrderForwardError p d
                        (fun k => J k.castSucc) (fun k => localErr k.castSucc)))
                    (localErr (Fin.last p))
        _ ≤
              c (Fin.last p) *
                vecNorm2
                  (firstOrderForwardError p d
                    (fun k => J k.castSucc) (fun k => localErr k.castSucc)) +
              eps (Fin.last p) := by
                exact add_le_add hstage hloc
        _ ≤
              c (Fin.last p) *
                firstOrderForwardBudget p
                  (fun k => c k.castSucc) (fun k => eps k.castSucc) +
              eps (Fin.last p) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hprefix (hc (Fin.last p)))
                  le_rfl
        _ = firstOrderForwardBudget (p + 1) c eps := by
              simp [firstOrderForwardBudget]

/-- Final output selection matrix applied to the accumulated first-order state
error.  This models the source's matrix `P` formed from selected columns of the
identity. -/
noncomputable def firstOrderSelectedOutputError {d m : ℕ}
    (P : Fin m → Fin d → ℝ) (e : Fin d → ℝ) : Fin m → ℝ :=
  rectMatMulVec P e

/-- Forward-error bound after applying the final output selection/projection. -/
theorem firstOrderSelectedOutputError_vecNorm2_le (p d m : ℕ)
    (J : Fin p → Fin d → Fin d → ℝ) (localErr : Fin p → Fin d → ℝ)
    (c eps : Fin p → ℝ) (P : Fin m → Fin d → ℝ) (cP : ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hP_nonneg : 0 ≤ cP)
    (hJ : ∀ k e, vecNorm2 (rectMatMulVec (J k) e) ≤ c k * vecNorm2 e)
    (hlocal : ∀ k, vecNorm2 (localErr k) ≤ eps k)
    (hP : ∀ e, vecNorm2 (rectMatMulVec P e) ≤ cP * vecNorm2 e) :
    vecNorm2
        (firstOrderSelectedOutputError P
          (firstOrderForwardError p d J localErr)) ≤
      cP * firstOrderForwardBudget p c eps := by
  have hacc :=
    firstOrderForwardError_vecNorm2_le_budget p d J localErr c eps hc hJ hlocal
  calc
    vecNorm2
        (firstOrderSelectedOutputError P
          (firstOrderForwardError p d J localErr))
        ≤ cP * vecNorm2 (firstOrderForwardError p d J localErr) := by
          simpa [firstOrderSelectedOutputError] using
            hP (firstOrderForwardError p d J localErr)
    _ ≤ cP * firstOrderForwardBudget p c eps :=
          mul_le_mul_of_nonneg_left hacc hP_nonneg

/-- The first-order backward-error equation `J_f Delta a = e`.

Here `J_f` is the Jacobian of the mathematical problem `f` at the input, `e` is
the observed first-order forward error, and `Delta a` is a candidate data
perturbation. -/
def firstOrderBackwardEquation {n m : ℕ}
    (Jf : Fin m → Fin n → ℝ) (forwardError : Fin m → ℝ)
    (DeltaA : Fin n → ℝ) : Prop :=
  rectMatMulVec Jf DeltaA = forwardError

/-- A norm-minimal solution of the first-order backward equation. -/
def IsMinimumNormFirstOrderBackwardSolution {n m : ℕ}
    (normIn : (Fin n → ℝ) → ℝ)
    (Jf : Fin m → Fin n → ℝ) (forwardError : Fin m → ℝ)
    (DeltaA : Fin n → ℝ) : Prop :=
  firstOrderBackwardEquation Jf forwardError DeltaA ∧
    ∀ DeltaA' : Fin n → ℝ,
      firstOrderBackwardEquation Jf forwardError DeltaA' →
        normIn DeltaA ≤ normIn DeltaA'

/-- Componentwise relative backward feasibility `|Delta a_i| <= c |a_i|`. -/
def ComponentwiseFirstOrderBackwardFeasible {n : ℕ}
    (a DeltaA : Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ i : Fin n, |DeltaA i| ≤ c * |a i|

/-- A componentwise-minimal scale for a first-order backward explanation. -/
def IsMinimumComponentwiseFirstOrderBackwardScale {n m : ℕ}
    (a : Fin n → ℝ) (Jf : Fin m → Fin n → ℝ)
    (forwardError : Fin m → ℝ) (DeltaA : Fin n → ℝ) (c : ℝ) : Prop :=
  firstOrderBackwardEquation Jf forwardError DeltaA ∧
    ComponentwiseFirstOrderBackwardFeasible a DeltaA c ∧
    ∀ (c' : ℝ) (DeltaA' : Fin n → ℝ),
      firstOrderBackwardEquation Jf forwardError DeltaA' →
        ComponentwiseFirstOrderBackwardFeasible a DeltaA' c' →
          c ≤ c'

/-- Any minimum-norm first-order backward solution is, in particular, a solution
of the linearized backward equation. -/
theorem firstOrderBackward_minimumNorm_solution {n m : ℕ}
    (normIn : (Fin n → ℝ) → ℝ)
    (Jf : Fin m → Fin n → ℝ) (forwardError : Fin m → ℝ)
    (DeltaA : Fin n → ℝ)
    (hmin : IsMinimumNormFirstOrderBackwardSolution normIn Jf forwardError DeltaA) :
    firstOrderBackwardEquation Jf forwardError DeltaA :=
  hmin.1

/-- Any minimum componentwise first-order backward scale supplies a data
perturbation explaining the forward error and satisfying its scale bound. -/
theorem firstOrderBackward_minimumComponentwise_solution {n m : ℕ}
    (a : Fin n → ℝ) (Jf : Fin m → Fin n → ℝ)
    (forwardError : Fin m → ℝ) (DeltaA : Fin n → ℝ) (c : ℝ)
    (hmin : IsMinimumComponentwiseFirstOrderBackwardScale
      a Jf forwardError DeltaA c) :
    firstOrderBackwardEquation Jf forwardError DeltaA ∧
      ComponentwiseFirstOrderBackwardFeasible a DeltaA c :=
  ⟨hmin.1, hmin.2.1⟩

end NumStability
