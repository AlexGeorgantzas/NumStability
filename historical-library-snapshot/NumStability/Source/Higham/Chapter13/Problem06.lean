import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory

/-!
# Source.Higham.Chapter13.Problem06

This module formalizes the source-facing Chapter 13 statements for
`Problem06`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    rank-one matrix perturbation that maps the computed solution to a given
    single-right-hand-side residual.

    The printed exercise asks for a perturbation `ΔA` satisfying
    `(A + ΔA)x̂ = b`.  This local construction supplies the exact algebraic
    witness used to absorb the triangular-solve residual into `ΔA`, under the
    necessary domain condition that one component of `x̂` is nonzero. -/
noncomputable def higham13_problem13_6_residualRankOneDelta {n : Type*} [DecidableEq n]
    (rsolve xhat : n → ℝ) (j0 : n) : Matrix n n ℝ :=
  fun i j => if j = j0 then rsolve i / xhat j0 else 0

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    the rank-one residual perturbation sends `x̂` to the solve residual. -/
theorem higham13_problem13_6_residualRankOneDelta_mulVec {n : Type*}
    [Fintype n] [DecidableEq n]
    (rsolve xhat : n → ℝ) (j0 : n) (hx : xhat j0 ≠ 0) :
    higham13_problem13_6_residualRankOneDelta rsolve xhat j0 *ᵥ xhat =
      rsolve := by
  ext i
  simp [Matrix.mulVec, dotProduct,
    higham13_problem13_6_residualRankOneDelta, hx]

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    exact single-right-hand-side backward-error identity.

    If the computed factors satisfy `L̂Û = A + ΔA_fact` and the triangular
    solve leaves vector residual `(L̂Û)x̂ = b + r`, then the corrected
    perturbation `ΔA_fact - E`, where `E x̂ = r`, gives
    `(A + (ΔA_fact - E))x̂ = b`.  The rank-one construction above supplies the
    explicit `E` whenever `x̂` has a nonzero component. -/
theorem higham13_problem13_6_single_rhs_backward_error_identity {n : Type*}
    [Fintype n] [DecidableEq n]
    (A DeltaFact Lhat Uhat : Matrix n n ℝ) (xhat b rsolve : n → ℝ)
    (hLU : Lhat * Uhat = A + DeltaFact)
    (hSolve : (Lhat * Uhat) *ᵥ xhat = b + rsolve)
    (j0 : n) (hx : xhat j0 ≠ 0) :
    (A + (DeltaFact -
        higham13_problem13_6_residualRankOneDelta rsolve xhat j0)) *ᵥ xhat =
      b := by
  ext i
  have hdelta := congrFun
    (higham13_problem13_6_residualRankOneDelta_mulVec rsolve xhat j0 hx) i
  have hlu_vec : (A + DeltaFact) *ᵥ xhat = b + rsolve := by
    rw [← hLU]
    exact hSolve
  have hlu_i := congrFun hlu_vec i
  simp [Matrix.add_mulVec, Matrix.sub_mulVec, hdelta] at hlu_i ⊢
  linarith

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    existential form of the single-right-hand-side backward-error equation.

    This closes the exact algebraic construction of a matrix perturbation from
    a factorization perturbation and a triangular-solve residual, conditional
    on the necessary nonzero computed-solution component.  The norm bound for
    the constructed perturbation remains the separate first-order estimate
    recorded in the chapter inventory. -/
theorem higham13_problem13_6_single_rhs_backward_error_exists {n : Type*}
    [Fintype n] [DecidableEq n]
    (A DeltaFact Lhat Uhat : Matrix n n ℝ) (xhat b rsolve : n → ℝ)
    (hLU : Lhat * Uhat = A + DeltaFact)
    (hSolve : (Lhat * Uhat) *ᵥ xhat = b + rsolve)
    (hx : ∃ j0 : n, xhat j0 ≠ 0) :
    ∃ DeltaA : Matrix n n ℝ, (A + DeltaA) *ᵥ xhat = b := by
  rcases hx with ⟨j0, hj0⟩
  refine ⟨DeltaFact -
      higham13_problem13_6_residualRankOneDelta rsolve xhat j0, ?_⟩
  exact higham13_problem13_6_single_rhs_backward_error_identity
    A DeltaFact Lhat Uhat xhat b rsolve hLU hSolve j0 hj0

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    Frobenius norm of the standard residual rank-one perturbation.

    This is a source-facing reuse of the existing residual perturbation
    infrastructure (`ΔA = r x̂ᵀ / (x̂ᵀ x̂)`) from the linear-system
    perturbation theory files. -/
theorem higham13_problem13_6_residualRankOnePerturbation_frobNorm (n : ℕ)
    (rsolve xhat : Fin n → ℝ) (hx : vecNorm2 xhat ≠ 0) :
    frobNorm (residualRankOnePerturbation n rsolve xhat) =
      vecNorm2 rsolve / vecNorm2 xhat :=
  frobNorm_residualRankOnePerturbation n rsolve xhat hx

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    operator 2-norm certificate for the standard residual rank-one
    perturbation.

    This is the operator-norm counterpart of
    `higham13_problem13_6_residualRankOnePerturbation_frobNorm`, reusing the
    existing Higham Lemma 1.1 residual perturbation infrastructure. -/
theorem higham13_problem13_6_residualRankOnePerturbation_opNorm2Le (n : ℕ)
    (rsolve xhat : Fin n → ℝ) (hx : vecNorm2 xhat ≠ 0) :
    opNorm2Le (residualRankOnePerturbation n rsolve xhat)
      (vecNorm2 rsolve / vecNorm2 xhat) :=
  opNorm2Le_residualRankOnePerturbation n rsolve xhat hx

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    exact single-right-hand-side backward-error identity using the Frobenius
    rank-one perturbation from the existing residual theory.

    This is the function-shaped `Fin n` counterpart of
    `higham13_problem13_6_single_rhs_backward_error_identity`, using
    `residualRankOnePerturbation` so the same correction has the norm formula
    above. -/
theorem higham13_problem13_6_single_rhs_backward_error_frobenius_identity
    (n : ℕ)
    (A DeltaFact Lhat Uhat : Fin n → Fin n → ℝ) (xhat b rsolve : Fin n → ℝ)
    (hLU : matMul n Lhat Uhat = fun i j => A i j + DeltaFact i j)
    (hSolve : matMulVec n (matMul n Lhat Uhat) xhat =
      fun i => b i + rsolve i)
    (hx : vecNorm2 xhat ≠ 0) :
    let DeltaA :=
      fun i j => DeltaFact i j - residualRankOnePerturbation n rsolve xhat i j
    matMulVec n (fun i j => A i j + DeltaA i j) xhat = b := by
  intro DeltaA
  ext i
  have hdelta := congrFun (residualRankOnePerturbation_mul_vec n rsolve xhat hx) i
  have hlu_vec :
      matMulVec n (fun i j => A i j + DeltaFact i j) xhat =
        fun i => b i + rsolve i := by
    rw [← hLU]
    exact hSolve
  have hlu_i := congrFun hlu_vec i
  simp [matMulVec, DeltaA, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at hdelta hlu_i ⊢
  linarith

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    first-order Frobenius bound for the residual rank-one correction.

    If the single-right-hand-side triangular solve residual is bounded by
    `c_s u (‖A‖ + ‖L̂‖‖Û‖) ‖x̂‖₂ + O(u²)`, then the standard rank-one
    correction `r x̂ᵀ/(x̂ᵀx̂)` has Frobenius norm bounded by
    `c_s u (‖A‖ + ‖L̂‖‖Û‖) + O(u²)`. -/
theorem higham13_problem13_6_residualRankOnePerturbation_frobNorm_firstOrder
    (n : ℕ) (rsolve xhat : Fin n → ℝ)
    (normA normL normU u cSolve : ℝ)
    (hx : vecNorm2 xhat ≠ 0)
    (hResidual : FirstOrderLe u
      (cSolve * u * (normA + normL * normU) * vecNorm2 xhat)
      (vecNorm2 rsolve)) :
    FirstOrderLe u
      (cSolve * u * (normA + normL * normU))
      (frobNorm (residualRankOnePerturbation n rsolve xhat)) := by
  have hxpos : 0 < vecNorm2 xhat :=
    lt_of_le_of_ne (vecNorm2_nonneg xhat) (Ne.symm hx)
  have hxinv_nonneg : 0 ≤ (vecNorm2 xhat)⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
  have hscaled :
      FirstOrderLe u
        ((cSolve * u * (normA + normL * normU) * vecNorm2 xhat) *
          (vecNorm2 xhat)⁻¹)
        (vecNorm2 rsolve * (vecNorm2 xhat)⁻¹) :=
    FirstOrderLe.bound_mul_nonneg_right hResidual hxinv_nonneg le_rfl
  have hleading :
      (cSolve * u * (normA + normL * normU) * vecNorm2 xhat) *
          (vecNorm2 xhat)⁻¹ =
        cSolve * u * (normA + normL * normU) := by
    field_simp [ne_of_gt hxpos]
  have hvalue :
      frobNorm (residualRankOnePerturbation n rsolve xhat) =
        vecNorm2 rsolve * (vecNorm2 xhat)⁻¹ := by
    rw [higham13_problem13_6_residualRankOnePerturbation_frobNorm n rsolve xhat hx]
    rw [div_eq_mul_inv]
  rw [hvalue]
  exact hscaled.mono_leading (le_of_eq hleading)

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    first-order operator 2-norm certificate for the residual rank-one
    correction.

    If the single-right-hand-side triangular-solve residual is bounded by
    `c_s u (‖A‖ + ‖L̂‖‖Û‖) ‖x̂‖₂ + O(u²)`, then the rank-one correction has an
    operator 2-norm upper bound whose first-order leading term is
    `c_s u (‖A‖ + ‖L̂‖‖Û‖)`. -/
theorem higham13_problem13_6_residualRankOnePerturbation_opNorm2Le_firstOrder
    (n : ℕ) (rsolve xhat : Fin n → ℝ)
    (normA normL normU u cSolve : ℝ)
    (hx : vecNorm2 xhat ≠ 0)
    (hResidual : FirstOrderLe u
      (cSolve * u * (normA + normL * normU) * vecNorm2 xhat)
      (vecNorm2 rsolve)) :
    ∃ opBound : ℝ,
      FirstOrderLe u (cSolve * u * (normA + normL * normU)) opBound ∧
      opNorm2Le (residualRankOnePerturbation n rsolve xhat) opBound := by
  refine ⟨vecNorm2 rsolve / vecNorm2 xhat, ?_, ?_⟩
  · have hxpos : 0 < vecNorm2 xhat :=
      lt_of_le_of_ne (vecNorm2_nonneg xhat) (Ne.symm hx)
    have hxinv_nonneg : 0 ≤ (vecNorm2 xhat)⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
    have hscaled :
        FirstOrderLe u
          ((cSolve * u * (normA + normL * normU) * vecNorm2 xhat) *
            (vecNorm2 xhat)⁻¹)
          (vecNorm2 rsolve * (vecNorm2 xhat)⁻¹) :=
      FirstOrderLe.bound_mul_nonneg_right hResidual hxinv_nonneg le_rfl
    have hleading :
        (cSolve * u * (normA + normL * normU) * vecNorm2 xhat) *
            (vecNorm2 xhat)⁻¹ =
          cSolve * u * (normA + normL * normU) := by
      field_simp [ne_of_gt hxpos]
    simpa [div_eq_mul_inv] using hscaled.mono_leading (le_of_eq hleading)
  · exact higham13_problem13_6_residualRankOnePerturbation_opNorm2Le n rsolve xhat hx

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    scalar first-order Frobenius aggregation for the single-RHS perturbation.

    The theorem combines a Theorem 13.5-style factorization perturbation budget
    with the rank-one solve-residual correction above.  The hypothesis
    `normDeltaTotal ≤ normDeltaFact + frobNorm E` is the norm triangle
    inequality for the final perturbation `ΔA_fact - E`; the exact equation is
    supplied by `higham13_problem13_6_single_rhs_backward_error_frobenius_identity`. -/
theorem higham13_problem13_6_single_rhs_backward_error_frobenius_firstOrder
    (n : ℕ) (rsolve xhat : Fin n → ℝ)
    (normDeltaFact normDeltaTotal normA normL normU u cFact cSolve cₙ : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hx : vecNorm2 xhat ≠ 0)
    (hc : cFact + cSolve ≤ cₙ)
    (hFact : FirstOrderLe u (cFact * u * (normA + normL * normU)) normDeltaFact)
    (hResidual : FirstOrderLe u
      (cSolve * u * (normA + normL * normU) * vecNorm2 xhat)
      (vecNorm2 rsolve))
    (hTotal : normDeltaTotal ≤ normDeltaFact +
      frobNorm (residualRankOnePerturbation n rsolve xhat)) :
    FirstOrderLe u
      (cₙ * u * (normA + normL * normU))
      normDeltaTotal := by
  have hSolveDelta :=
    higham13_problem13_6_residualRankOnePerturbation_frobNorm_firstOrder
      n rsolve xhat normA normL normU u cSolve hx hResidual
  have hsum := FirstOrderLe.add hFact hSolveDelta hTotal
  refine hsum.mono_leading ?_
  have hS : 0 ≤ normA + normL * normU := by linarith [mul_nonneg hL hU]
  have hP : 0 ≤ u * (normA + normL * normU) := mul_nonneg hu hS
  nlinarith [mul_le_mul_of_nonneg_right hc hP]

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    exact multiple-right-hand-side residual identity.

    If the computed factors satisfy `L̂Û = A + ΔA`, and the triangular solves
    leave the residual `(L̂Û) X̂ = B + R`, then the source residual is
    `A X̂ - B = R - ΔA X̂`.  This is the algebraic core behind the displayed
    multiple-RHS residual bound in Problem 13.6. -/
theorem higham13_problem13_6_multiple_rhs_residual_identity {n p : Type*}
    [Fintype n] [Fintype p]
    (A DeltaA Lhat Uhat : Matrix n n ℝ) (Xhat B Rsolve : Matrix n p ℝ)
    (hLU : Lhat * Uhat = A + DeltaA)
    (hSolve : (Lhat * Uhat) * Xhat = B + Rsolve) :
    A * Xhat - B = Rsolve - DeltaA * Xhat := by
  calc
    A * Xhat - B = (A + DeltaA) * Xhat - DeltaA * Xhat - B := by
      rw [Matrix.add_mul]
      abel
    _ = (Lhat * Uhat) * Xhat - DeltaA * Xhat - B := by rw [← hLU]
    _ = (B + Rsolve) - DeltaA * Xhat - B := by rw [hSolve]
    _ = Rsolve - DeltaA * Xhat := by abel

/-- Higham, 2nd ed., Chapter 13, Problem 13.6:
    scalar first-order aggregation for the multiple-right-hand-side residual.

    The hypotheses are the source proof obligations: a Theorem 13.5-style
    factorization perturbation bound, a triangular-solve residual bound for
    multiple right-hand sides, and a norm estimate
    `‖A X̂ - B‖ ≤ ‖R‖ + ‖ΔA‖ ‖X̂‖` obtained from the exact identity above.
    The conclusion is the displayed Problem 13.6 residual bound with an
    explicit `+ O(u^2)` witness. -/
theorem higham13_problem13_6_multiple_rhs_residual_firstOrder
    (normResidual normSolveResidual normDeltaA normA normL normU normXhat
      u cΔ cSolve cₙ : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hX : 0 ≤ normXhat)
    (hc : cSolve + cΔ ≤ cₙ)
    (hDelta : FirstOrderLe u (cΔ * u * (normA + normL * normU)) normDeltaA)
    (hSolve : FirstOrderLe u
      (cSolve * u * (normA + normL * normU) * normXhat) normSolveResidual)
    (hResidual : normResidual ≤ normSolveResidual + normDeltaA * normXhat) :
    FirstOrderLe u
      (cₙ * u * (normA + normL * normU) * normXhat)
      normResidual := by
  have hDeltaX :
      FirstOrderLe u
        ((cΔ * u * (normA + normL * normU)) * normXhat)
        (normDeltaA * normXhat) :=
    FirstOrderLe.bound_mul_nonneg_right hDelta hX le_rfl
  have hsum := FirstOrderLe.add hSolve hDeltaX hResidual
  refine hsum.mono_leading ?_
  have hS : 0 ≤ normA + normL * normU := by linarith [mul_nonneg hL hU]
  have hP : 0 ≤ u * (normA + normL * normU) * normXhat := by
    exact mul_nonneg (mul_nonneg hu hS) hX
  nlinarith [mul_le_mul_of_nonneg_right hc hP]

end NumStability
