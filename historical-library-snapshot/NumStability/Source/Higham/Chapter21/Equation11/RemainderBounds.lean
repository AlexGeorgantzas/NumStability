import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation11.UnderdeterminedSolve

/-!
# Source.Higham.Chapter21.Equation11.RemainderBounds

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Uniform local bounds for the signed SNE higher-order terms.



namespace NumStability

open scoped BigOperators

set_option maxHeartbeats 1200000



























































































































































































































































































































































































































































































































































































































































































/-- The explicit finite remainder in equation (21.11) is uniformly quadratic
once the matrix perturbation, dual displacement, and forward displacement are
each first order.  The coefficient is expanded in primitive Frobenius norms
and contains no division by the active radius. -/
theorem higham21_eq21_11_finite_remainder_vecNorm2_le_radius
    {m n : Nat}
    (eta KF Ky Kx : Real)
    (heta : 0 <= eta) (hKF : 0 <= KF) (_hKy : 0 <= Ky) (_hKx : 0 <= Kx)
    (A F : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (xhat : Fin n -> Real) (yhat : Fin m -> Real)
    (hF : frobNorm F <= eta * KF)
    (hy :
      let Aplus := undetAplusOfGramNonsingInv A
      let x := rectMatMulVec Aplus b
      let y := rectTransposeMulVec Aplus x
      vecNorm2 (fun i => yhat i - y i) <= eta * Ky)
    (hx :
      let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
      vecNorm2 (fun j => xhat j - x j) <= eta * Kx) :
    vecNorm2 (higham21Eq21_11FiniteRemainder A F b xhat yhat) <=
      eta ^ 2 *
        (KF *
          ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * Ky +
            frobNorm (undetAplusOfGramNonsingInv A) * Kx)) := by
  dsimp only at hy hx
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let y : Fin m -> Real := rectTransposeMulVec Aplus x
  let dy : Fin m -> Real := fun i => yhat i - y i
  let dx : Fin n -> Real := fun j => xhat j - x j
  let dualTerm : Fin n -> Real := rectTransposeMulVec F dy
  let projected : Fin n -> Real :=
    rectMatMulVec Aplus (rectMatMulVec A dualTerm)
  let forwardTerm : Fin n -> Real :=
    rectMatMulVec Aplus (rectMatMulVec F dx)
  have hdy : vecNorm2 dy <= eta * Ky := by simpa [dy, y, x, Aplus] using hy
  have hdx : vecNorm2 dx <= eta * Kx := by simpa [dx, x, Aplus] using hx
  have hdualTerm : vecNorm2 dualTerm <= eta ^ 2 * (KF * Ky) := by
    calc
      vecNorm2 dualTerm <=
          frobNormRect (finiteTranspose F) * vecNorm2 dy := by
        simpa [dualTerm, rectTransposeMulVec] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul (finiteTranspose F) dy
      _ = frobNorm F * vecNorm2 dy := by
        rw [frobNormRect_finiteTranspose, frobNormRect_eq_frobNormFn]
      _ <= (eta * KF) * (eta * Ky) :=
        mul_le_mul hF hdy (vecNorm2_nonneg _)
          (mul_nonneg heta hKF)
      _ = eta ^ 2 * (KF * Ky) := by ring
  have hprojected : vecNorm2 projected <=
      eta ^ 2 *
        (frobNorm Aplus * frobNorm A * (KF * Ky)) := by
    calc
      vecNorm2 projected <=
          frobNormRect Aplus * vecNorm2 (rectMatMulVec A dualTerm) := by
        simpa [projected] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul Aplus
            (rectMatMulVec A dualTerm)
      _ = frobNorm Aplus * vecNorm2 (rectMatMulVec A dualTerm) := by
        rw [frobNormRect_eq_frobNormFn]
      _ <= frobNorm Aplus * (frobNormRect A * vecNorm2 dualTerm) :=
        mul_le_mul_of_nonneg_left
          (vecNorm2_rectMatMulVec_le_frobNormRect_mul A dualTerm)
          (frobNorm_nonneg Aplus)
      _ = frobNorm Aplus * (frobNorm A * vecNorm2 dualTerm) := by
        rw [frobNormRect_eq_frobNormFn]
      _ <= frobNorm Aplus *
          (frobNorm A * (eta ^ 2 * (KF * Ky))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdualTerm (frobNorm_nonneg A))
          (frobNorm_nonneg Aplus)
      _ = eta ^ 2 *
          (frobNorm Aplus * frobNorm A * (KF * Ky)) := by ring
  have hFdx : vecNorm2 (rectMatMulVec F dx) <=
      eta ^ 2 * (KF * Kx) := by
    calc
      vecNorm2 (rectMatMulVec F dx) <= frobNormRect F * vecNorm2 dx :=
        vecNorm2_rectMatMulVec_le_frobNormRect_mul F dx
      _ = frobNorm F * vecNorm2 dx := by rw [frobNormRect_eq_frobNormFn]
      _ <= (eta * KF) * (eta * Kx) :=
        mul_le_mul hF hdx (vecNorm2_nonneg _)
          (mul_nonneg heta hKF)
      _ = eta ^ 2 * (KF * Kx) := by ring
  have hforwardTerm : vecNorm2 forwardTerm <=
      eta ^ 2 * (frobNorm Aplus * (KF * Kx)) := by
    calc
      vecNorm2 forwardTerm <=
          frobNormRect Aplus * vecNorm2 (rectMatMulVec F dx) := by
        simpa [forwardTerm] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul Aplus
            (rectMatMulVec F dx)
      _ = frobNorm Aplus * vecNorm2 (rectMatMulVec F dx) := by
        rw [frobNormRect_eq_frobNormFn]
      _ <= frobNorm Aplus * (eta ^ 2 * (KF * Kx)) :=
        mul_le_mul_of_nonneg_left hFdx (frobNorm_nonneg Aplus)
      _ = eta ^ 2 * (frobNorm Aplus * (KF * Kx)) := by ring
  have hshape :
      higham21Eq21_11FiniteRemainder A F b xhat yhat =
        fun j => (dualTerm j - projected j) - forwardTerm j := by
    rfl
  have htri1 : vecNorm2 (fun j => dualTerm j - projected j) <=
      vecNorm2 dualTerm + vecNorm2 projected := by
    simpa [sub_eq_add_neg, vecNorm2_neg] using
      vecNorm2_add_le dualTerm (fun j => -projected j)
  have htri2 :
      vecNorm2 (fun j => (dualTerm j - projected j) - forwardTerm j) <=
        vecNorm2 (fun j => dualTerm j - projected j) +
          vecNorm2 forwardTerm := by
    simpa [sub_eq_add_neg, vecNorm2_neg] using
      vecNorm2_add_le (fun j => dualTerm j - projected j)
        (fun j => -forwardTerm j)
  rw [hshape]
  calc
    vecNorm2 (fun j => (dualTerm j - projected j) - forwardTerm j) <=
        vecNorm2 (fun j => dualTerm j - projected j) +
          vecNorm2 forwardTerm := htri2
    _ <= (vecNorm2 dualTerm + vecNorm2 projected) +
          vecNorm2 forwardTerm := add_le_add htri1 le_rfl
    _ <= (eta ^ 2 * (KF * Ky) +
          eta ^ 2 * (frobNorm Aplus * frobNorm A * (KF * Ky))) +
          eta ^ 2 * (frobNorm Aplus * (KF * Kx)) :=
      add_le_add (add_le_add hdualTerm hprojected) hforwardTerm
    _ = eta ^ 2 *
        (KF *
          ((1 + frobNorm Aplus * frobNorm A) * Ky +
            frobNorm Aplus * Kx)) := by ring
    _ = eta ^ 2 *
        (KF *
          ((1 + frobNorm (undetAplusOfGramNonsingInv A) * frobNorm A) * Ky +
            frobNorm (undetAplusOfGramNonsingInv A) * Kx)) := by
      rfl

end NumStability
