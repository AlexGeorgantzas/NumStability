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
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.ComputedOutput.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.Forward
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.EnvelopeTransfer
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.ActualOutput

/-!
# Source.Higham.Chapter21.Theorem04.SeminormalEquations.EnvelopeTransfer

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Transfer of the SNE factor envelope through a QR factorization of A^T.



namespace NumStability

open scoped BigOperators

/-!
# SNE envelope transfer

The aggregate SNE theorem bounds its Gram perturbation by

  `eta * |R_hat^T| |R_hat|`.

The declarations below transport this quantity through the componentwise
Householder-QR certificate for `A^T`.  They deliberately stop at an explicit
source-data majorant.  Demmel--Higham's sharper first-order argument
(equations (3.17)--(3.20) of their 1993 paper) keeps the two triangular
perturbations separate and cancels QR factors before taking absolute values.
That cancellation is no longer present in `higham21SNEForwardEnvelope`, which
already contains `|(A A^T)^-1|`.

`Higham21SNEAggregateQRMajorantCond2Bridge` names the stronger aggregate
estimate that would be needed to fill the existing `hTransferred` premise by
this route.  It is intentionally an explicit proposition, not a claimed
consequence of the QR certificate.  The split triangular-solve certificate
retaining `DeltaR1` and `DeltaR2` is recovered below.  The genuinely missing
upstream input for the printed coefficient is the factorwise QR-cancellation
estimate consuming that certificate, corresponding to Demmel--Higham (3.18)
and (3.20).
-/



















































































































































































































































































































































































































































/-- The split factorwise transfer input is sufficient for the complete rounded
    SNE output.  Since `gamma_m <= eta`, expanding the right side gives the
    printed `(m + k) * eta * cond2(A)` first-order coefficient and a quadratic
    remainder, exactly as in the arithmetic endpoint of
    `Higham21SNEActualOutput`. -/
theorem higham21_sne_actual_output_error_of_split_factorwise_transfer
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real) (C : Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hm1 : gammaValid fp (m + 1))
    (hSplit : Higham21SNESplitFactorwiseCond2TransferInput
      fp A AAT_inv R_hat b y C) :
    let eta := Higham21SNEBackwardCoefficient fp m
    let x_hat := higham21SNEActualOutput fp m (m + k) A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    vecNorm2 (fun j => x_hat j - x j) <=
      gamma fp m * higham21Cond2With A Aplus * vecNorm2 x +
        (1 + gamma fp m) *
          (((m + k : Real) - 1) * eta *
              higham21Cond2With A Aplus * vecNorm2 x +
            eta ^ 2 * C) := by
  dsimp only [Higham21SNESplitFactorwiseCond2TransferInput] at hSplit ⊢
  obtain ⟨splitEnvelope, hcomponentwise, hTransferred⟩ := hSplit
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hRight :
      rectMatMul A (undetAplusOfGramInv A AAT_inv) = idMatrix m :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_inverse
      A (rectGram A) AAT_inv (by intro i j; rfl) hInv
  have hOutput :=
    higham21_sne_fl_transpose_forward_error_of_componentwise
      fp A (undetAplusOfGramInv A AAT_inv) y
        (higham21SNEComputedNormalSolution fp m R_hat b) splitEnvelope
        hRight hm hcomponentwise
  have hone_gamma_nonneg : 0 <= 1 + gamma fp m := by
    linarith [gamma_nonneg fp hm]
  have hOutput' := hOutput.trans
    (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left hTransferred hone_gamma_nonneg))
  simpa [higham21SNEActualOutput] using hOutput'

/-- Printed quadratic endpoint obtained from the source-faithful split
    factorwise transfer input.  This avoids asserting the generally stronger
    bound on the pre-existing aggregate SNE envelope. -/
theorem higham21_sne_actual_output_relative_error_quadratic_of_split_factorwise_transfer
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real) (C : Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hm1 : gammaValid fp (m + 1))
    (hn : 0 < m + k) (hC : 0 <= C)
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y))
    (hSplit : Higham21SNESplitFactorwiseCond2TransferInput
      fp A AAT_inv R_hat b y C) :
    let eta := Higham21SNEBackwardCoefficient fp m
    let x_hat := higham21SNEActualOutput fp m (m + k) A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      (m + k : Real) * eta * higham21Cond2With A Aplus +
        eta ^ 2 *
          (((m + k : Real) - 1) * higham21Cond2With A Aplus *
              vecNorm2 x +
            (1 + eta) * C) / vecNorm2 x := by
  have hAbsolute :=
    higham21_sne_actual_output_error_of_split_factorwise_transfer
      fp A AAT_inv R_hat b y C hInv hm1 hSplit
  dsimp only at hAbsolute ⊢
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hgamma_nonneg : 0 <= gamma fp m := gamma_nonneg fp hm
  have heta : 0 <= Higham21SNEBackwardCoefficient fp m :=
    Higham21SNEBackwardCoefficient_nonneg_of_gammaValid fp m hm1
  have hgamma_le :
      gamma fp m <= Higham21SNEBackwardCoefficient fp m :=
    gamma_le_Higham21SNEBackwardCoefficient fp m hm1
  have hcond_nonneg :
      0 <= higham21Cond2With A (undetAplusOfGramInv A AAT_inv) :=
    higham21Cond2With_nonneg A (undetAplusOfGramInv A AAT_inv)
  have hxnorm_nonneg : 0 <= vecNorm2 (rectTransposeMulVec A y) :=
    vecNorm2_nonneg _
  have hn_real : (1 : Real) <= (m + k : Real) := by
    exact_mod_cast hn
  have hdim_nonneg : 0 <= (m + k : Real) - 1 := sub_nonneg.mpr hn_real
  have hbudget_nonneg :
      0 <= ((m + k : Real) - 1) *
            Higham21SNEBackwardCoefficient fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
          Higham21SNEBackwardCoefficient fp m ^ 2 * C := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hdim_nonneg heta) hcond_nonneg)
        hxnorm_nonneg)
      (mul_nonneg
        (sq_nonneg (Higham21SNEBackwardCoefficient fp m)) hC)
  have hlead :
      gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) <=
        Higham21SNEBackwardCoefficient fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgamma_le hcond_nonneg) hxnorm_nonneg
  have hone_le :
      1 + gamma fp m <= 1 + Higham21SNEBackwardCoefficient fp m := by
    linarith
  have hscaledBudget :
      (1 + gamma fp m) *
          (((m + k : Real) - 1) *
              Higham21SNEBackwardCoefficient fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            Higham21SNEBackwardCoefficient fp m ^ 2 * C) <=
        (1 + Higham21SNEBackwardCoefficient fp m) *
          (((m + k : Real) - 1) *
              Higham21SNEBackwardCoefficient fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            Higham21SNEBackwardCoefficient fp m ^ 2 * C) :=
    mul_le_mul_of_nonneg_right hone_le hbudget_nonneg
  have hAbsoluteShape :
      vecNorm2 (fun j =>
          higham21SNEActualOutput fp m (m + k) A R_hat b j -
            rectTransposeMulVec A y j) <=
        (m + k : Real) * Higham21SNEBackwardCoefficient fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
          Higham21SNEBackwardCoefficient fp m ^ 2 *
            (((m + k : Real) - 1) *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
              (1 + Higham21SNEBackwardCoefficient fp m) * C) := by
    calc
      vecNorm2 (fun j =>
          higham21SNEActualOutput fp m (m + k) A R_hat b j -
            rectTransposeMulVec A y j) <=
          gamma fp m *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
            (1 + gamma fp m) *
              (((m + k : Real) - 1) *
                  Higham21SNEBackwardCoefficient fp m *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) +
                Higham21SNEBackwardCoefficient fp m ^ 2 * C) := hAbsolute
      _ <= Higham21SNEBackwardCoefficient fp m *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
            (1 + Higham21SNEBackwardCoefficient fp m) *
              (((m + k : Real) - 1) *
                  Higham21SNEBackwardCoefficient fp m *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) +
                Higham21SNEBackwardCoefficient fp m ^ 2 * C) :=
        add_le_add hlead hscaledBudget
      _ = (m + k : Real) * Higham21SNEBackwardCoefficient fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
          Higham21SNEBackwardCoefficient fp m ^ 2 *
            (((m + k : Real) - 1) *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
              (1 + Higham21SNEBackwardCoefficient fp m) * C) := by
        ring
  have hxne : vecNorm2 (rectTransposeMulVec A y) ≠ 0 := ne_of_gt hx
  calc
    vecNorm2 (fun j =>
        higham21SNEActualOutput fp m (m + k) A R_hat b j -
          rectTransposeMulVec A y j) /
          vecNorm2 (rectTransposeMulVec A y) <=
      ((m + k : Real) * Higham21SNEBackwardCoefficient fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
          Higham21SNEBackwardCoefficient fp m ^ 2 *
            (((m + k : Real) - 1) *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
              (1 + Higham21SNEBackwardCoefficient fp m) * C)) /
        vecNorm2 (rectTransposeMulVec A y) :=
      div_le_div_of_nonneg_right hAbsoluteShape (le_of_lt hx)
    _ = (m + k : Real) * Higham21SNEBackwardCoefficient fp m *
          higham21Cond2With A (undetAplusOfGramInv A AAT_inv) +
        Higham21SNEBackwardCoefficient fp m ^ 2 *
          (((m + k : Real) - 1) *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            (1 + Higham21SNEBackwardCoefficient fp m) * C) /
          vecNorm2 (rectTransposeMulVec A y) := by
      field_simp [hxne]




































































end NumStability
