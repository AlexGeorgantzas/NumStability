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
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Forward

/-!
# Source.Higham.Chapter21.Equation11.ActualOutput

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The final transpose action and forward-error composition for the SNE method.




namespace NumStability

open scoped BigOperators









































































































































































































































































































































/-- Equation (21.11), SNE side, for the complete computed output.  This is the
    strongest unconditional relative 2-norm statement supplied by the current
    SNE backward-error infrastructure: the rounded final formation contributes
    `gamma_m * cond2(A)`, while the normal-solve error remains as the explicit
    transferred finite envelope. -/
theorem higham21_eq21_11_sne_actual_output_relative_forward_error_envelope
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hExact : forall i, matMulVec m (rectGram A) y i = b i)
    (hR_diag : forall i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m (rectGram A) R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y)) :
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    let x_hat := higham21SNEActualOutput fp m n A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    let envelope := higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      gamma fp m * higham21Cond2With A Aplus +
        (1 + gamma fp m) *
          vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) /
            vecNorm2 x := by
  dsimp only
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hRight :
      rectMatMul A (undetAplusOfGramInv A AAT_inv) = idMatrix m :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_inverse
      A (rectGram A) AAT_inv (by intro i j; rfl) hInv
  have hCore :=
    higham21_sne_computed_forward_error fp m (rectGram A) AAT_inv R_hat
      b y hInv hExact hR_diag hChol hm1
  dsimp only at hCore
  obtain ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm⟩ := hCore
  have hAbsolute :=
    higham21_sne_fl_transpose_forward_error_of_componentwise fp A
      (undetAplusOfGramInv A AAT_inv) y
      (higham21SNEComputedNormalSolution fp m R_hat b)
      (higham21SNEForwardEnvelope fp m AAT_inv R_hat
        (higham21SNEComputedNormalSolution fp m R_hat b))
      hRight hm hEnvelope
  have hxne : vecNorm2 (rectTransposeMulVec A y) ≠ 0 := ne_of_gt hx
  calc
    vecNorm2 (fun j => higham21SNEActualOutput fp m n A R_hat b j -
        rectTransposeMulVec A y j) /
        vecNorm2 (rectTransposeMulVec A y) <=
      (gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
          (1 + gamma fp m) *
            vecNorm2
              (rectTransposeMulVec (absMatrixRect A)
                (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                  (higham21SNEComputedNormalSolution fp m R_hat b)))) /
        vecNorm2 (rectTransposeMulVec A y) :=
      div_le_div_of_nonneg_right hAbsolute (le_of_lt hx)
    _ = gamma fp m *
          higham21Cond2With A (undetAplusOfGramInv A AAT_inv) +
        (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) /
          vecNorm2 (rectTransposeMulVec A y) := by
      field_simp [hxne]

/-- A finite source-shaped endpoint.  If the transferred normal-solve envelope
    has a first-order `(n-1) * eta * cond2(A)` bound and a finite
    `eta^2 * C` remainder, then the complete rounded output has the printed
    `n * eta * cond2(A)` leading term and the explicit quadratic remainder
    displayed below.

    The transferred-envelope hypothesis is intentionally visible: it is the
    precise QR/SNE estimate not derivable from `sne_backward_error` alone. -/
theorem higham21_eq21_11_sne_actual_output_relative_forward_error_quadratic_of_transferred_bound
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real)
    (eta C : Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hExact : forall i, matMulVec m (rectGram A) y i = b i)
    (hR_diag : forall i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m (rectGram A) R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hn : 0 < n)
    (heta : 0 <= eta)
    (hC : 0 <= C)
    (hgamma_le : gamma fp m <= eta)
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y))
    (hTransferred :
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let envelope := higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat
      let x := rectTransposeMulVec A y
      let Aplus := undetAplusOfGramInv A AAT_inv
      vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) <=
        ((n : Real) - 1) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          eta ^ 2 * C) :
    let x_hat := higham21SNEActualOutput fp m n A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      (n : Real) * eta * higham21Cond2With A Aplus +
        eta ^ 2 *
          (((n : Real) - 1) * higham21Cond2With A Aplus * vecNorm2 x +
            (1 + eta) * C) / vecNorm2 x := by
  dsimp only at hTransferred ⊢
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hm1
  have hgamma_nonneg : 0 <= gamma fp m := gamma_nonneg fp hm
  have hcond_nonneg :
      0 <= higham21Cond2With A (undetAplusOfGramInv A AAT_inv) :=
    higham21Cond2With_nonneg A (undetAplusOfGramInv A AAT_inv)
  have hxnorm_nonneg : 0 <= vecNorm2 (rectTransposeMulVec A y) :=
    vecNorm2_nonneg _
  have hn_real : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hdim_nonneg : 0 <= (n : Real) - 1 := sub_nonneg.mpr hn_real
  have hbudget_nonneg :
      0 <= ((n : Real) - 1) * eta *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hdim_nonneg heta) hcond_nonneg)
        hxnorm_nonneg)
      (mul_nonneg (sq_nonneg eta) hC)
  have hone_gamma_nonneg : 0 <= 1 + gamma fp m := by linarith
  have hone_le : 1 + gamma fp m <= 1 + eta := by linarith
  have hlead :
      gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) <=
        eta * higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
          vecNorm2 (rectTransposeMulVec A y) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgamma_le hcond_nonneg) hxnorm_nonneg
  have hscaledTransferred :
      (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) <=
        (1 + eta) *
          (((n : Real) - 1) * eta *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) := by
    calc
      (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) <=
          (1 + gamma fp m) *
            (((n : Real) - 1) * eta *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) :=
        mul_le_mul_of_nonneg_left hTransferred hone_gamma_nonneg
      _ <= (1 + eta) *
            (((n : Real) - 1) * eta *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) :=
        mul_le_mul_of_nonneg_right hone_le hbudget_nonneg
  have hEnvelopeRelative :=
    higham21_eq21_11_sne_actual_output_relative_forward_error_envelope
      fp A AAT_inv R_hat b y hInv hExact hR_diag hChol hm1 hx
  dsimp only at hEnvelopeRelative
  have hxne : vecNorm2 (rectTransposeMulVec A y) ≠ 0 := ne_of_gt hx
  have hAbsoluteShape :
      gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
          (1 + gamma fp m) *
            vecNorm2
              (rectTransposeMulVec (absMatrixRect A)
                (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                  (higham21SNEComputedNormalSolution fp m R_hat b))) <=
        (n : Real) * eta *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
          eta ^ 2 *
            (((n : Real) - 1) *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
              (1 + eta) * C) := by
    calc
      gamma fp m *
            higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
          (1 + gamma fp m) *
            vecNorm2
              (rectTransposeMulVec (absMatrixRect A)
                (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                  (higham21SNEComputedNormalSolution fp m R_hat b))) <=
          eta * higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
              vecNorm2 (rectTransposeMulVec A y) +
            (1 + eta) *
              (((n : Real) - 1) * eta *
                    higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                      vecNorm2 (rectTransposeMulVec A y) + eta ^ 2 * C) :=
        add_le_add hlead hscaledTransferred
      _ = (n : Real) * eta *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
          eta ^ 2 *
            (((n : Real) - 1) *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
              (1 + eta) * C) := by ring
  have hRelativeShape :
      (gamma fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            (1 + gamma fp m) *
              vecNorm2
                (rectTransposeMulVec (absMatrixRect A)
                  (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                    (higham21SNEComputedNormalSolution fp m R_hat b)))) /
          vecNorm2 (rectTransposeMulVec A y) <=
        ((n : Real) * eta *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
            eta ^ 2 *
              (((n : Real) - 1) *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) +
                (1 + eta) * C)) /
          vecNorm2 (rectTransposeMulVec A y) :=
    div_le_div_of_nonneg_right hAbsoluteShape (le_of_lt hx)
  calc
    vecNorm2 (fun j => higham21SNEActualOutput fp m n A R_hat b j -
        rectTransposeMulVec A y j) / vecNorm2 (rectTransposeMulVec A y) <=
      gamma fp m *
          higham21Cond2With A (undetAplusOfGramInv A AAT_inv) +
        (1 + gamma fp m) *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A)
              (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                (higham21SNEComputedNormalSolution fp m R_hat b))) /
          vecNorm2 (rectTransposeMulVec A y) := hEnvelopeRelative
    _ = (gamma fp m *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            (1 + gamma fp m) *
              vecNorm2
                (rectTransposeMulVec (absMatrixRect A)
                  (higham21SNEForwardEnvelope fp m AAT_inv R_hat
                    (higham21SNEComputedNormalSolution fp m R_hat b)))) /
          vecNorm2 (rectTransposeMulVec A y) := by
      field_simp [hxne]
    _ <= ((n : Real) * eta *
                higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                  vecNorm2 (rectTransposeMulVec A y) +
            eta ^ 2 *
              (((n : Real) - 1) *
                  higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                    vecNorm2 (rectTransposeMulVec A y) +
                (1 + eta) * C)) /
          vecNorm2 (rectTransposeMulVec A y) := hRelativeShape
    _ = (n : Real) * eta *
          higham21Cond2With A (undetAplusOfGramInv A AAT_inv) +
        eta ^ 2 *
          (((n : Real) - 1) *
              higham21Cond2With A (undetAplusOfGramInv A AAT_inv) *
                vecNorm2 (rectTransposeMulVec A y) +
            (1 + eta) * C) / vecNorm2 (rectTransposeMulVec A y) := by
      field_simp [hxne]

/-- The source-shaped theorem specialized to the finite gamma combination
    returned by `sne_backward_error`.  The remaining hypothesis is exactly the
    unavailable transfer of that solve certificate through `|A|^T` with the
    displayed first-order coefficient and a finite quadratic remainder. -/
theorem higham21_eq21_11_sne_actual_output_relative_forward_error_quadratic
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real)
    (C : Real)
    (hInv : IsInverse m (rectGram A) AAT_inv)
    (hExact : forall i, matMulVec m (rectGram A) y i = b i)
    (hR_diag : forall i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m (rectGram A) R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hn : 0 < n)
    (hC : 0 <= C)
    (hx : 0 < vecNorm2 (rectTransposeMulVec A y))
    (hTransferred :
      let eta := Higham21SNEBackwardCoefficient fp m
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let envelope := higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat
      let x := rectTransposeMulVec A y
      let Aplus := undetAplusOfGramInv A AAT_inv
      vecNorm2 (rectTransposeMulVec (absMatrixRect A) envelope) <=
        ((n : Real) - 1) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          eta ^ 2 * C) :
    let eta := Higham21SNEBackwardCoefficient fp m
    let x_hat := higham21SNEActualOutput fp m n A R_hat b
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x <=
      (n : Real) * eta * higham21Cond2With A Aplus +
        eta ^ 2 *
          (((n : Real) - 1) * higham21Cond2With A Aplus * vecNorm2 x +
            (1 + eta) * C) / vecNorm2 x := by
  exact
    higham21_eq21_11_sne_actual_output_relative_forward_error_quadratic_of_transferred_bound
      fp A AAT_inv R_hat b y (Higham21SNEBackwardCoefficient fp m) C
      hInv hExact hR_diag hChol hm1 hn
      (Higham21SNEBackwardCoefficient_nonneg_of_gammaValid fp m hm1) hC
      (gamma_le_Higham21SNEBackwardCoefficient fp m hm1) hx hTransferred

end NumStability
