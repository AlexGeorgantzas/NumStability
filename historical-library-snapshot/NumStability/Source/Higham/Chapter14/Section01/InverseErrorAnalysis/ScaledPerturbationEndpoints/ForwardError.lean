import Mathlib.Analysis.Asymptotics.Lemmas
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatVec
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.ForwardErrorEndpoint
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1.ForwardErrorEndpoint

/-!
# ForwardError

Canonical destination for the Chapter14.Section01 declarations relocated from the
historical path `NumStability.Algorithms.Ch14ForwardErrorEndpoint` during wave R08.
Holds 12 declaration(s): 7 public and 5 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

private theorem ch14ext_matMulVec_matrix_add_scaled (n : ℕ)
    (M R : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (c : ℝ) :
    matMulVec n (fun i j => M i j + c * R i j) v =
      fun i => matMulVec n M v i + c * matMulVec n R v i := by
  funext i
  simp only [matMulVec]
  calc
    ∑ j : Fin n, (M i j + c * R i j) * v j
        = ∑ j : Fin n, (M i j * v j + c * (R i j * v j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ j : Fin n, M i j * v j) +
          ∑ j : Fin n, c * (R i j * v j) := Finset.sum_add_distrib
    _ = (∑ j : Fin n, M i j * v j) +
          c * ∑ j : Fin n, R i j * v j := by rw [Finset.mul_sum]

private theorem ch14ext_matMulVec_vector_add_scaled (n : ℕ)
    (M : Fin n → Fin n → ℝ) (v w : Fin n → ℝ) (c : ℝ) :
    matMulVec n M (fun j => v j + c * w j) =
      fun i => matMulVec n M v i + c * matMulVec n M w i := by
  funext i
  simp only [matMulVec]
  calc
    ∑ j : Fin n, M i j * (v j + c * w j)
        = ∑ j : Fin n, (M i j * v j + c * (M i j * w j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ j : Fin n, M i j * v j) +
          ∑ j : Fin n, c * (M i j * w j) := Finset.sum_add_distrib
    _ = (∑ j : Fin n, M i j * v j) +
          c * ∑ j : Fin n, M i j * w j := by rw [Finset.mul_sum]

private theorem ch14ext_matMulVec_triple_matrix_add_scaled (n : ℕ)
    (P Q M R : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (c : ℝ) :
    matMulVec n P
        (matMulVec n Q (matMulVec n (fun i j => M i j + c * R i j) v)) =
      fun i =>
        matMulVec n P (matMulVec n Q (matMulVec n M v)) i +
          c * matMulVec n P (matMulVec n Q (matMulVec n R v)) i := by
  calc
    matMulVec n P
        (matMulVec n Q (matMulVec n (fun i j => M i j + c * R i j) v))
        = matMulVec n P
            (matMulVec n Q (fun i => matMulVec n M v i + c * matMulVec n R v i)) := by
              rw [ch14ext_matMulVec_matrix_add_scaled]
    _ = matMulVec n P
          (fun i => matMulVec n Q (matMulVec n M v) i +
            c * matMulVec n Q (matMulVec n R v) i) := by
              rw [ch14ext_matMulVec_vector_add_scaled]
    _ = fun i =>
          matMulVec n P (matMulVec n Q (matMulVec n M v)) i +
            c * matMulVec n P (matMulVec n Q (matMulVec n R v)) i :=
              ch14ext_matMulVec_vector_add_scaled n P
                (matMulVec n Q (matMulVec n M v))
                (matMulVec n Q (matMulVec n R v)) c

private theorem ch14ext_double_sum_add_scaled {n : ℕ} (c : ℝ)
    (f : Fin n → ℝ) (g : Fin n → Fin n → ℝ) (M R : Fin n → ℝ) :
    (∑ k₁ : Fin n, f k₁ *
      (∑ k₂ : Fin n, g k₁ k₂ * (M k₂ + c * R k₂))) =
      (∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * M k₂)) +
        c * ∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * R k₂) := by
  calc
    (∑ k₁ : Fin n, f k₁ *
        (∑ k₂ : Fin n, g k₁ k₂ * (M k₂ + c * R k₂))) =
        (∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * M k₂)) +
          ∑ k₁ : Fin n, f k₁ *
            (∑ k₂ : Fin n, g k₁ k₂ * (c * R k₂)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k₁ _
              have hin :
                  (∑ k₂ : Fin n, g k₁ k₂ * (M k₂ + c * R k₂)) =
                    (∑ k₂ : Fin n, g k₁ k₂ * M k₂) +
                      ∑ k₂ : Fin n, g k₁ k₂ * (c * R k₂) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro k₂ _
                ring
              rw [hin]
              ring
    _ = (∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * M k₂)) +
          c * ∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * R k₂) := by
            rw [ch14ext_pull_eps_double_sum]

/-- Higham, 2nd ed., Chapter 14, equation (14.6), explicit endpoint.
The first term is `n*u |L⁻¹||L||L⁻¹|`; every remaining term is factored
behind a literal `u²`, with rational coefficients and the residual-derived
envelope displayed explicitly. -/
theorem ch14ext_eq14_6_method1_forward_error_endpoint (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j, |X_hat i j - L_inv i j| ≤
      ((n : ℝ) * fp.u) *
          (∑ k₁ : Fin n, |L_inv i k₁| *
            (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
        fp.u ^ 2 *
          (ch14ext_gammaQuadraticCoefficient fp n *
              (∑ k₁ : Fin n, |L_inv i k₁| *
                (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
            (ch14ext_gammaUnitCoefficient fp n) ^ 2 *
              (∑ k₁ : Fin n, |L_inv i k₁| *
                (∑ k₂ : Fin n, |L k₁ k₂| *
                  ch14ext_rightResidualEnvelopeRemainder n L L_inv X_hat k₂ j))) := by
  intro X_hat i j
  let R := ch14ext_rightResidualEnvelopeRemainder n L L_inv X_hat
  let X_bound : Fin n → Fin n → ℝ :=
    fun p q => |L_inv p q| + gamma fp n * R p q
  have hBound : ∀ p q, |X_hat p q| ≤ X_bound p q := by
    intro p q
    simpa [X_bound, R] using
      ch14ext_eq14_6_method1_abs_Xhat_envelope
        n fp L L_inv hL_diag hLT hInv hn p q
  have hpre := triInv_method1_forward_error_firstorder
    n fp L L_inv X_bound hL_diag hLT hInv hn hBound i j
  have hsplit :
      (∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j)) =
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
          gamma fp n *
            (∑ k₁ : Fin n, |L_inv i k₁| *
              (∑ k₂ : Fin n, |L k₁ k₂| * R k₂ j)) := by
    simpa [X_bound] using
      ch14ext_double_sum_add_scaled (gamma fp n)
        (fun k₁ => |L_inv i k₁|) (fun k₁ k₂ => |L k₁ k₂|)
        (fun k₂ => |L_inv k₂ j|) (fun k₂ => R k₂ j)
  have hgamma := ch14ext_gamma_eq_linear_plus_quadraticRemainder fp n hn
  calc
    |X_hat i j - L_inv i j|
        ≤ gamma fp n *
            (∑ k₁ : Fin n, |L_inv i k₁| *
              (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j)) := hpre
    _ = ((n : ℝ) * fp.u) *
          (∑ k₁ : Fin n, |L_inv i k₁| *
            (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
        ch14ext_gammaQuadraticRemainder fp n *
          (∑ k₁ : Fin n, |L_inv i k₁| *
            (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
        (gamma fp n) ^ 2 *
          (∑ k₁ : Fin n, |L_inv i k₁| *
            (∑ k₂ : Fin n, |L k₁ k₂| * R k₂ j)) := by
          rw [hsplit, hgamma]
          ring
    _ = ((n : ℝ) * fp.u) *
          (∑ k₁ : Fin n, |L_inv i k₁| *
            (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
        fp.u ^ 2 *
          (ch14ext_gammaQuadraticCoefficient fp n *
              (∑ k₁ : Fin n, |L_inv i k₁| *
                (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
            (ch14ext_gammaUnitCoefficient fp n) ^ 2 *
              (∑ k₁ : Fin n, |L_inv i k₁| *
                (∑ k₂ : Fin n, |L k₁ k₂| * R k₂ j))) := by
          rw [ch14ext_gammaQuadraticRemainder_eq_u_sq_mul_coefficient,
            ch14ext_gamma_eq_u_mul_unitCoefficient]
          ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-inverse forward endpoint.
The exact residual route is rewritten as the source first-order coefficient
`(n+1)u` plus a literal `u²` times an explicit rational remainder.  The `|X|`
envelope is derived from `|AX-I| ≤ u|A||X|`, not assumed. -/
theorem ch14ext_problem14_5_right_inverse_solve_forward_error_endpoint
    (n : ℕ) (fp : FPModel)
    (A A_inv X : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hRightRes : ∀ i j, |inverseRightResidual n A X i j| ≤
      fp.u * ∑ k : Fin n, |A i k| * |X k j|) :
    let x_hat := fl_matVec fp n n X b
    ∀ i, |x_hat i - x i| ≤
      (((n + 1 : ℕ) : ℝ) * fp.u) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
        fp.u ^ 2 *
          (ch14ext_gammaQuadraticCoefficient fp (n + 1) *
              matMulVec n (absMatrix n A_inv)
                (matMulVec n (absMatrix n A)
                  (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
            ch14ext_gammaUnitCoefficient fp (n + 1) *
              matMulVec n (absMatrix n A_inv)
                (matMulVec n (absMatrix n A)
                  (matMulVec n
                    (ch14ext_rightResidualEnvelopeRemainder n A A_inv X)
                    (absVec n b))) i) := by
  intro x_hat i
  let R := ch14ext_rightResidualEnvelopeRemainder n A A_inv X
  let X_bound : Fin n → Fin n → ℝ :=
    fun p q => (absMatrix n A_inv) p q + fp.u * R p q
  have hBound : ∀ p q, |X p q| ≤ X_bound p q := by
    intro p q
    simpa [X_bound, R, absMatrix] using
      ch14ext_abs_X_le_abs_Ainv_plus_rightResidual_remainder
        n A A_inv X fp.u hLeft hRightRes p q
  have hpre :=
    higham14_problem14_5_right_inverse_solve_forward_error_bound_of_abs_X_le
      n fp A A_inv X x b hn1 hLeft hsolve hRightRes X_bound hBound i
  have hsplit := ch14ext_matMulVec_triple_matrix_add_scaled n
    (absMatrix n A_inv) (absMatrix n A) (absMatrix n A_inv) R
    (absVec n b) fp.u
  have hgamma :=
    ch14ext_gamma_eq_linear_plus_quadraticRemainder fp (n + 1) hn1
  have hfinal : |x_hat i - x i| ≤
      (((n + 1 : ℕ) : ℝ) * fp.u) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
        fp.u ^ 2 *
          (ch14ext_gammaQuadraticCoefficient fp (n + 1) *
              matMulVec n (absMatrix n A_inv)
                (matMulVec n (absMatrix n A)
                  (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
            ch14ext_gammaUnitCoefficient fp (n + 1) *
              matMulVec n (absMatrix n A_inv)
                (matMulVec n (absMatrix n A)
                  (matMulVec n R (absVec n b))) i) := by
    calc
      |x_hat i - x i| ≤
          gamma fp (n + 1) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A)
                (matMulVec n X_bound (absVec n b))) i := hpre
      _ = (((n + 1 : ℕ) : ℝ) * fp.u) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A)
                (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
          ch14ext_gammaQuadraticRemainder fp (n + 1) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A)
                (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
          (gamma fp (n + 1) * fp.u) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A)
                (matMulVec n R (absVec n b))) i := by
            have hi := congrFun hsplit i
            simp only [X_bound]
            rw [hi, hgamma]
            ring
      _ = (((n + 1 : ℕ) : ℝ) * fp.u) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A)
                (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
          fp.u ^ 2 *
            (ch14ext_gammaQuadraticCoefficient fp (n + 1) *
                matMulVec n (absMatrix n A_inv)
                  (matMulVec n (absMatrix n A)
                    (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
              ch14ext_gammaUnitCoefficient fp (n + 1) *
                matMulVec n (absMatrix n A_inv)
                  (matMulVec n (absMatrix n A)
                    (matMulVec n R (absVec n b))) i) := by
            rw [ch14ext_gammaQuadraticRemainder_eq_u_sq_mul_coefficient,
              ch14ext_gamma_eq_u_mul_unitCoefficient]
            ring
  simpa [R] using hfinal

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-inverse forward endpoint.
The source first-order coefficient `(n+1)u` and the literal `u²` remainder are
explicit.  The needed `|Y| = |A⁻¹| + O(u)` envelope follows from the stated left
residual and a right-inverse certificate for the true inverse. -/
theorem ch14ext_problem14_5_left_inverse_solve_forward_error_endpoint
    (n : ℕ) (fp : FPModel)
    (A A_inv Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hRight : IsRightInverse n A A_inv)
    (hLeftRes : ∀ i j, |inverseLeftResidual n A Y i j| ≤
      fp.u * ∑ k : Fin n, |Y i k| * |A k j|) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i, |y_hat i - x i| ≤
      (((n + 1 : ℕ) : ℝ) * fp.u) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A) (absVec n x)) i +
        fp.u ^ 2 *
          (ch14ext_gammaQuadraticCoefficient fp (n + 1) *
              matMulVec n (absMatrix n A_inv)
                (matMulVec n (absMatrix n A) (absVec n x)) i +
            ch14ext_gammaUnitCoefficient fp (n + 1) *
              matMulVec n
                (ch14ext_leftResidualEnvelopeRemainder n A A_inv Y)
                (matMulVec n (absMatrix n A) (absVec n x)) i) := by
  intro b y_hat i
  let R := ch14ext_leftResidualEnvelopeRemainder n A A_inv Y
  let Y_bound : Fin n → Fin n → ℝ :=
    fun p q => (absMatrix n A_inv) p q + fp.u * R p q
  have hBound : ∀ p q, |Y p q| ≤ Y_bound p q := by
    intro p q
    simpa [Y_bound, R, absMatrix] using
      ch14ext_abs_Y_le_abs_Ainv_plus_leftResidual_remainder
        n A A_inv Y fp.u hRight hLeftRes p q
  have hpre :=
    higham14_problem14_5_left_inverse_solve_forward_error_bound_of_abs_Y_le
      n fp A Y x hn1 hLeftRes Y_bound hBound i
  have hsplit := ch14ext_matMulVec_matrix_add_scaled n
    (absMatrix n A_inv) R
    (matMulVec n (absMatrix n A) (absVec n x)) fp.u
  have hgamma :=
    ch14ext_gamma_eq_linear_plus_quadraticRemainder fp (n + 1) hn1
  have hfinal : |y_hat i - x i| ≤
      (((n + 1 : ℕ) : ℝ) * fp.u) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A) (absVec n x)) i +
        fp.u ^ 2 *
          (ch14ext_gammaQuadraticCoefficient fp (n + 1) *
              matMulVec n (absMatrix n A_inv)
                (matMulVec n (absMatrix n A) (absVec n x)) i +
            ch14ext_gammaUnitCoefficient fp (n + 1) *
              matMulVec n R
                (matMulVec n (absMatrix n A) (absVec n x)) i) := by
    calc
      |y_hat i - x i| ≤
          gamma fp (n + 1) *
            matMulVec n Y_bound
              (matMulVec n (absMatrix n A) (absVec n x)) i := hpre
      _ = (((n + 1 : ℕ) : ℝ) * fp.u) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A) (absVec n x)) i +
          ch14ext_gammaQuadraticRemainder fp (n + 1) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A) (absVec n x)) i +
          (gamma fp (n + 1) * fp.u) *
            matMulVec n R
              (matMulVec n (absMatrix n A) (absVec n x)) i := by
            have hi := congrFun hsplit i
            simp only [Y_bound]
            rw [hi, hgamma]
            ring
      _ = (((n + 1 : ℕ) : ℝ) * fp.u) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A) (absVec n x)) i +
          fp.u ^ 2 *
            (ch14ext_gammaQuadraticCoefficient fp (n + 1) *
                matMulVec n (absMatrix n A_inv)
                  (matMulVec n (absMatrix n A) (absVec n x)) i +
              ch14ext_gammaUnitCoefficient fp (n + 1) *
                matMulVec n R
                  (matMulVec n (absMatrix n A) (absVec n x)) i) := by
            rw [ch14ext_gammaQuadraticRemainder_eq_u_sq_mul_coefficient,
              ch14ext_gamma_eq_u_mul_unitCoefficient]
            ring
  simpa [R] using hfinal

private theorem ch14ext_sq_mul_isBigO_of_continuousAt
    (coefficient : ℝ → ℝ) (hcoefficient : ContinuousAt coefficient 0) :
    (fun u : ℝ => u ^ 2 * coefficient u)
      =O[𝓝 0] (fun u : ℝ => u ^ 2) := by
  have hsq :
      (fun u : ℝ => u ^ 2) =O[𝓝 0] (fun u : ℝ => u ^ 2) :=
    Asymptotics.isBigO_refl (fun u : ℝ => u ^ 2) (𝓝 0)
  have hcoefficientO :
      coefficient =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    hcoefficient.tendsto.isBigO_one ℝ
  simpa using hsq.mul hcoefficientO

/-- Fixed-data Landau check for the equation (14.3) remainder: for fixed
matrices and a fixed entry, the explicit scalar expression is `O(ε²)`.

This theorem deliberately does not claim that `Y` is the inverse produced by
a perturbation family varying with `ε`; that source-level family statement is
a separate obligation. -/
theorem ch14ext_eq14_3_quadraticRemainder_isBigO (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ) (i j : Fin n) :
    (fun ε : ℝ => ch14ext_eq14_3_quadraticRemainder n A A_inv Y i j ε)
      =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by
  simpa only [ch14ext_eq14_3_quadraticRemainder] using
    ch14ext_sq_mul_isBigO_of_continuousAt
      (fun _ : ℝ => ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| *
          (∑ m₁ : Fin n, |A_inv k₂ m₁| *
            (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|))))
      continuousAt_const

/-- Fixed-data Landau check for the equation (14.6) remainder.  The computed
inverse is held fixed, so this is an algebraic remainder check rather than a
uniform floating-point algorithm family. -/
theorem ch14ext_eq14_6_method1_quadraticRemainder_isBigO (n : ℕ)
    (L L_inv X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    (fun u : ℝ =>
      ch14ext_eq14_6_method1_quadraticRemainder n L L_inv X_hat i j u)
      =O[𝓝 0] (fun u : ℝ => u ^ 2) := by
  let Clinear : ℝ := ∑ k₁ : Fin n, |L_inv i k₁| *
    (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)
  let Cresidual : ℝ := ∑ k₁ : Fin n, |L_inv i k₁| *
    (∑ k₂ : Fin n, |L k₁ k₂| *
      ch14ext_rightResidualEnvelopeRemainder n L L_inv X_hat k₂ j)
  have hcoefficient : ContinuousAt
      (fun u : ℝ =>
        ch14ext_gammaQuadraticCoefficientScalar n u * Clinear +
          (ch14ext_gammaUnitCoefficientScalar n u) ^ 2 * Cresidual) 0 :=
    ((ch14ext_gammaQuadraticCoefficientScalar_continuousAt_zero n).mul
      continuousAt_const).add
        (((ch14ext_gammaUnitCoefficientScalar_continuousAt_zero n).pow 2).mul
          continuousAt_const)
  simpa [ch14ext_eq14_6_method1_quadraticRemainder, Clinear, Cresidual] using
    ch14ext_sq_mul_isBigO_of_continuousAt _ hcoefficient

/-- Fixed-data Landau check for the right-inverse Problem 14.5 remainder.  It
does not by itself construct a computed-inverse family indexed by roundoff. -/
theorem ch14ext_problem14_5_right_quadraticRemainder_isBigO (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    (fun u : ℝ =>
      ch14ext_problem14_5_right_quadraticRemainder n A A_inv X b i u)
      =O[𝓝 0] (fun u : ℝ => u ^ 2) := by
  let Clinear : ℝ :=
    matMulVec n (absMatrix n A_inv)
      (matMulVec n (absMatrix n A)
        (matMulVec n (absMatrix n A_inv) (absVec n b))) i
  let Cresidual : ℝ :=
    matMulVec n (absMatrix n A_inv)
      (matMulVec n (absMatrix n A)
        (matMulVec n
          (ch14ext_rightResidualEnvelopeRemainder n A A_inv X)
          (absVec n b))) i
  have hcoefficient : ContinuousAt
      (fun u : ℝ =>
        ch14ext_gammaQuadraticCoefficientScalar (n + 1) u * Clinear +
          ch14ext_gammaUnitCoefficientScalar (n + 1) u * Cresidual) 0 :=
    ((ch14ext_gammaQuadraticCoefficientScalar_continuousAt_zero (n + 1)).mul
      continuousAt_const).add
        ((ch14ext_gammaUnitCoefficientScalar_continuousAt_zero (n + 1)).mul
          continuousAt_const)
  simpa [ch14ext_problem14_5_right_quadraticRemainder, Clinear, Cresidual] using
    ch14ext_sq_mul_isBigO_of_continuousAt _ hcoefficient

/-- Fixed-data Landau check for the left-inverse Problem 14.5 remainder.  It
does not by itself construct a computed-inverse family indexed by roundoff. -/
theorem ch14ext_problem14_5_left_quadraticRemainder_isBigO (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (fun u : ℝ =>
      ch14ext_problem14_5_left_quadraticRemainder n A A_inv Y x i u)
      =O[𝓝 0] (fun u : ℝ => u ^ 2) := by
  let Clinear : ℝ :=
    matMulVec n (absMatrix n A_inv)
      (matMulVec n (absMatrix n A) (absVec n x)) i
  let Cresidual : ℝ :=
    matMulVec n
      (ch14ext_leftResidualEnvelopeRemainder n A A_inv Y)
      (matMulVec n (absMatrix n A) (absVec n x)) i
  have hcoefficient : ContinuousAt
      (fun u : ℝ =>
        ch14ext_gammaQuadraticCoefficientScalar (n + 1) u * Clinear +
          ch14ext_gammaUnitCoefficientScalar (n + 1) u * Cresidual) 0 :=
    ((ch14ext_gammaQuadraticCoefficientScalar_continuousAt_zero (n + 1)).mul
      continuousAt_const).add
        ((ch14ext_gammaUnitCoefficientScalar_continuousAt_zero (n + 1)).mul
          continuousAt_const)
  simpa [ch14ext_problem14_5_left_quadraticRemainder, Clinear, Cresidual] using
    ch14ext_sq_mul_isBigO_of_continuousAt _ hcoefficient

end Ch14Ext
end NumStability
