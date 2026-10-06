import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.MatrixInversion

/-!
# Chapter14 Section01 InverseErrorAnalysis ForwardErrorEndpoint

Canonical destination for material split out of
`NumStability.Algorithms.Ch14ForwardErrorEndpoint` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- Factor a scalar `ε` out of a nested (double) sum:
    `∑ f · (∑ g · (ε·T)) = ε · ∑ f · (∑ g·T)`. -/
theorem ch14ext_pull_eps_double_sum {n : ℕ} (ε : ℝ)
    (f : Fin n → ℝ) (g : Fin n → Fin n → ℝ) (T : Fin n → ℝ) :
    ∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * (ε * T k₂))
      = ε * ∑ k₁ : Fin n, f k₁ * (∑ k₂ : Fin n, g k₁ k₂ * T k₂) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k₁ _
  have hin : ∑ k₂ : Fin n, g k₁ k₂ * (ε * T k₂)
      = ε * ∑ k₂ : Fin n, g k₁ k₂ * T k₂ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k₂ _; ring
  rw [hin]; ring

/-- **Higham (14.3), envelope step — bound (ii).**  The O(ε) componentwise
    envelope for the perturbed inverse.

    For `Y = (A + ΔA)⁻¹` (encoded honestly by `(A + ΔA)Y = I`) with `|ΔA| ≤ ε|A|`
    and `A_inv` a two-sided inverse of `A`,
        `|Y| ≤ |A⁻¹| + ε·|A⁻¹||A||Y|`.
    The remainder `R = ε·|A⁻¹||A||Y|` is explicitly ε-scaled — no `O(ε²)`
    hand-waving.  Proof: from the EXACT identity `A⁻¹ − Y = A⁻¹ΔAY`
    (`ideal_forward_error`), `Y = A⁻¹ − (A⁻¹ − Y)`, then the triangle
    inequality. -/
theorem ch14ext_abs_Y_le_abs_Ainv_plus_firstorder_remainder (n : ℕ)
    (A A_inv Y ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |Y i j| ≤ |A_inv i j| +
      ε * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
  intro i j
  have hbase := ideal_forward_error n A A_inv Y ΔA ε hε hΔA hInv hRInv hY i j
  have hrw : Y i j = A_inv i j + -(A_inv i j - Y i j) := by ring
  rw [hrw]
  calc |A_inv i j + -(A_inv i j - Y i j)|
      ≤ |A_inv i j| + |-(A_inv i j - Y i j)| := abs_add_le _ _
    _ = |A_inv i j| + |A_inv i j - Y i j| := by rw [abs_neg]
    _ ≤ |A_inv i j| + ε * ∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
        linarith [hbase]

/-- **Higham (14.3) endpoint.**  The printed forward-error bound for a computed
    inverse, at full printed strength.

    For `Y = (A + ΔA)⁻¹` with `|ΔA| ≤ ε|A|` and `A_inv` a two-sided inverse of
    `A`, the componentwise forward error splits as
        `|A⁻¹ − Y| ≤ ε·|A⁻¹||A||A⁻¹|  +  ε²·(explicit ≥ 0 remainder)`.
    The first summand is exactly Higham's first-order term `ε|A⁻¹||A||A⁻¹|`; the
    second is the book's `O(ε²)`, here exhibited as `ε²` times a concrete
    nonnegative sum rather than left informal.

    Proof: substitute the O(ε) envelope
    (`ch14ext_abs_Y_le_abs_Ainv_plus_firstorder_remainder`, bound (ii)) for `|Y|`
    into the Codex plus-remainder wrapper
    `higham14_eq14_3_forward_error_firstorder_plus_remainder`, then factor the
    resulting ε·(remainder involving ε) into ε². -/
theorem ch14ext_eq14_3_forward_error_endpoint (n : ℕ)
    (A A_inv Y ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |A_inv i j - Y i j| ≤
      ε * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|))
      + ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| *
          (∑ m₁ : Fin n, |A_inv k₂ m₁| *
            (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := by
  intro i j
  -- Feed the O(ε) envelope (bound (ii)) into the plus-remainder wrapper with
  -- R p q = ε · (∑ |A⁻¹||A||Y|).
  have hpr :=
    higham14_eq14_3_forward_error_firstorder_plus_remainder n A A_inv Y ΔA
      (fun p q => ε * ∑ k₁ : Fin n, |A_inv p k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ q|))
      ε hε hΔA hInv hRInv hY
      (ch14ext_abs_Y_le_abs_Ainv_plus_firstorder_remainder
        n A A_inv Y ΔA ε hε hΔA hInv hRInv hY)
      i j
  -- hpr's remainder is  ε · (∑ |A⁻¹| (∑ |A| · (ε·S))) ; factor the inner ε to ε².
  have hEq :
      ε * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| *
          (ε * ∑ m₁ : Fin n, |A_inv k₂ m₁| *
            (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|))))
      = ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| *
          (∑ m₁ : Fin n, |A_inv k₂ m₁| *
            (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := by
    rw [pow_two, mul_assoc]
    congr 1
    exact ch14ext_pull_eps_double_sum ε (fun k₁ => |A_inv i k₁|)
      (fun k₁ k₂ => |A k₁ k₂|)
      (fun k₂ => ∑ m₁ : Fin n, |A_inv k₂ m₁| *
        (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|))
  calc |A_inv i j - Y i j|
      ≤ ε * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|))
        + ε * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| *
            (ε * ∑ m₁ : Fin n, |A_inv k₂ m₁| *
              (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := hpr
    _ = ε * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|))
        + ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, |A k₁ k₂| *
            (∑ m₁ : Fin n, |A_inv k₂ m₁| *
              (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|)))) := by rw [hEq]

/-- The nonnegative matrix `|A⁻¹||A||X|` occurring in the right-residual
first-order envelope. -/
noncomputable def ch14ext_rightResidualEnvelopeRemainder (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k₁ : Fin n, |A_inv i k₁| *
    (∑ k₂ : Fin n, |A k₁ k₂| * |X k₂ j|)

/-- The nonnegative matrix `|Y||A||A⁻¹|` occurring in the left-residual
first-order envelope. -/
noncomputable def ch14ext_leftResidualEnvelopeRemainder (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k₁ : Fin n, |Y i k₁| *
    (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|)

/-- If `A_inv A = I`, then `X - A_inv = A_inv (A X - I)`. -/
theorem ch14ext_sub_trueInverse_eq_mul_rightResidual (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    ∀ i j, X i j - A_inv i j =
      ∑ k : Fin n, A_inv i k * inverseRightResidual n A X k j := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let XM : Matrix (Fin n) (Fin n) ℝ := X
  have hAinvA : AinvM * AM = 1 := by
    ext i j
    simpa [AinvM, AM, Matrix.mul_apply] using hLeft i j
  have hmat : XM - AinvM = AinvM * (AM * XM - 1) := by
    calc
      XM - AinvM = (AinvM * AM) * XM - AinvM := by rw [hAinvA]; simp
      _ = AinvM * (AM * XM - 1) := by noncomm_ring
  intro i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [XM, AinvM, AM, inverseRightResidual, matMul, idMatrix,
    Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- If `A A_inv = I`, then `Y - A_inv = (Y A - I) A_inv`. -/
theorem ch14ext_sub_trueInverse_eq_leftResidual_mul (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    ∀ i j, Y i j - A_inv i j =
      ∑ k : Fin n, inverseLeftResidual n A Y i k * A_inv k j := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let YM : Matrix (Fin n) (Fin n) ℝ := Y
  have hAAinv : AM * AinvM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hRight i j
  have hmat : YM - AinvM = (YM * AM - 1) * AinvM := by
    calc
      YM - AinvM = YM * (AM * AinvM) - AinvM := by rw [hAAinv]; simp
      _ = (YM * AM - 1) * AinvM := by noncomm_ring
  intro i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [YM, AinvM, AM, inverseLeftResidual, matMul, idMatrix,
    Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- A right-residual bound derives the honest envelope
`|X| ≤ |A⁻¹| + c |A⁻¹||A||X|`. -/
theorem ch14ext_abs_X_le_abs_Ainv_plus_rightResidual_remainder (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ) (c : ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (hRightRes : ∀ i j, |inverseRightResidual n A X i j| ≤
      c * ∑ k : Fin n, |A i k| * |X k j|) :
    ∀ i j, |X i j| ≤ |A_inv i j| +
      c * ch14ext_rightResidualEnvelopeRemainder n A A_inv X i j := by
  intro i j
  have hdiff : |X i j - A_inv i j| ≤
      c * ch14ext_rightResidualEnvelopeRemainder n A A_inv X i j := by
    rw [ch14ext_sub_trueInverse_eq_mul_rightResidual n A A_inv X hLeft i j]
    calc
      |∑ k : Fin n, A_inv i k * inverseRightResidual n A X k j|
          ≤ ∑ k : Fin n, |A_inv i k * inverseRightResidual n A X k j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |A_inv i k| * |inverseRightResidual n A X k j| := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_mul _ _
      _ ≤ ∑ k : Fin n, |A_inv i k| *
            (c * ∑ l : Fin n, |A k l| * |X l j|) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (hRightRes k j) (abs_nonneg _)
      _ = c * ch14ext_rightResidualEnvelopeRemainder n A A_inv X i j := by
            simp only [ch14ext_rightResidualEnvelopeRemainder]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
  have hdecomp : X i j = A_inv i j + (X i j - A_inv i j) := by ring
  rw [hdecomp]
  calc
    |A_inv i j + (X i j - A_inv i j)|
        ≤ |A_inv i j| + |X i j - A_inv i j| := abs_add_le _ _
    _ ≤ |A_inv i j| +
        c * ch14ext_rightResidualEnvelopeRemainder n A A_inv X i j := by
          linarith

/-- A left-residual bound derives the honest envelope
`|Y| ≤ |A⁻¹| + c |Y||A||A⁻¹|`. -/
theorem ch14ext_abs_Y_le_abs_Ainv_plus_leftResidual_remainder (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ) (c : ℝ)
    (hRight : IsRightInverse n A A_inv)
    (hLeftRes : ∀ i j, |inverseLeftResidual n A Y i j| ≤
      c * ∑ k : Fin n, |Y i k| * |A k j|) :
    ∀ i j, |Y i j| ≤ |A_inv i j| +
      c * ch14ext_leftResidualEnvelopeRemainder n A A_inv Y i j := by
  intro i j
  have hdiff : |Y i j - A_inv i j| ≤
      c * ch14ext_leftResidualEnvelopeRemainder n A A_inv Y i j := by
    rw [ch14ext_sub_trueInverse_eq_leftResidual_mul n A A_inv Y hRight i j]
    calc
      |∑ k : Fin n, inverseLeftResidual n A Y i k * A_inv k j|
          ≤ ∑ k : Fin n, |inverseLeftResidual n A Y i k * A_inv k j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |inverseLeftResidual n A Y i k| * |A_inv k j| := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_mul _ _
      _ ≤ ∑ k : Fin n,
            (c * ∑ l : Fin n, |Y i l| * |A l k|) * |A_inv k j| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hLeftRes i k) (abs_nonneg _)
      _ = c * ch14ext_leftResidualEnvelopeRemainder n A A_inv Y i j := by
            simp only [ch14ext_leftResidualEnvelopeRemainder,
              Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            ring
  have hdecomp : Y i j = A_inv i j + (Y i j - A_inv i j) := by ring
  rw [hdecomp]
  calc
    |A_inv i j + (Y i j - A_inv i j)|
        ≤ |A_inv i j| + |Y i j - A_inv i j| := abs_add_le _ _
    _ ≤ |A_inv i j| +
        c * ch14ext_leftResidualEnvelopeRemainder n A A_inv Y i j := by
          linarith

/-- The rational quadratic-and-higher part of `gamma_k`. -/
noncomputable def ch14ext_gammaQuadraticRemainder (fp : FPModel) (k : ℕ) : ℝ :=
  (((k : ℝ) * fp.u) ^ 2) / (1 - (k : ℝ) * fp.u)

/-- The rational coefficient in the exact factorization
`gamma_k = u * gammaUnitCoefficient`. -/
noncomputable def ch14ext_gammaUnitCoefficient (fp : FPModel) (k : ℕ) : ℝ :=
  (k : ℝ) / (1 - (k : ℝ) * fp.u)

/-- The rational coefficient left after factoring `u²` from the
quadratic-and-higher part of `gamma_k`. -/
noncomputable def ch14ext_gammaQuadraticCoefficient
    (fp : FPModel) (k : ℕ) : ℝ :=
  ((k : ℝ) ^ 2) / (1 - (k : ℝ) * fp.u)

/-- Exact factorization of `gamma_k` with one visible unit-roundoff factor. -/
theorem ch14ext_gamma_eq_u_mul_unitCoefficient (fp : FPModel) (k : ℕ) :
    gamma fp k = fp.u * ch14ext_gammaUnitCoefficient fp k := by
  simp only [gamma, ch14ext_gammaUnitCoefficient]
  ring

/-- Exact factorization of the higher-order part of `gamma_k` with a visible
`u²` factor. -/
theorem ch14ext_gammaQuadraticRemainder_eq_u_sq_mul_coefficient
    (fp : FPModel) (k : ℕ) :
    ch14ext_gammaQuadraticRemainder fp k =
      fp.u ^ 2 * ch14ext_gammaQuadraticCoefficient fp k := by
  simp only [ch14ext_gammaQuadraticRemainder,
    ch14ext_gammaQuadraticCoefficient]
  ring

/-- Exact first-order split `gamma_k = k u + gammaQuadraticRemainder`. -/
theorem ch14ext_gamma_eq_linear_plus_quadraticRemainder
    (fp : FPModel) (k : ℕ) (hk : gammaValid fp k) :
    gamma fp k = (k : ℝ) * fp.u + ch14ext_gammaQuadraticRemainder fp k := by
  simpa [ch14ext_gammaQuadraticRemainder] using
    gamma_eq_linear_plus_quadratic_remainder fp k hk

/-- The explicit `gamma_k` higher-order remainder is nonnegative. -/
theorem ch14ext_gammaQuadraticRemainder_nonneg
    (fp : FPModel) (k : ℕ) (hk : gammaValid fp k) :
    0 ≤ ch14ext_gammaQuadraticRemainder fp k := by
  have hden : 0 ≤ 1 - (k : ℝ) * fp.u := by
    unfold gammaValid at hk
    linarith
  exact div_nonneg (sq_nonneg _) hden

/-- The scalar version of the rational coefficient left after factoring one
power of unit roundoff from gamma_k. -/
noncomputable def ch14ext_gammaUnitCoefficientScalar (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) / (1 - (k : ℝ) * u)

/-- The scalar version of the rational coefficient left after factoring u²
from the quadratic-and-higher part of gamma_k. -/
noncomputable def ch14ext_gammaQuadraticCoefficientScalar
    (k : ℕ) (u : ℝ) : ℝ :=
  ((k : ℝ) ^ 2) / (1 - (k : ℝ) * u)

/-- Scalarization preserves the unit coefficient used by the endpoint
theorems when evaluated at the model's unit roundoff. -/
theorem ch14ext_gammaUnitCoefficientScalar_at_fp (fp : FPModel) (k : ℕ) :
    ch14ext_gammaUnitCoefficientScalar k fp.u =
      ch14ext_gammaUnitCoefficient fp k := by
  rfl

/-- Scalarization preserves the quadratic coefficient used by the endpoint
theorems when evaluated at the model's unit roundoff. -/
theorem ch14ext_gammaQuadraticCoefficientScalar_at_fp
    (fp : FPModel) (k : ℕ) :
    ch14ext_gammaQuadraticCoefficientScalar k fp.u =
      ch14ext_gammaQuadraticCoefficient fp k := by
  rfl

/-- The gamma-style unit coefficient is continuous at zero; its denominator
is nonzero there. -/
theorem ch14ext_gammaUnitCoefficientScalar_continuousAt_zero (k : ℕ) :
    ContinuousAt (fun u : ℝ => ch14ext_gammaUnitCoefficientScalar k u) 0 := by
  unfold ch14ext_gammaUnitCoefficientScalar
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

/-- The gamma-style quadratic coefficient is continuous at zero; its
denominator is nonzero there. -/
theorem ch14ext_gammaQuadraticCoefficientScalar_continuousAt_zero (k : ℕ) :
    ContinuousAt
      (fun u : ℝ => ch14ext_gammaQuadraticCoefficientScalar k u) 0 := by
  unfold ch14ext_gammaQuadraticCoefficientScalar
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

/-- The rational unit coefficient is locally bounded near zero, expressed as
a Mathlib O(1) statement. -/
theorem ch14ext_gammaUnitCoefficientScalar_isBigO_one (k : ℕ) :
    (fun u : ℝ => ch14ext_gammaUnitCoefficientScalar k u)
      =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
  (ch14ext_gammaUnitCoefficientScalar_continuousAt_zero k).tendsto.isBigO_one ℝ

/-- The rational quadratic coefficient is locally bounded near zero,
expressed as a Mathlib O(1) statement. -/
theorem ch14ext_gammaQuadraticCoefficientScalar_isBigO_one (k : ℕ) :
    (fun u : ℝ => ch14ext_gammaQuadraticCoefficientScalar k u)
      =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
  (ch14ext_gammaQuadraticCoefficientScalar_continuousAt_zero k).tendsto.isBigO_one ℝ

/-- The scalarized quadratic remainder associated with equation (14.3), with
all matrix data and the selected entry fixed. -/
noncomputable def ch14ext_eq14_3_quadraticRemainder (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ) (i j : Fin n) (ε : ℝ) : ℝ :=
  ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
    (∑ k₂ : Fin n, |A k₁ k₂| *
      (∑ m₁ : Fin n, |A_inv k₂ m₁| *
        (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|))))

end Ch14Ext
end NumStability
