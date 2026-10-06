-- Algorithms/Ch14ForwardErrorEndpoint.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 ("Matrix Inversion"), §14.1, equation (14.3), p. 261.
--
-- Target (14.3):  for Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|,
--     |A⁻¹ − Y| ≤ ε|A⁻¹||A||A⁻¹| + O(ε²).
--
-- This module is IMPORT-ONLY.  It reuses the public declarations in
-- `Algorithms/MatrixInversion.lean` and supplies the first-order envelopes that
-- its bounded-replacement wrappers leave to the caller.  Besides (14.3), it
-- closes the corresponding explicit-remainder steps for (14.6) and Problem
-- 14.5 without editing the shared matrix-inversion module.
--
-- The printed derivation is followed exactly:
--   * the EXACT identity  A⁻¹ − Y = A⁻¹ · ΔA · Y  (proved in `ideal_forward_error`);
--   * bound (i)   |A⁻¹ − Y| ≤ ε|A⁻¹||A||Y|;
--   * bound (ii)  |Y| ≤ |A⁻¹| + ε|A⁻¹||A||Y|   (the O(ε) envelope, R := ε·S);
--   * substitution of (ii) into (i), which separates the first-order term
--     ε|A⁻¹||A||A⁻¹| from an explicit remainder that is manifestly ε² · (≥0),
--     i.e. the book's O(ε²).
-- No informal `O(ε²)` hand-waving: the remainder is exhibited as ε² times an
-- explicit nonnegative sum.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.MatrixInversion
import Mathlib.Analysis.Asymptotics.Lemmas

namespace NumStability.Ch14Ext

open scoped BigOperators Topology
open NumStability

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

/-! ## Residual-derived first-order envelopes

The source uses `X = A⁻¹ + O(u)` (or `Y = A⁻¹ + O(u)`) when interpreting
right- and left-residual bounds.  The declarations below derive those envelopes
from the residual hypotheses themselves.  In particular, they do not assume
the stronger and generally false componentwise comparison `|X| ≤ |A⁻¹|`.
-/

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

/-! ## Explicit higher-order scalar bookkeeping -/

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

/-! ## Higham (14.6): Method 1 explicit-remainder endpoint -/

/-- Higham, 2nd ed., Chapter 14, equation (14.6), envelope step.
The Method 1 right-residual theorem itself implies
`|Xhat| ≤ |L⁻¹| + gamma_n |L⁻¹||L||Xhat|`; no componentwise domination of
`Xhat` by the true inverse is assumed. -/
theorem ch14ext_eq14_6_method1_abs_Xhat_envelope (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j, |X_hat i j| ≤ |L_inv i j| + gamma fp n *
      ch14ext_rightResidualEnvelopeRemainder n L L_inv X_hat i j := by
  intro X_hat i j
  apply ch14ext_abs_X_le_abs_Ainv_plus_rightResidual_remainder
    n L L_inv X_hat (gamma fp n) hInv
  intro p q
  have hres := triInv_method1_right_residual_matrix n fp L hL_diag hLT hn p q
  simpa [inverseRightResidual, matMul, idMatrix] using hres

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

/-! ## Higham Problem 14.5: explicit forward-error endpoints -/

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

/-! ## Landau certificates for the explicit quadratic remainders

The endpoint theorems above are pointwise statements for a fixed floating-point
model.  To state their source-level O(u²) claims, the declarations below keep
all matrix and vector data fixed and vary only the scalar u.  In particular,
the computed inverse matrices are fixed parameters of these scalar remainder
functions rather than implicit functions of a varying floating-point model.
-/

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

/-- The scalarized quadratic remainder associated with equation (14.3), with
all matrix data and the selected entry fixed. -/
noncomputable def ch14ext_eq14_3_quadraticRemainder (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ) (i j : Fin n) (ε : ℝ) : ℝ :=
  ε ^ 2 * (∑ k₁ : Fin n, |A_inv i k₁| *
    (∑ k₂ : Fin n, |A k₁ k₂| *
      (∑ m₁ : Fin n, |A_inv k₂ m₁| *
        (∑ m₂ : Fin n, |A m₁ m₂| * |Y m₂ j|))))

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

/-- The full higher-order term displayed by the equation (14.6) endpoint,
scalarized in u while the computed inverse and all other matrix data stay
fixed. -/
noncomputable def ch14ext_eq14_6_method1_quadraticRemainder (n : ℕ)
    (L L_inv X_hat : Fin n → Fin n → ℝ) (i j : Fin n) (u : ℝ) : ℝ :=
  u ^ 2 *
    (ch14ext_gammaQuadraticCoefficientScalar n u *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
      (ch14ext_gammaUnitCoefficientScalar n u) ^ 2 *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| *
            ch14ext_rightResidualEnvelopeRemainder n L L_inv X_hat k₂ j)))

/-- At the model unit roundoff, the scalarized equation (14.6) remainder is
definitionally the higher-order term in the endpoint theorem. -/
theorem ch14ext_eq14_6_method1_quadraticRemainder_at_fp (n : ℕ)
    (fp : FPModel) (L L_inv X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    ch14ext_eq14_6_method1_quadraticRemainder
        n L L_inv X_hat i j fp.u =
      fp.u ^ 2 *
        (ch14ext_gammaQuadraticCoefficient fp n *
            (∑ k₁ : Fin n, |L_inv i k₁| *
              (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
          (ch14ext_gammaUnitCoefficient fp n) ^ 2 *
            (∑ k₁ : Fin n, |L_inv i k₁| *
              (∑ k₂ : Fin n, |L k₁ k₂| *
                ch14ext_rightResidualEnvelopeRemainder
                  n L L_inv X_hat k₂ j))) := by
  rfl

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

/-- The full higher-order term displayed by the right-inverse Problem 14.5
endpoint, scalarized in u with all matrix/vector data fixed. -/
noncomputable def ch14ext_problem14_5_right_quadraticRemainder (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (i : Fin n) (u : ℝ) : ℝ :=
  u ^ 2 *
    (ch14ext_gammaQuadraticCoefficientScalar (n + 1) u *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
      ch14ext_gammaUnitCoefficientScalar (n + 1) u *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n
              (ch14ext_rightResidualEnvelopeRemainder n A A_inv X)
              (absVec n b))) i)

/-- At the model unit roundoff, the scalarized right-inverse Problem 14.5
remainder is definitionally the endpoint theorem's higher-order term. -/
theorem ch14ext_problem14_5_right_quadraticRemainder_at_fp (n : ℕ)
    (fp : FPModel) (A A_inv X : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (i : Fin n) :
    ch14ext_problem14_5_right_quadraticRemainder
        n A A_inv X b i fp.u =
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
  rfl

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

/-- The full higher-order term displayed by the left-inverse Problem 14.5
endpoint, scalarized in u with all matrix/vector data fixed. -/
noncomputable def ch14ext_problem14_5_left_quadraticRemainder (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (i : Fin n) (u : ℝ) : ℝ :=
  u ^ 2 *
    (ch14ext_gammaQuadraticCoefficientScalar (n + 1) u *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A) (absVec n x)) i +
      ch14ext_gammaUnitCoefficientScalar (n + 1) u *
        matMulVec n
          (ch14ext_leftResidualEnvelopeRemainder n A A_inv Y)
          (matMulVec n (absMatrix n A) (absVec n x)) i)

/-- At the model unit roundoff, the scalarized left-inverse Problem 14.5
remainder is definitionally the endpoint theorem's higher-order term. -/
theorem ch14ext_problem14_5_left_quadraticRemainder_at_fp (n : ℕ)
    (fp : FPModel) (A A_inv Y : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    ch14ext_problem14_5_left_quadraticRemainder
        n A A_inv Y x i fp.u =
      fp.u ^ 2 *
        (ch14ext_gammaQuadraticCoefficient fp (n + 1) *
            matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A) (absVec n x)) i +
          ch14ext_gammaUnitCoefficient fp (n + 1) *
            matMulVec n
              (ch14ext_leftResidualEnvelopeRemainder n A A_inv Y)
              (matMulVec n (absMatrix n A) (absVec n x)) i) := by
  rfl

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

end NumStability.Ch14Ext
