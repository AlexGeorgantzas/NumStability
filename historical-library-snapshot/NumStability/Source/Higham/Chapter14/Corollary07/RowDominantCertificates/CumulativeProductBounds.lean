import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section05

/-!
# CumulativeProductBounds

Canonical destination for the Chapter14.Corollary07 declarations relocated from the
historical path `NumStability.Algorithms.GaussJordan` during wave R08.
Holds 6 declaration(s): 6 public.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Finset BigOperators

namespace NumStability

/-- **Corollary 14.7 conditional row-dominant certificate route**.

    For a row-diagonally-dominant upper factor, the existing Chapter 9
    Lemma-8.8 route gives the source-facing `‖|L||U|‖∞ ≤ (2n-1)‖A‖∞`
    first-stage budget.  The GJE residual side then specializes the proved
    cumulative-product certificate route by exposing the remaining source
    comparison `|N̂_n⋯N̂_2| ≤ |Û⁻¹|` as `hUinvDom`.

    This is deliberately conditional: the theorem records the row-dominant
    bridge and the componentwise residual transfer, while the preservation of
    row diagonal dominance by the computed elimination path remains a separate
    source-instantiation obligation. -/
theorem gje_rowDiagDominantUpper_residual_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|) :
    higham9_17_rowDiagDom_absLU_bound n A L_hat U_hat ∧
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) := by
  have hAbsLU : higham9_17_rowDiagDom_absLU_bound n A L_hat U_hat :=
    higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec
      hnpos A L_hat U_hat hLUExact hURow
  refine ⟨hAbsLU, ?_⟩
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  let U_inv : Fin n → Fin n → ℝ := nonsingInv n U_hat
  have hXdom : ∀ i j : Fin n, |X_abs i j| ≤ |U_inv i j| := by
    intro i j
    simpa [X_abs, U_inv] using hUinvDom i j
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hGen :
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) *
            |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |X_abs k j| * |y j|) := by
    simpa [X_abs] using
      gje_overall_residual_of_cumulative_product_certificates
        n fp A L_hat U_hat b y x_hat N_hat DeltaN start
        hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  intro i
  let T1 : ℝ :=
    gamma fp n * ∑ j : Fin n,
      (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
  let T2X : ℝ :=
    gje_c₃ fp n * ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) *
        |x_hat j|
  let T2U : ℝ :=
    gje_c₃ fp n * ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n, |U_inv k₁ k₂| * |U_hat k₂ j|)) *
        |x_hat j|
  let T3X : ℝ :=
    gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |X_abs k j| * |y j|)
  let T3U : ℝ :=
    gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |U_inv k j| * |y j|)
  have hT2 : T2X ≤ T2U := by
    dsimp [T2X, T2U]
    apply mul_le_mul_of_nonneg_left _ hc3
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro k₁ _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro k₂ _
    exact mul_le_mul_of_nonneg_right (hXdom k₁ k₂) (abs_nonneg _)
  have hT3 : T3X ≤ T3U := by
    dsimp [T3X, T3U]
    apply mul_le_mul_of_nonneg_left _ hc3
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (hXdom k j) (abs_nonneg _)
  have hResidual :
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤ T1 + T2U + T3U := by
    calc
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤ T1 + T2X + T3X := by
        simpa [T1, T2X, T3X] using hGen i
      _ ≤ T1 + T2U + T3X := by
        linarith
      _ ≤ T1 + T2U + T3U := by
        linarith
  simpa [T1, T2U, T3U, U_inv] using hResidual

/-- **Corollary 14.7 conditional infinity-norm residual route**.

    This normwise wrapper uses the row-dominant `|| |L| |U| ||_inf` budget
    supplied by `gje_rowDiagDominantUpper_residual_of_cumulative_product_certificates`
    for the first-stage term, caps the GJE second-stage coefficient by
    `3 n u + gje_c3_quadratic_remainder fp n`, and exposes the two remaining
    second-stage norm aggregations as `beta` and `eta` hypotheses. -/
theorem gje_rowDiagDominantUpper_residual_relative_infNorm_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (beta eta : ℝ)
    (hApos : 0 < infNorm A)
    (hxpos : 0 < infNormVec x_hat)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat)
    (hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat) :
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * infNormVec x_hat) ≤
      gamma fp n * (2 * (n : ℝ) - 1) +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (beta + eta) := by
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x_hat j
  let W : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let x_abs : Fin n → ℝ := absVec n x_hat
  let denom : ℝ := infNorm A * infNormVec x_hat
  let C : ℝ := 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n
  have hLU : LUBackwardError n A L_hat U_hat (gamma fp n) :=
    higham9_LUFactSpec_to_LUBackwardError_gamma fp n hn hLUExact
  have hPack :=
    gje_rowDiagDominantUpper_residual_of_cumulative_product_certificates
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLUExact hLU hURow hn hnpos hn3 hidx hDelta hy hBackwardEq hUinvDom
  have hAbsLU : higham9_17_rowDiagDom_absLU_bound n A L_hat U_hat := hPack.1
  have hResidual := hPack.2
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hC : gje_c₃ fp n ≤ C := by
    simpa [C] using gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3
  have hC_nonneg : 0 ≤ C := le_trans hc3 hC
  have hdenom_pos : 0 < denom := by
    exact mul_pos hApos hxpos
  have hrowCoeff_nonneg : 0 ≤ 2 * (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    nlinarith
  have hT1_bound : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| ≤
        (2 * (n : ℝ) - 1) * infNorm A * infNormVec x_hat := by
    intro i
    have hsum_eq :
        (∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|) =
          matMulVec n W x_abs i := by
      simp [W, x_abs, matMulVec, matMul, absMatrix, absVec]
    have hcomponent :
        matMulVec n W x_abs i ≤ infNorm W * infNormVec x_abs := by
      exact (le_abs_self _).trans
        ((abs_le_infNormVec (matMulVec n W x_abs) i).trans
          (infNormVec_matMulVec_le hnpos W x_abs))
    calc
      ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
          = matMulVec n W x_abs i := hsum_eq
      _ ≤ infNorm W * infNormVec x_abs := hcomponent
      _ ≤ ((2 * (n : ℝ) - 1) * infNorm A) * infNormVec x_abs := by
            exact mul_le_mul_of_nonneg_right hAbsLU (infNormVec_nonneg x_abs)
      _ = (2 * (n : ℝ) - 1) * infNorm A * infNormVec x_hat := by
            rw [infNormVec_absVec hnpos x_hat]
  have hcomponent_bound : ∀ i : Fin n,
      |r i| ≤
        (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom := by
    intro i
    let S1 : ℝ :=
      ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
    let S2 : ℝ :=
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
    let S3 : ℝ :=
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
    have hS1 : S1 ≤ (2 * (n : ℝ) - 1) * denom := by
      calc
        S1 ≤ (2 * (n : ℝ) - 1) * infNorm A * infNormVec x_hat := by
          simpa [S1] using hT1_bound i
        _ = (2 * (n : ℝ) - 1) * denom := by
          simp [denom]
          ring
    have hS2 : S2 ≤ beta * denom := by
      calc
        S2 ≤ beta * infNorm A * infNormVec x_hat := by
          simpa [S2] using hSecondU_x i
        _ = beta * denom := by
          simp [denom]
          ring
    have hS3 : S3 ≤ eta * denom := by
      calc
        S3 ≤ eta * infNorm A * infNormVec x_hat := by
          simpa [S3] using hSecondU_y i
        _ = eta * denom := by
          simp [denom]
          ring
    have hS2_nonneg : 0 ≤ S2 := by
      dsimp [S2]
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg
        (Finset.sum_nonneg (fun k₁ _ =>
          mul_nonneg (abs_nonneg _)
            (Finset.sum_nonneg (fun k₂ _ =>
              mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
        (abs_nonneg _)
    have hS3_nonneg : 0 ≤ S3 := by
      dsimp [S3]
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    have h1 :
        gamma fp n * S1 ≤
          gamma fp n * ((2 * (n : ℝ) - 1) * denom) :=
      mul_le_mul_of_nonneg_left hS1 hgamma
    have h2 :
        gje_c₃ fp n * S2 ≤ C * (beta * denom) := by
      calc
        gje_c₃ fp n * S2 ≤ C * S2 :=
          mul_le_mul_of_nonneg_right hC hS2_nonneg
        _ ≤ C * (beta * denom) :=
          mul_le_mul_of_nonneg_left hS2 hC_nonneg
    have h3 :
        gje_c₃ fp n * S3 ≤ C * (eta * denom) := by
      calc
        gje_c₃ fp n * S3 ≤ C * S3 :=
          mul_le_mul_of_nonneg_right hC hS3_nonneg
        _ ≤ C * (eta * denom) :=
          mul_le_mul_of_nonneg_left hS3 hC_nonneg
    calc
      |r i| ≤ gamma fp n * S1 + gje_c₃ fp n * S2 + gje_c₃ fp n * S3 := by
        simpa [r, S1, S2, S3] using hResidual i
      _ ≤ gamma fp n * ((2 * (n : ℝ) - 1) * denom) +
            C * (beta * denom) + C * (eta * denom) := by
            nlinarith
      _ = (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom := by
            ring
  have hscalar_nonneg :
      0 ≤ (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom := by
    have hsum_nonneg :
        0 ≤ gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta) :=
      add_nonneg
        (mul_nonneg hgamma hrowCoeff_nonneg)
        (mul_nonneg hC_nonneg (add_nonneg hbeta heta))
    exact mul_nonneg hsum_nonneg hdenom_pos.le
  have hVec :
      infNormVec r ≤
        (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom :=
    infNormVec_le_of_abs_le r hcomponent_bound hscalar_nonneg
  have hFinal :
      infNormVec r / denom ≤
        gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta) := by
    have hDiv := div_le_div_of_nonneg_right hVec hdenom_pos.le
    calc
      infNormVec r / denom ≤
          ((gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom) /
            denom := hDiv
      _ = gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta) := by
          field_simp [hdenom_pos.ne']
  simpa [r, denom, C] using hFinal

/-- **Corollary 14.7 conditional infinity-norm forward-error route**.

    This composes the row-dominant relative residual bridge with the exact
    inverse action `x - x_hat = A_inv (b - A x_hat)`.  The result keeps
    the same explicit `beta`/`eta` second-stage aggregation hypotheses and
    an explicit `infNorm A_inv * infNorm A` condition factor. -/
theorem gje_rowDiagDominantUpper_forward_error_relative_infNorm_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hAinv : IsLeftInverse n A A_inv)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (beta eta : ℝ)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat)
    (hxpos : 0 < infNormVec x)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat)
    (hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      infNorm A_inv * infNorm A *
        (gamma fp n * (2 * (n : ℝ) - 1) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (beta + eta)) *
        (infNormVec x_hat / infNormVec x) := by
  let e : Fin n → ℝ := fun i => x i - x_hat i
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x_hat j
  let B : ℝ :=
    gamma fp n * (2 * (n : ℝ) - 1) +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) * (beta + eta)
  let denom : ℝ := infNorm A * infNormVec x_hat
  have hResRel :=
    gje_rowDiagDominantUpper_residual_relative_infNorm_of_cumulative_product_certificates_c3_cap
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLUExact hURow hn hnpos hn3 hidx hDelta hy hBackwardEq hUinvDom
      beta eta hApos hxhatpos hbeta heta hSecondU_x hSecondU_y
  have hdenom_pos : 0 < denom := mul_pos hApos hxhatpos
  have hResNorm : infNormVec r ≤ B * denom := by
    have hmul := mul_le_mul_of_nonneg_right
      (by simpa [r, denom, B] using hResRel) hdenom_pos.le
    calc
      infNormVec r = (infNormVec r / denom) * denom := by
        field_simp [hdenom_pos.ne']
      _ ≤ B * denom := by
        simpa using hmul
  have hDiff : ∀ i : Fin n, e i = ∑ j : Fin n, A_inv i j * r j := by
    intro i
    have hRHS_expand : ∑ j : Fin n, A_inv i j * r j =
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) -
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hExact j]
      simp [r]
      ring
    have hFirst : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x k) = x i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hSecond : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x_hat k) = x_hat i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    calc
      e i = x i - x_hat i := rfl
      _ = ∑ j : Fin n, A_inv i j * r j := by
        rw [hRHS_expand, hFirst, hSecond]
  have hForwardNorm : infNormVec e ≤ infNorm A_inv * infNormVec r := by
    apply infNormVec_le_of_abs_le
    · intro i
      calc
        |e i| = |∑ j : Fin n, A_inv i j * r j| := by rw [hDiff i]
        _ ≤ ∑ j : Fin n, |A_inv i j * r j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |A_inv i j| * |r j| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_mul]
        _ ≤ ∑ j : Fin n, |A_inv i j| * infNormVec r := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left (abs_le_infNormVec r j) (abs_nonneg _)
        _ = (∑ j : Fin n, |A_inv i j|) * infNormVec r := by
              rw [Finset.sum_mul]
        _ ≤ infNorm A_inv * infNormVec r := by
              exact mul_le_mul_of_nonneg_right
                (row_sum_le_infNorm A_inv i) (infNormVec_nonneg r)
    · exact mul_nonneg (infNorm_nonneg A_inv) (infNormVec_nonneg r)
  have hEbound :
      infNormVec e ≤ infNorm A_inv * (B * denom) := by
    calc
      infNormVec e ≤ infNorm A_inv * infNormVec r := hForwardNorm
      _ ≤ infNorm A_inv * (B * denom) :=
        mul_le_mul_of_nonneg_left hResNorm (infNorm_nonneg A_inv)
  have hFinal :
      infNormVec e / infNormVec x ≤
        infNorm A_inv * infNorm A * B *
          (infNormVec x_hat / infNormVec x) := by
    have hDiv := div_le_div_of_nonneg_right hEbound hxpos.le
    calc
      infNormVec e / infNormVec x ≤
          (infNorm A_inv * (B * denom)) / infNormVec x := hDiv
      _ = infNorm A_inv * infNorm A * B *
            (infNormVec x_hat / infNormVec x) := by
          simp [denom]
          field_simp [hxpos.ne']
  simpa [e, B] using hFinal

/-- **Corollary 14.7 conditional infinity-norm forward-error route, kappa form**.

    This is the source-facing condition-number wrapper for
    `gje_rowDiagDominantUpper_forward_error_relative_infNorm_of_cumulative_product_certificates_c3_cap`.
    It rewrites the raw `infNorm A_inv * infNorm A` amplification as
    `kappaInf n _ A A_inv`, leaving the same explicit certificate and
    aggregation hypotheses. -/
theorem gje_rowDiagDominantUpper_forward_error_relative_infNorm_kappaInf_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hAinv : IsLeftInverse n A A_inv)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (beta eta : ℝ)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat)
    (hxpos : 0 < infNormVec x)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat)
    (hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      kappaInf n (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv *
        (gamma fp n * (2 * (n : ℝ) - 1) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (beta + eta)) *
        (infNormVec x_hat / infNormVec x) := by
  have hraw :=
    gje_rowDiagDominantUpper_forward_error_relative_infNorm_of_cumulative_product_certificates_c3_cap
      n fp A A_inv L_hat U_hat b y x x_hat N_hat DeltaN start
      hLUExact hAinv hURow hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hUinvDom
      beta eta hApos hxhatpos hxpos hbeta heta hSecondU_x hSecondU_y
  calc
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
        infNorm A_inv * infNorm A *
          (gamma fp n * (2 * (n : ℝ) - 1) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (beta + eta)) *
          (infNormVec x_hat / infNormVec x) := hraw
    _ =
        kappaInf n (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv *
          (gamma fp n * (2 * (n : ℝ) - 1) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (beta + eta)) *
          (infNormVec x_hat / infNormVec x) := by
        rw [kappaInf_eq_infNorm_mul_infNorm n
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv]
        ring

/-- **Corollary 14.7 conditional infinity-norm residual route, finite
    row-sum aggregation form**.

    This wrapper discharges the explicit `beta` and `eta` aggregation
    hypotheses in the row-dominant residual theorem by using canonical finite
    row-sum constants. It is the residual-side companion to the `kappaInf`
    forward-error row-sum wrapper below. -/
theorem gje_rowDiagDominantUpper_residual_relative_infNorm_rowsum_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat) :
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * infNormVec x_hat) ≤
      gamma fp n * (2 * (n : ℝ) - 1) +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (gje_rowDiagDominantUpper_secondStageX_rowsumConstant
              n A L_hat U_hat x_hat +
            gje_rowDiagDominantUpper_secondStageY_rowsumConstant
              n A L_hat U_hat x_hat y) := by
  let beta : ℝ :=
    gje_rowDiagDominantUpper_secondStageX_rowsumConstant n A L_hat U_hat x_hat
  let eta : ℝ :=
    gje_rowDiagDominantUpper_secondStageY_rowsumConstant n A L_hat U_hat x_hat y
  let denom : ℝ := infNorm A * infNormVec x_hat
  let Xrow : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n,
          |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
  let Yrow : Fin n → ℝ := fun i =>
    ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
  have hdenom_pos : 0 < denom := mul_pos hApos hxhatpos
  have hXrow_nonneg : ∀ i : Fin n, 0 ≤ Xrow i := by
    intro i
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg
        (Finset.sum_nonneg (fun k₁ _ =>
          mul_nonneg (abs_nonneg _)
            (Finset.sum_nonneg (fun k₂ _ =>
              mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
        (abs_nonneg _))
  have hYrow_nonneg : ∀ i : Fin n, 0 ≤ Yrow i := by
    intro i
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hbeta_nonneg : 0 ≤ beta := by
    have hsum : 0 ≤ ∑ i : Fin n, Xrow i :=
      Finset.sum_nonneg (fun i _ => hXrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Xrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow, denom] using hdiv
  have heta_nonneg : 0 ≤ eta := by
    have hsum : 0 ≤ ∑ i : Fin n, Yrow i :=
      Finset.sum_nonneg (fun i _ => hYrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Yrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow, denom] using hdiv
  have hbeta_eq :
      beta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Xrow i := by
    simp [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow]
    field_simp [hdenom_pos.ne']
  have heta_eq :
      eta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Yrow i := by
    simp [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow]
    field_simp [hdenom_pos.ne']
  have hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
          = Xrow i := rfl
      _ ≤ ∑ r : Fin n, Xrow r :=
          Finset.single_le_sum (fun r _ => hXrow_nonneg r) (Finset.mem_univ i)
      _ = beta * infNorm A * infNormVec x_hat := by
          rw [hbeta_eq]
  have hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
          = Yrow i := rfl
      _ ≤ ∑ r : Fin n, Yrow r :=
          Finset.single_le_sum (fun r _ => hYrow_nonneg r) (Finset.mem_univ i)
      _ = eta * infNorm A * infNormVec x_hat := by
          rw [heta_eq]
  have hbase :=
    gje_rowDiagDominantUpper_residual_relative_infNorm_of_cumulative_product_certificates_c3_cap
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLUExact hURow hn hnpos hn3 hidx hDelta hy hBackwardEq hUinvDom
      beta eta hApos hxhatpos hbeta_nonneg heta_nonneg hSecondU_x hSecondU_y
  simpa [beta, eta] using hbase

/-- **Corollary 14.7 conditional infinity-norm forward-error route, finite
    row-sum aggregation form**.

    This wrapper discharges the explicit `beta` and `eta` aggregation
    hypotheses in the `kappaInf` row-dominant forward-error theorem by using
    canonical finite row-sum constants.  It still keeps the source-critical
    row-dominance, cumulative-product domination, exact backward equation, and
    rounded per-stage certificate hypotheses explicit. -/
theorem gje_rowDiagDominantUpper_forward_error_relative_infNorm_kappaInf_rowsum_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hAinv : IsLeftInverse n A A_inv)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat)
    (hxpos : 0 < infNormVec x) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      kappaInf n (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv *
        (gamma fp n * (2 * (n : ℝ) - 1) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (gje_rowDiagDominantUpper_secondStageX_rowsumConstant
                n A L_hat U_hat x_hat +
              gje_rowDiagDominantUpper_secondStageY_rowsumConstant
                n A L_hat U_hat x_hat y)) *
        (infNormVec x_hat / infNormVec x) := by
  let beta : ℝ :=
    gje_rowDiagDominantUpper_secondStageX_rowsumConstant n A L_hat U_hat x_hat
  let eta : ℝ :=
    gje_rowDiagDominantUpper_secondStageY_rowsumConstant n A L_hat U_hat x_hat y
  let denom : ℝ := infNorm A * infNormVec x_hat
  let Xrow : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n,
          |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
  let Yrow : Fin n → ℝ := fun i =>
    ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
  have hdenom_pos : 0 < denom := mul_pos hApos hxhatpos
  have hXrow_nonneg : ∀ i : Fin n, 0 ≤ Xrow i := by
    intro i
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg
        (Finset.sum_nonneg (fun k₁ _ =>
          mul_nonneg (abs_nonneg _)
            (Finset.sum_nonneg (fun k₂ _ =>
              mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
        (abs_nonneg _))
  have hYrow_nonneg : ∀ i : Fin n, 0 ≤ Yrow i := by
    intro i
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hbeta_nonneg : 0 ≤ beta := by
    have hsum : 0 ≤ ∑ i : Fin n, Xrow i :=
      Finset.sum_nonneg (fun i _ => hXrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Xrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow, denom] using hdiv
  have heta_nonneg : 0 ≤ eta := by
    have hsum : 0 ≤ ∑ i : Fin n, Yrow i :=
      Finset.sum_nonneg (fun i _ => hYrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Yrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow, denom] using hdiv
  have hbeta_eq :
      beta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Xrow i := by
    simp [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow]
    field_simp [hdenom_pos.ne']
  have heta_eq :
      eta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Yrow i := by
    simp [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow]
    field_simp [hdenom_pos.ne']
  have hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
          = Xrow i := rfl
      _ ≤ ∑ r : Fin n, Xrow r :=
          Finset.single_le_sum (fun r _ => hXrow_nonneg r) (Finset.mem_univ i)
      _ = beta * infNorm A * infNormVec x_hat := by
          rw [hbeta_eq]
  have hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
          = Yrow i := rfl
      _ ≤ ∑ r : Fin n, Yrow r :=
          Finset.single_le_sum (fun r _ => hYrow_nonneg r) (Finset.mem_univ i)
      _ = eta * infNorm A * infNormVec x_hat := by
          rw [heta_eq]
  have hbase :=
    gje_rowDiagDominantUpper_forward_error_relative_infNorm_kappaInf_of_cumulative_product_certificates_c3_cap
      n fp A A_inv L_hat U_hat b y x x_hat N_hat DeltaN start
      hLUExact hAinv hURow hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hUinvDom
      beta eta hApos hxhatpos hxpos hbeta_nonneg heta_nonneg hSecondU_x hSecondU_y
  simpa [beta, eta] using hbase

end NumStability
