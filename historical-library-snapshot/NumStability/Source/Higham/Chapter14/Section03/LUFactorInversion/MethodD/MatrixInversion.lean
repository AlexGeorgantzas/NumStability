import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter14 Section03 LUFactorInversion MethodD MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Product-formation perturbation for Higham's Method D, equation (14.20):
    `X_hat = X_U * X_L + Delta`. -/
noncomputable def higham14_methodDProductDelta {n : ℕ}
    (X_hat X_U X_L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => X_hat i j - matMul n X_U X_L i j

/-- LU backward perturbation for Method D, using the repository sign convention
    `Delta_A = L_hat * U_hat - A`. -/
noncomputable def higham14_methodDLUBackwardDelta {n : ℕ}
    (A L_hat U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n L_hat U_hat i j - A i j

/-- Left residual of the computed lower-triangular inverse used by Method D:
    `X_L * L_hat - I`. -/
noncomputable def higham14_methodDXLLeftResidual {n : ℕ}
    (X_L L_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n X_L L_hat i j - if i = j then 1 else 0

/-- Left residual of the computed upper-triangular inverse used by Method D:
    `X_U * U_hat - I`. -/
noncomputable def higham14_methodDXULeftResidual {n : ℕ}
    (X_U U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n X_U U_hat i j - if i = j then 1 else 0

/-- Higham equation (14.20), Method D product formation:
    the computed product is the exact product plus an explicit perturbation. -/
theorem higham14_eq14_20_methodD_product_decomposition {n : ℕ}
    (X_hat X_U X_L : Fin n → Fin n → ℝ) (i j : Fin n) :
    X_hat i j = matMul n X_U X_L i j +
      higham14_methodDProductDelta X_hat X_U X_L i j := by
  unfold higham14_methodDProductDelta
  ring

/-- The product perturbation in (14.20) inherits any `MatProdError` componentwise
    bound supplied by the local floating-point multiplication analysis. -/
theorem higham14_eq14_20_methodD_productDelta_bound {n : ℕ}
    (X_hat X_U X_L : Fin n → Fin n → ℝ)
    (ε : ℝ) (absProduct : Fin n → Fin n → ℝ)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) ε absProduct) :
    ∀ i j : Fin n,
      |higham14_methodDProductDelta X_hat X_U X_L i j| ≤ ε * absProduct i j := by
  intro i j
  simpa [higham14_methodDProductDelta] using hProd i j

/-- Higham equation (14.21), Method D LU substitution:
    using `A = L_hat * U_hat - Delta_A`, expand `X_hat * A`. -/
theorem higham14_eq14_21_methodD_lu_substitution {n : ℕ}
    (A L_hat U_hat X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n, X_hat i k * A k j =
      ∑ k : Fin n, X_hat i k * (∑ l : Fin n, L_hat k l * U_hat l j) -
        ∑ k : Fin n, X_hat i k *
          higham14_methodDLUBackwardDelta A L_hat U_hat k j := by
  simp [higham14_methodDLUBackwardDelta, matMul, mul_sub, Finset.sum_sub_distrib]

/-- The LU perturbation in (14.21) inherits the componentwise LU backward-error
    bound. -/
theorem higham14_eq14_21_methodD_luDelta_bound {n : ℕ}
    (A L_hat U_hat : Fin n → Fin n → ℝ) (ε : ℝ)
    (hLU : LUBackwardError n A L_hat U_hat ε) :
    ∀ i j : Fin n,
      |higham14_methodDLUBackwardDelta A L_hat U_hat i j| ≤
        ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
  intro i j
  simpa [higham14_methodDLUBackwardDelta, matMul] using hLU.backward_bound i j

/-- Higham equation (14.22), Method D left-residual expansion.

    With the perturbations from (14.20) and (14.21), the left residual splits
    into the upper-inverse residual, the lower-inverse residual propagated
    through `X_U` and `U_hat`, the product-formation perturbation, and the LU
    backward perturbation. -/
theorem higham14_eq14_22_methodD_left_residual_expansion {n : ℕ}
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0) =
      higham14_methodDXULeftResidual X_U U_hat i j +
      ∑ k₁ : Fin n, X_U i k₁ *
        (∑ k₂ : Fin n,
          higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j) +
      ∑ k₁ : Fin n, higham14_methodDProductDelta X_hat X_U X_L i k₁ *
        (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j) -
      ∑ k : Fin n, X_hat i k *
        higham14_methodDLUBackwardDelta A L_hat U_hat k j := by
  have hAssoc :
      ∑ k : Fin n, (∑ l : Fin n, X_U i l * X_L l k) *
          (∑ m : Fin n, L_hat k m * U_hat m j) =
        ∑ k : Fin n, X_U i k *
          (∑ l : Fin n, (∑ m : Fin n, X_L k m * L_hat m l) * U_hat l j) := by
    have h1 :
        matMul n (matMul n X_U X_L) (matMul n L_hat U_hat) =
          matMul n X_U (matMul n X_L (matMul n L_hat U_hat)) :=
      matMul_assoc n X_U X_L (matMul n L_hat U_hat)
    have h2 :
        matMul n X_L (matMul n L_hat U_hat) =
          matMul n (matMul n X_L L_hat) U_hat :=
      (matMul_assoc n X_L L_hat U_hat).symm
    have h :
        matMul n (matMul n X_U X_L) (matMul n L_hat U_hat) =
          matMul n X_U (matMul n (matMul n X_L L_hat) U_hat) := by
      rw [h1, h2]
    exact congrFun (congrFun h i) j
  have hXU_res_expand :
      higham14_methodDXULeftResidual X_U U_hat i j +
        ∑ k₁ : Fin n, X_U i k₁ *
          (∑ k₂ : Fin n,
            higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j) =
        ∑ k : Fin n, X_U i k *
          (∑ l : Fin n, (∑ m : Fin n, X_L k m * L_hat m l) * U_hat l j) -
          (if i = j then 1 else 0) := by
    simp [higham14_methodDXULeftResidual, higham14_methodDXLLeftResidual,
      matMul, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hXhat_decomp :
      ∑ k : Fin n, X_hat i k * (∑ l : Fin n, L_hat k l * U_hat l j) =
        ∑ k : Fin n, (∑ l : Fin n, X_U i l * X_L l k) *
          (∑ m : Fin n, L_hat k m * U_hat m j) +
        ∑ k : Fin n, higham14_methodDProductDelta X_hat X_U X_L i k *
          (∑ m : Fin n, L_hat k m * U_hat m j) := by
    simp [higham14_methodDProductDelta, matMul, sub_mul,
      Finset.sum_sub_distrib]
  have hA := higham14_eq14_21_methodD_lu_substitution A L_hat U_hat X_hat i j
  rw [hA]
  rw [hXhat_decomp]
  rw [hAssoc]
  linarith [hXU_res_expand]

/-- Higham equation (14.22), Method D:
    the exact residual expansion gives an unconditional componentwise
    absolute-value budget by the triangle inequality. -/
theorem higham14_eq14_22_methodD_left_residual_abs_le_expanded_terms {n : ℕ}
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
      |higham14_methodDXULeftResidual X_U U_hat i j| +
      ∑ k₁ : Fin n, |X_U i k₁| *
        (∑ k₂ : Fin n,
          |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j|) +
      ∑ k₁ : Fin n,
        |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) +
      ∑ k : Fin n,
        |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j| := by
  rw [higham14_eq14_22_methodD_left_residual_expansion]
  let rU := higham14_methodDXULeftResidual X_U U_hat i j
  let rL := ∑ k₁ : Fin n, X_U i k₁ *
    (∑ k₂ : Fin n,
      higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j)
  let rP := ∑ k₁ : Fin n,
    higham14_methodDProductDelta X_hat X_U X_L i k₁ *
      (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)
  let rA := ∑ k : Fin n,
    X_hat i k * higham14_methodDLUBackwardDelta A L_hat U_hat k j
  let bL := ∑ k₁ : Fin n, |X_U i k₁| *
    (∑ k₂ : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j|)
  let bP := ∑ k₁ : Fin n,
    |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
      (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)
  let bA := ∑ k : Fin n,
    |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j|
  change |rU + rL + rP - rA| ≤ |rU| + bL + bP + bA
  have hsplit : |rU + rL + rP - rA| ≤ |rU| + |rL| + |rP| + |rA| := by
    calc
      |rU + rL + rP - rA| = |((rU + rL) + rP) + (-rA)| := by ring_nf
      _ ≤ |(rU + rL) + rP| + |-rA| := abs_add_le _ _
      _ ≤ (|rU + rL| + |rP|) + |rA| := by
        have h := abs_add_le (rU + rL) rP
        rw [abs_neg]
        linarith
      _ ≤ ((|rU| + |rL|) + |rP|) + |rA| := by
        have h := abs_add_le rU rL
        linarith
      _ = |rU| + |rL| + |rP| + |rA| := by ring
  have hLinner : ∀ k₁ : Fin n,
      |∑ k₂ : Fin n,
        higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j| ≤
        ∑ k₂ : Fin n,
          |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j| := by
    intro k₁
    calc
      |∑ k₂ : Fin n,
        higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j|
          ≤ ∑ k₂ : Fin n,
              |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₂ : Fin n,
            |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j| :=
          Finset.sum_abs_mul
            (fun k₂ : Fin n => higham14_methodDXLLeftResidual X_L L_hat k₁ k₂)
            (fun k₂ : Fin n => U_hat k₂ j)
  have hL : |rL| ≤ bL := by
    dsimp [rL, bL]
    calc
      |∑ k₁ : Fin n, X_U i k₁ *
        (∑ k₂ : Fin n,
          higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j)|
          ≤ ∑ k₁ : Fin n,
              |X_U i k₁ *
                (∑ k₂ : Fin n,
                  higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ *
                    U_hat k₂ j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₁ : Fin n, |X_U i k₁| *
            |∑ k₂ : Fin n,
              higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j| := by
          apply Finset.sum_congr rfl
          intro k₁ _
          exact abs_mul (X_U i k₁)
            (∑ k₂ : Fin n,
              higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j)
      _ ≤ ∑ k₁ : Fin n, |X_U i k₁| *
            (∑ k₂ : Fin n,
              |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| *
                |U_hat k₂ j|) := by
          apply Finset.sum_le_sum
          intro k₁ _
          exact mul_le_mul_of_nonneg_left (hLinner k₁) (abs_nonneg _)
  have hPinner : ∀ k₁ : Fin n,
      |∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j| ≤
        ∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j| := by
    intro k₁
    calc
      |∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j|
          ≤ ∑ k₂ : Fin n, |L_hat k₁ k₂ * U_hat k₂ j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j| :=
          Finset.sum_abs_mul (fun k₂ : Fin n => L_hat k₁ k₂)
            (fun k₂ : Fin n => U_hat k₂ j)
  have hP : |rP| ≤ bP := by
    dsimp [rP, bP]
    calc
      |∑ k₁ : Fin n,
        higham14_methodDProductDelta X_hat X_U X_L i k₁ *
          (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)|
          ≤ ∑ k₁ : Fin n,
              |higham14_methodDProductDelta X_hat X_U X_L i k₁ *
                (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₁ : Fin n,
            |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
              |∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j| := by
          apply Finset.sum_congr rfl
          intro k₁ _
          exact abs_mul (higham14_methodDProductDelta X_hat X_U X_L i k₁)
            (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)
      _ ≤ ∑ k₁ : Fin n,
            |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
              (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
          apply Finset.sum_le_sum
          intro k₁ _
          exact mul_le_mul_of_nonneg_left (hPinner k₁) (abs_nonneg _)
  have hA : |rA| ≤ bA := by
    dsimp [rA, bA]
    calc
      |∑ k : Fin n,
        X_hat i k * higham14_methodDLUBackwardDelta A L_hat U_hat k j|
          ≤ ∑ k : Fin n,
              |X_hat i k * higham14_methodDLUBackwardDelta A L_hat U_hat k j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n,
            |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j| :=
          Finset.sum_abs_mul (fun k : Fin n => X_hat i k)
            (fun k : Fin n => higham14_methodDLUBackwardDelta A L_hat U_hat k j)
  linarith

/-- Higham equation (14.23), dependency form:
    combine the exact (14.22) residual budget with the already exposed
    product, LU, and triangular-inverse componentwise error hypotheses.  This
    leaves only the scalar simplification to the printed `(4γ + 2γ^2)` envelope
    open. -/
theorem higham14_eq14_23_methodD_left_residual_expanded_budget {n : ℕ}
    (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j| +
        ∑ k₁ : Fin n, |X_U i k₁| *
          (∑ k₂ : Fin n,
            (gamma fp n * ∑ l : Fin n, |X_L k₁ l| * |L_hat l k₂|) *
              |U_hat k₂ j|) +
        ∑ k₁ : Fin n,
          (gamma fp n * ∑ l : Fin n, |X_U i l| * |X_L l k₁|) *
            (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) +
        ∑ k : Fin n,
          |X_hat i k| *
            (gamma fp n * ∑ l : Fin n, |L_hat k l| * |U_hat l j|) := by
  intro i j
  have hbase :=
    higham14_eq14_22_methodD_left_residual_abs_le_expanded_terms
      A L_hat U_hat X_U X_L X_hat i j
  have hU := hXU_res i j
  have hL :
      (∑ k₁ : Fin n, |X_U i k₁| *
        (∑ k₂ : Fin n,
          |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j|)) ≤
      ∑ k₁ : Fin n, |X_U i k₁| *
        (∑ k₂ : Fin n,
          (gamma fp n * ∑ l : Fin n, |X_L k₁ l| * |L_hat l k₂|) *
            |U_hat k₂ j|) := by
    apply Finset.sum_le_sum
    intro k₁ _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro k₂ _
    exact mul_le_mul_of_nonneg_right (hXL_res k₁ k₂) (abs_nonneg _)
  have hP :
      (∑ k₁ : Fin n,
        |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) ≤
      ∑ k₁ : Fin n,
        (gamma fp n * ∑ l : Fin n, |X_U i l| * |X_L l k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
    apply Finset.sum_le_sum
    intro k₁ _
    apply mul_le_mul_of_nonneg_right
      (higham14_eq14_20_methodD_productDelta_bound X_hat X_U X_L
        (gamma fp n) (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)
        hProd i k₁)
    exact Finset.sum_nonneg fun k₂ _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hA :
      (∑ k : Fin n,
        |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j|) ≤
      ∑ k : Fin n,
        |X_hat i k| *
          (gamma fp n * ∑ l : Fin n, |L_hat k l| * |U_hat l j|) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left
      (higham14_eq14_21_methodD_luDelta_bound A L_hat U_hat
        (gamma fp n) hLU k j)
      (abs_nonneg _)
  linarith

/-- Method D absolute-product associativity:
    `|X_U||X_L||L_hat||U_hat|` can be read either as the source product
    `( |X_U||X_L| ) ( |L_hat||U_hat| )` or as
    `|X_U| ( |X_L||L_hat| ) |U_hat|`. -/
theorem higham14_methodD_abs_product_assoc {n : ℕ}
    (X_U X_L L_hat U_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ q : Fin n, |X_U i q| *
        (∑ r : Fin n,
          (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|)) =
      ∑ p : Fin n,
        (∑ q : Fin n, |X_U i q| * |X_L q p|) *
          (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
  let XUa := absMatrix n X_U
  let XLa := absMatrix n X_L
  let La := absMatrix n L_hat
  let Ua := absMatrix n U_hat
  have hassoc₁ :
      matMul n (matMul n XUa XLa) (matMul n La Ua) =
        matMul n XUa (matMul n XLa (matMul n La Ua)) :=
    matMul_assoc n XUa XLa (matMul n La Ua)
  have hassoc₂ :
      matMul n XLa (matMul n La Ua) =
        matMul n (matMul n XLa La) Ua :=
    (matMul_assoc n XLa La Ua).symm
  have hassoc :
      matMul n (matMul n XUa XLa) (matMul n La Ua) =
        matMul n XUa (matMul n (matMul n XLa La) Ua) := by
    rw [hassoc₁, hassoc₂]
  have hentry := congrFun (congrFun hassoc i) j
  simpa [XUa, XLa, La, Ua, matMul, absMatrix, mul_assoc, mul_left_comm,
    mul_comm] using hentry.symm

/-- Method D diagonal lower bound:
    a componentwise left-residual certificate for `X_L * L_hat - I` implies
    `1 <= (1+gamma) * (|X_L||L_hat|)_{qq}` on each diagonal. -/
theorem higham14_methodD_abs_XL_L_diag_ge_inv_scale {n : ℕ}
    {γ : ℝ} (X_L L_hat : Fin n → Fin n → ℝ)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        γ * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (q : Fin n) :
    1 ≤ (1 + γ) * ∑ p : Fin n, |X_L q p| * |L_hat p q| := by
  let S := ∑ p : Fin n, |X_L q p| * |L_hat p q|
  let x := matMul n X_L L_hat q q
  have hx_abs : |x| ≤ S := by
    calc
      |x| = |∑ p : Fin n, X_L q p * L_hat p q| := by
        simp [x, matMul]
      _ ≤ ∑ p : Fin n, |X_L q p * L_hat p q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by
        simp [S]
  have hres : |x - 1| ≤ γ * S := by
    simpa [x, S, higham14_methodDXLLeftResidual, matMul] using hXL_res q q
  have htri : (1 : ℝ) ≤ |x| + |x - 1| := by
    have h := abs_add_le x (1 - x)
    have hone : |(1 : ℝ)| ≤ |x| + |1 - x| := by
      calc
        |(1 : ℝ)| = |x + (1 - x)| := by
          congr 1
          ring_nf
        _ ≤ |x| + |1 - x| := h
    simpa [abs_of_nonneg zero_le_one, abs_sub_comm] using hone
  calc
    (1 : ℝ) ≤ |x| + |x - 1| := htri
    _ ≤ S + γ * S := add_le_add hx_abs hres
    _ = (1 + γ) * S := by ring_nf

/-- Method D scalar bridge:
    the direct upper-residual product `|X_U||U_hat|` is dominated by
    `(1+gamma)|X_U||X_L||L_hat||U_hat|` when the lower inverse has the
    componentwise left-residual certificate. -/
theorem higham14_methodD_abs_XU_U_le_scaled_abs_product {n : ℕ}
    {γ : ℝ} (hγ : 0 ≤ γ)
    (X_U X_L L_hat U_hat : Fin n → Fin n → ℝ)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        γ * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (i j : Fin n) :
    (∑ q : Fin n, |X_U i q| * |U_hat q j|) ≤
      (1 + γ) *
        ∑ p : Fin n,
          (∑ q : Fin n, |X_U i q| * |X_L q p|) *
            (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
  let D := ∑ q : Fin n,
    |X_U i q| *
      ((∑ p : Fin n, |X_L q p| * |L_hat p q|) * |U_hat q j|)
  have hterm : (∑ q : Fin n, |X_U i q| * |U_hat q j|) ≤
      (1 + γ) * D := by
    calc
      (∑ q : Fin n, |X_U i q| * |U_hat q j|)
          ≤ ∑ q : Fin n,
              (1 + γ) *
                (|X_U i q| *
                  ((∑ p : Fin n, |X_L q p| * |L_hat p q|) *
                    |U_hat q j|)) := by
            apply Finset.sum_le_sum
            intro q _
            have hdiag :=
              higham14_methodD_abs_XL_L_diag_ge_inv_scale
                X_L L_hat hXL_res q
            have hnonneg : 0 ≤ |X_U i q| * |U_hat q j| :=
              mul_nonneg (abs_nonneg _) (abs_nonneg _)
            have hmul := mul_le_mul_of_nonneg_right hdiag hnonneg
            nlinarith [hmul]
      _ = (1 + γ) * D := by
            simp [D, Finset.mul_sum]
  have hD_le_product : D ≤
      ∑ q : Fin n, |X_U i q| *
        (∑ r : Fin n,
          (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|) := by
    apply Finset.sum_le_sum
    intro q _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hnonneg_r : ∀ r ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j| := by
      intro r _
      exact mul_nonneg
        (Finset.sum_nonneg fun p _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (abs_nonneg _)
    simpa using Finset.single_le_sum hnonneg_r (Finset.mem_univ q)
  have hscale : (1 + γ) * D ≤
      (1 + γ) *
        ∑ q : Fin n, |X_U i q| *
          (∑ r : Fin n,
            (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|) :=
    mul_le_mul_of_nonneg_left hD_le_product (by nlinarith)
  have hassoc :=
    higham14_methodD_abs_product_assoc X_U X_L L_hat U_hat i j
  calc
    (∑ q : Fin n, |X_U i q| * |U_hat q j|)
        ≤ (1 + γ) * D := hterm
    _ ≤ (1 + γ) *
        ∑ q : Fin n, |X_U i q| *
          (∑ r : Fin n,
            (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|) := hscale
    _ = (1 + γ) *
        ∑ p : Fin n,
          (∑ q : Fin n, |X_U i q| * |X_L q p|) *
            (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
          rw [hassoc]

/-- The product-formation certificate gives a usable absolute bound on entries
    of the computed Method D product. -/
theorem higham14_methodD_abs_Xhat_le_scaled_abs_product {n : ℕ}
    {γ : ℝ} (X_hat X_U X_L : Fin n → Fin n → ℝ)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) γ
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (i j : Fin n) :
    |X_hat i j| ≤
      (1 + γ) * ∑ k : Fin n, |X_U i k| * |X_L k j| := by
  let S := ∑ k : Fin n, |X_U i k| * |X_L k j|
  let x := matMul n X_U X_L i j
  have hx_abs : |x| ≤ S := by
    calc
      |x| = |∑ k : Fin n, X_U i k * X_L k j| := by
        simp [x, matMul]
      _ ≤ ∑ k : Fin n, |X_U i k * X_L k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by
        simp [S]
  have hdiff : |X_hat i j - x| ≤ γ * S := by
    simpa [x, S] using hProd i j
  calc
    |X_hat i j| = |x + (X_hat i j - x)| := by ring_nf
    _ ≤ |x| + |X_hat i j - x| := abs_add_le _ _
    _ ≤ S + γ * S := add_le_add hx_abs hdiff
    _ = (1 + γ) * S := by ring_nf

/-- Higham equation (14.23), scalar coefficient form:
    the expanded Method D budget from (14.22), together with the lower/upper
    triangular inverse residual certificates, product error, and LU backward
    error, implies the printed `(4γ + 2γ^2)` componentwise envelope. -/
theorem higham14_eq14_23_methodD_left_residual_bound_from_expanded_budget {n : ℕ}
    (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |X_U i q| * |X_L q p|) *
              (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
  intro i j
  let γ := gamma fp n
  let P :=
    ∑ p : Fin n,
      (∑ q : Fin n, |X_U i q| * |X_L q p|) *
        (∑ r : Fin n, |L_hat p r| * |U_hat r j|)
  let Uterm := γ * ∑ q : Fin n, |X_U i q| * |U_hat q j|
  let Lterm := ∑ q : Fin n, |X_U i q| *
    (∑ r : Fin n,
      (γ * ∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|)
  let Pterm := ∑ p : Fin n,
    (γ * ∑ q : Fin n, |X_U i q| * |X_L q p|) *
      (∑ r : Fin n, |L_hat p r| * |U_hat r j|)
  let Aterm := ∑ p : Fin n,
    |X_hat i p| * (γ * ∑ r : Fin n, |L_hat p r| * |U_hat r j|)
  have hγ : 0 ≤ γ := gamma_nonneg fp hn
  have hbase :
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        Uterm + Lterm + Pterm + Aterm := by
    simpa [γ, Uterm, Lterm, Pterm, Aterm] using
      higham14_eq14_23_methodD_left_residual_expanded_budget
        fp A L_hat U_hat X_U X_L X_hat hLU hXL_res hXU_res hProd i j
  have hU_core :
      (∑ q : Fin n, |X_U i q| * |U_hat q j|) ≤ (1 + γ) * P := by
    simpa [γ, P] using
      higham14_methodD_abs_XU_U_le_scaled_abs_product
        hγ X_U X_L L_hat U_hat hXL_res i j
  have hU : Uterm ≤ (γ * (1 + γ)) * P := by
    calc
      Uterm ≤ γ * ((1 + γ) * P) := by
        simpa [Uterm] using mul_le_mul_of_nonneg_left hU_core hγ
      _ = (γ * (1 + γ)) * P := by ring_nf
  have hassoc := higham14_methodD_abs_product_assoc X_U X_L L_hat U_hat i j
  have hL_eq : Lterm = γ * P := by
    calc
      Lterm =
          γ * (∑ q : Fin n, |X_U i q| *
            (∑ r : Fin n,
              (∑ p : Fin n, |X_L q p| * |L_hat p r|) *
                |U_hat r j|)) := by
            simp [Lterm, Finset.mul_sum, mul_assoc,
              mul_left_comm, mul_comm]
      _ = γ * P := by
            rw [hassoc]
  have hL : Lterm ≤ γ * P := le_of_eq hL_eq
  have hPterm_eq : Pterm = γ * P := by
    simp [Pterm, P, Finset.mul_sum, Finset.sum_mul]
    ring_nf
  have hPterm : Pterm ≤ γ * P := le_of_eq hPterm_eq
  have hA_step : Aterm ≤
      ∑ p : Fin n,
        ((1 + γ) * ∑ q : Fin n, |X_U i q| * |X_L q p|) *
          (γ * ∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right
      (higham14_methodD_abs_Xhat_le_scaled_abs_product
        X_hat X_U X_L hProd i p)
    exact mul_nonneg hγ
      (Finset.sum_nonneg fun r _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hA_rhs_eq :
      (∑ p : Fin n,
        ((1 + γ) * ∑ q : Fin n, |X_U i q| * |X_L q p|) *
          (γ * ∑ r : Fin n, |L_hat p r| * |U_hat r j|)) =
        (γ * (1 + γ)) * P := by
    simp [P, Finset.mul_sum, Finset.sum_mul]
    ring_nf
  have hA : Aterm ≤ (γ * (1 + γ)) * P :=
    hA_step.trans (le_of_eq hA_rhs_eq)
  calc
    |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)|
        ≤ Uterm + Lterm + Pterm + Aterm := hbase
    _ ≤ (γ * (1 + γ)) * P + γ * P + γ * P +
        (γ * (1 + γ)) * P := by
          nlinarith [hU, hL, hPterm, hA]
    _ = (4 * γ + 2 * γ ^ 2) * P := by ring_nf

/-- Higham, 2nd ed., Chapter 14, equation (14.23), Method D:
    source-facing local-certificate route to the printed scalar coefficient.

    This wrapper exposes the proved path from the LU backward-error certificate,
    lower/upper triangular inverse residual certificates, and product-error
    certificate directly to the `(4γ + 2γ^2)` left-residual envelope.  The
    remaining source dependency is upstream: deriving the triangular inverse
    residual certificates for the chosen Method 2/2C kernels. -/
theorem higham14_eq14_23_methodD_left_residual_bound_of_local_certificates
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |X_U i q| * |X_L q p|) *
              (∑ r : Fin n, |L_hat p r| * |U_hat r j|) :=
  higham14_eq14_23_methodD_left_residual_bound_from_expanded_budget
    fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd

/-- Higham, 2nd ed., Chapter 14, equation (14.23), Method D:
    normwise companion to the local-certificate residual route.

    The componentwise `(4γ + 2γ^2)` envelope above implies the corresponding
    infinity-norm bound with the two source absolute products retained. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_of_local_certificates
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm (matMul n (absMatrix n X_U) (absMatrix n X_L)) *
          infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hComp0 :=
    higham14_eq14_23_methodD_left_residual_bound_of_local_certificates
      n fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL_nonneg : ∀ i p : Fin n, 0 ≤ XUL i p := by
    intro i p
    simp [XUL, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hLU_nonneg : ∀ p j : Fin n, 0 ≤ LU p j := by
    intro p j
    simp [LU, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hComp : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n, |XUL i p| * |LU p j| := by
    intro i j
    calc
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0|
          ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n,
              (∑ q : Fin n, |X_U i q| * |X_L q p|) *
                (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := hComp0 i j
      _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n, |XUL i p| * |LU p j| := by
          congr 1
          apply Finset.sum_congr rfl
          intro p _
          rw [abs_of_nonneg (hXUL_nonneg i p),
            abs_of_nonneg (hLU_nonneg p j)]
          rfl
  simpa [XUL, LU] using
    higham14_infNorm_le_of_componentwise_matmul_bound hn0
      (R := fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
      (A := XUL) (B := LU) hCoeff_nonneg hComp

/-- Higham, 2nd ed., Chapter 14, equation (14.23), Method D:
    product-of-norms companion to the local-certificate residual route.

    This is the coarser but simpler infinity-norm form obtained by applying
    submultiplicativity to the two retained absolute-product norms. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_product_of_local_certificates
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hRetained :=
    higham14_eq14_23_methodD_left_residual_infNorm_of_local_certificates
      n hn0 fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL :
      infNorm XUL ≤ infNorm X_U * infNorm X_L := by
    simpa [XUL, infNorm_absMatrix hn0 X_U, infNorm_absMatrix hn0 X_L] using
      infNorm_matMul_le hn0 (absMatrix n X_U) (absMatrix n X_L)
  have hLUprod :
      infNorm LU ≤ infNorm L_hat * infNorm U_hat := by
    simpa [LU, infNorm_absMatrix hn0 L_hat, infNorm_absMatrix hn0 U_hat] using
      infNorm_matMul_le hn0 (absMatrix n L_hat) (absMatrix n U_hat)
  have hXUNonneg : 0 ≤ infNorm X_U := infNorm_nonneg X_U
  have hXLNonneg : 0 ≤ infNorm X_L := infNorm_nonneg X_L
  have hXULProdNonneg : 0 ≤ infNorm X_U * infNorm X_L :=
    mul_nonneg hXUNonneg hXLNonneg
  calc
    infNorm (fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
        ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm XUL * infNorm LU := by
            simpa [XUL, LU] using hRetained
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) * infNorm LU := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hXUL hCoeff_nonneg)
              (infNorm_nonneg LU)
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) *
            (infNorm L_hat * infNorm U_hat) := by
            exact mul_le_mul_of_nonneg_left hLUprod
              (mul_nonneg hCoeff_nonneg hXULProdNonneg)
    _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
            ring

/-- Source-facing Higham equation (14.23) wrapper for the Method D left-residual
    bound.  The detailed floating-point composition of the terms in (14.22) is
    still supplied as the local hypothesis `hLeftRes`, while (14.20)--(14.22)
    are exported above as exact algebra. -/
theorem higham14_eq14_23_methodD_left_residual_bound (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) :=
  methodD_left_residual n fp A L_hat U_hat X_U X_L X_hat
    hLU hn hXL_res hXU_res hProd hLeftRes

/-- Source-facing Higham equation (14.23), Method D:
    infinity-norm companion to `higham14_eq14_23_methodD_left_residual_bound`.

    This version keeps the two absolute-product matrix norms retained, matching
    the componentwise product structure supplied by the compatibility
    hypothesis `hLeftRes`. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_bound
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm (matMul n (absMatrix n X_U) (absMatrix n X_L)) *
          infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hComp0 :=
    higham14_eq14_23_methodD_left_residual_bound
      n fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd hLeftRes
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL_nonneg : ∀ i p : Fin n, 0 ≤ XUL i p := by
    intro i p
    simp [XUL, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hLU_nonneg : ∀ p j : Fin n, 0 ≤ LU p j := by
    intro p j
    simp [LU, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hComp : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n, |XUL i p| * |LU p j| := by
    intro i j
    calc
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0|
          ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n,
              (∑ q : Fin n, |X_U i q| * |X_L q p|) *
                (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := hComp0 i j
      _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n, |XUL i p| * |LU p j| := by
          congr 1
          apply Finset.sum_congr rfl
          intro p _
          rw [abs_of_nonneg (hXUL_nonneg i p),
            abs_of_nonneg (hLU_nonneg p j)]
          rfl
  simpa [XUL, LU] using
    higham14_infNorm_le_of_componentwise_matmul_bound hn0
      (R := fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
      (A := XUL) (B := LU) hCoeff_nonneg hComp

/-- Source-facing Higham equation (14.23), Method D:
    product-of-norms companion to `higham14_eq14_23_methodD_left_residual_bound`.

    This is the coarser normwise endpoint obtained by applying infinity-norm
    submultiplicativity to the two retained absolute products. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_product_bound
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hRetained :=
    higham14_eq14_23_methodD_left_residual_infNorm_bound
      n hn0 fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd hLeftRes
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL :
      infNorm XUL ≤ infNorm X_U * infNorm X_L := by
    simpa [XUL, infNorm_absMatrix hn0 X_U, infNorm_absMatrix hn0 X_L] using
      infNorm_matMul_le hn0 (absMatrix n X_U) (absMatrix n X_L)
  have hLUprod :
      infNorm LU ≤ infNorm L_hat * infNorm U_hat := by
    simpa [LU, infNorm_absMatrix hn0 L_hat, infNorm_absMatrix hn0 U_hat] using
      infNorm_matMul_le hn0 (absMatrix n L_hat) (absMatrix n U_hat)
  have hXUNonneg : 0 ≤ infNorm X_U := infNorm_nonneg X_U
  have hXLNonneg : 0 ≤ infNorm X_L := infNorm_nonneg X_L
  have hXULProdNonneg : 0 ≤ infNorm X_U * infNorm X_L :=
    mul_nonneg hXUNonneg hXLNonneg
  calc
    infNorm (fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
        ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm XUL * infNorm LU := by
            simpa [XUL, LU] using hRetained
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) * infNorm LU := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hXUL hCoeff_nonneg)
              (infNorm_nonneg LU)
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) *
            (infNorm L_hat * infNorm U_hat) := by
            exact mul_le_mul_of_nonneg_left hLUprod
              (mul_nonneg hCoeff_nonneg hXULProdNonneg)
    _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
            ring

end NumStability
