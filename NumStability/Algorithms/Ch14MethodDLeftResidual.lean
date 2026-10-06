-- Algorithms/Ch14MethodDLeftResidual.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 (Matrix Inversion), §14.3.4 "Method D", equations (14.20)-(14.23),
-- pp. 270-271.
--
-- Method D.  Compute L^{-1} and U^{-1} (via Method 2 / 2C and an upper-triangular
-- analogue) and form A^{-1} = U^{-1} X L^{-1}.  Higham's analysis (14.20)-(14.22)
-- expands the LEFT residual  X̂ A - I  into four pieces (upper-inverse residual,
-- lower-inverse residual propagated through X_U U, the product-formation
-- perturbation Δ(X_U,X_L), and the LU backward perturbation ΔA); the triangle
-- inequality and the diagonal-scaling bound (14.24) collapse them to the printed
--
--     |X̂ A - I| ≤ (4γ + 2γ²) |U^{-1}| |L^{-1}| |L| |U|            (14.23).
--
-- WAVE-3 GOAL (Method D left residual at whole-matrix strength).
--
-- The Codex composer chain in `MatrixInversion.lean`
-- (`higham14_eq14_23_methodD_left_residual_bound_of_local_certificates` and its
-- `_from_expanded_budget` / `_expanded_budget` predecessors) DERIVES (14.23) from
-- four local certificates, but every slot is HARDCODED to the single accumulator
-- `gamma fp n`.  The wave-2 whole-matrix Method 2 lower-triangular inverse
-- (`Ch14Method2Loop.ch14ext_method2_left_residual`) certifies its left residual at
-- `gamma fp (n+2)` — a strictly larger accumulator (n+2 > n) — so it cannot be
-- fed to a `gamma fp n` slot, and monotonicity runs the wrong way.  This file
-- removes that obstruction by re-deriving the entire (14.20)-(14.23) budget over
-- an ARBITRARY scalar accumulator `γ ≥ 0` (reusing the ε-generic building blocks
-- the composer chain itself is built from), and then instantiates the lower
-- inverse concretely with the wave-2 Method 2 loop at `γ = gamma fp (n+2)`.
--
-- What is CLOSED unconditionally here:
--   * `ch14ext_methodD_expanded_budget_eps`               — (14.22) budget at any γ.
--   * `ch14ext_methodD_left_residual_bound_eps`           — printed (4γ+2γ²)
--       componentwise envelope (14.23) at any γ.
--   * `ch14ext_methodD_left_residual_infNorm_eps`         — normwise (14.23) at any γ.
--   * `ch14ext_methodD_left_residual_method2lower`        — the SAME printed bound
--       with X_L specialized to the wave-2 whole-matrix Method 2 lower inverse,
--       its left-residual certificate DISCHARGED by `ch14ext_method2_left_residual`
--       at the honest `gamma fp (n+2)` accumulator (no longer a hypothesis).
--   * `ch14ext_methodD_left_residual_method2lower_infNorm`— normwise companion.
--
-- What remains a HYPOTHESIS (documented gap, see the theorem docstrings):
--   * the UPPER-triangular inverse left-residual certificate `hXU_res`.  Higham
--     obtains X_U from "an analogue of Method 2 or 2C for upper triangular
--     matrices" yielding a small LEFT residual; the wave-2 lower-triangular loop
--     transposes to a small RIGHT (not left) residual for U (cf. (14.24)), so no
--     derived whole-matrix upper-triangular LEFT-residual loop is available to
--     discharge it.  The 2-block Method 2C module certifies an off-diagonal block,
--     not a whole-matrix upper inverse.
--   * the LU backward-error certificate `hLU` (Higham Thm 9.3, γ_n) and the
--     product-formation certificate `hProd`.  These are standard GE / fl-matmul
--     certificates supplied upstream; both are naturally ≤ gamma fp (n+2) by
--     accumulator monotonicity, so requiring them at the shared γ is not a
--     strengthening beyond what wave-2 already provides for the lower inverse.
--
-- No new floating-point analysis is assumed: every constant in the conclusion is
-- DERIVED, and the lower-inverse certificate is the concrete wave-2 loop result.

import NumStability.FloatingPoint.Model
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.MatrixInversion
import NumStability.Algorithms.GaussJordan
import NumStability.Algorithms.Ch14Method2Loop
import NumStability.Analysis.MatrixAlgebra

namespace NumStability.Ch14Ext

open scoped BigOperators

-- ============================================================
-- (14.22) expanded budget at an arbitrary accumulator γ
-- ============================================================

/-- **Higham (14.22), Method D — ε-generic expanded budget.**

    Mirror of the Codex `higham14_eq14_23_methodD_left_residual_expanded_budget`,
    but stated over an arbitrary accumulator `γ` instead of the hardcoded
    `gamma fp n`.  Combines the unconditional (14.22) triangle-inequality budget
    with the four local componentwise certificates (LU backward error, lower- and
    upper-inverse left residuals, product formation), each carried at the same
    `γ`.  Every ingredient — `higham14_eq14_22_methodD_left_residual_abs_le_expanded_terms`,
    `higham14_eq14_21_methodD_luDelta_bound`, `higham14_eq14_20_methodD_productDelta_bound`
    — is already ε-generic in `MatrixInversion.lean`; only the outer wrapper was
    specialized, so this generalization is purely structural. -/
theorem ch14ext_methodD_expanded_budget_eps {n : ℕ} (γ : ℝ)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat γ)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        γ * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        γ * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) γ
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        γ * ∑ k : Fin n, |X_U i k| * |U_hat k j| +
        ∑ k₁ : Fin n, |X_U i k₁| *
          (∑ k₂ : Fin n,
            (γ * ∑ l : Fin n, |X_L k₁ l| * |L_hat l k₂|) *
              |U_hat k₂ j|) +
        ∑ k₁ : Fin n,
          (γ * ∑ l : Fin n, |X_U i l| * |X_L l k₁|) *
            (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) +
        ∑ k : Fin n,
          |X_hat i k| *
            (γ * ∑ l : Fin n, |L_hat k l| * |U_hat l j|) := by
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
          (γ * ∑ l : Fin n, |X_L k₁ l| * |L_hat l k₂|) *
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
        (γ * ∑ l : Fin n, |X_U i l| * |X_L l k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
    apply Finset.sum_le_sum
    intro k₁ _
    apply mul_le_mul_of_nonneg_right
      (higham14_eq14_20_methodD_productDelta_bound X_hat X_U X_L
        γ (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)
        hProd i k₁)
    exact Finset.sum_nonneg fun k₂ _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hA :
      (∑ k : Fin n,
        |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j|) ≤
      ∑ k : Fin n,
        |X_hat i k| *
          (γ * ∑ l : Fin n, |L_hat k l| * |U_hat l j|) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left
      (higham14_eq14_21_methodD_luDelta_bound A L_hat U_hat γ hLU k j)
      (abs_nonneg _)
  linarith

-- ============================================================
-- (14.23) printed (4γ + 2γ²) envelope at an arbitrary accumulator γ
-- ============================================================

/-- **Higham (14.23), Method D left residual — ε-generic printed envelope.**

    The componentwise printed bound

        |X̂ A - I|_{ij} ≤ (4γ + 2γ²) (|X_U||X_L| · |L̂||Û|)_{ij}

    over an ARBITRARY accumulator `γ ≥ 0`.  This is the honest generalization of
    the Codex `higham14_eq14_23_methodD_left_residual_bound_from_expanded_budget`
    (which fixes `γ = gamma fp n`): the diagonal-scaling bridges
    `higham14_methodD_abs_XU_U_le_scaled_abs_product`,
    `higham14_methodD_abs_Xhat_le_scaled_abs_product` and the associativity rewrite
    `higham14_methodD_abs_product_assoc` are all already ε-generic in `{γ}`, so the
    only change is threading `hγ : 0 ≤ γ` in place of `gamma_nonneg`. -/
theorem ch14ext_methodD_left_residual_bound_eps {n : ℕ} (γ : ℝ) (hγ : 0 ≤ γ)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat γ)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        γ * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        γ * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) γ
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        (4 * γ + 2 * γ ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |X_U i q| * |X_L q p|) *
              (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
  intro i j
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
  have hbase :
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        Uterm + Lterm + Pterm + Aterm := by
    simpa [Uterm, Lterm, Pterm, Aterm] using
      ch14ext_methodD_expanded_budget_eps γ
        A L_hat U_hat X_U X_L X_hat hLU hXL_res hXU_res hProd i j
  have hU_core :
      (∑ q : Fin n, |X_U i q| * |U_hat q j|) ≤ (1 + γ) * P := by
    simpa [P] using
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
            simp [Lterm, Finset.mul_sum,
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

/-- **Higham (14.23), Method D left residual — ε-generic normwise envelope.**

    Infinity-norm companion to `ch14ext_methodD_left_residual_bound_eps`, with the
    two source absolute products `|X_U||X_L|` and `|L̂||Û|` retained.  Mirror of
    `higham14_eq14_23_methodD_left_residual_infNorm_of_local_certificates` over an
    arbitrary `γ`. -/
theorem ch14ext_methodD_left_residual_infNorm_eps {n : ℕ} (hn0 : 0 < n)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat γ)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        γ * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        γ * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) γ
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * γ + 2 * γ ^ 2) *
        infNorm (matMul n (absMatrix n X_U) (absMatrix n X_L)) *
          infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hComp0 :=
    ch14ext_methodD_left_residual_bound_eps γ hγ
      A L_hat U_hat X_U X_L X_hat hLU hXL_res hXU_res hProd
  have hCoeff_nonneg : 0 ≤ 4 * γ + 2 * γ ^ 2 := by
    nlinarith [sq_nonneg γ]
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
        (4 * γ + 2 * γ ^ 2) *
          ∑ p : Fin n, |XUL i p| * |LU p j| := by
    intro i j
    calc
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0|
          ≤ (4 * γ + 2 * γ ^ 2) *
            ∑ p : Fin n,
              (∑ q : Fin n, |X_U i q| * |X_L q p|) *
                (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := hComp0 i j
      _ = (4 * γ + 2 * γ ^ 2) *
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

-- ============================================================
-- Instantiation: X_L = the wave-2 whole-matrix Method 2 lower inverse
-- ============================================================

/-- **Higham (14.23), Method D left residual — Method 2 lower inverse instance.**

    The printed `(4γ + 2γ²)` componentwise envelope with the LOWER inverse `X_L`
    specialized to the concrete wave-2 reverse-column Method 2 loop
    `ch14ext_method2Inv n fp L` and `L_hat := L`.  Its left-residual certificate is
    DISCHARGED (no longer a hypothesis) by
    `ch14ext_method2_left_residual` at the honest accumulator `γ = gamma fp (n+2)`.

    Because the shared accumulator is fixed to `gamma fp (n+2)` (the wave-2 Method 2
    strength), the LU backward-error, upper-inverse left-residual, and
    product-formation certificates are required at that same `gamma fp (n+2)`.
    They remain hypotheses:

      * `hLU` — Higham Thm 9.3 GE backward error (natural strength γ_n ≤ γ_{n+2});
      * `hXU_res` — the UPPER-triangular inverse LEFT residual; Higham forms X_U by
        an "analogue of Method 2/2C for upper triangular matrices" (§14.3.4) whose
        derived loop is not available (the lower loop transposes to a RIGHT, not
        LEFT, residual for U, cf. (14.24)), so this is the documented open gap;
      * `hProd` — the fl product-formation certificate for X_U X_L (natural
        strength γ_n ≤ γ_{n+2}).

    The lower-inverse constant is thus DERIVED from the concrete loop; the printed
    Method D envelope is exposed at whole-matrix strength conditional only on the
    three residual certificates above. -/
theorem ch14ext_methodD_left_residual_method2lower (n : ℕ) (fp : FPModel)
    (A L U_hat X_U X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnonzero : ∀ j : Fin n, L j j ≠ 0)
    (hLU : LUBackwardError n A L U_hat (gamma fp (n + 2)))
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat
      (matMul n X_U (ch14ext_method2Inv n fp L)) (gamma fp (n + 2))
      (fun i j => ∑ k : Fin n, |X_U i k| * |ch14ext_method2Inv n fp L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |X_U i q| * |ch14ext_method2Inv n fp L q p|) *
              (∑ r : Fin n, |L p r| * |U_hat r j|) := by
  have hγ : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hn2
  have hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual (ch14ext_method2Inv n fp L) L i j| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2Inv n fp L i k| * |L k j| := by
    intro i j
    simpa [higham14_methodDXLLeftResidual, matMul] using
      ch14ext_method2_left_residual n fp L hn2 hLT hLnonzero i j
  exact ch14ext_methodD_left_residual_bound_eps (gamma fp (n + 2)) hγ
    A L U_hat X_U (ch14ext_method2Inv n fp L) X_hat
    hLU hXL_res hXU_res hProd

/-- **Higham (14.23), Method D left residual — Method 2 lower inverse instance,
    normwise.**

    Infinity-norm companion to `ch14ext_methodD_left_residual_method2lower`; the
    lower-inverse left-residual certificate is again discharged by the concrete
    wave-2 Method 2 loop, with the same three residual hypotheses. -/
theorem ch14ext_methodD_left_residual_method2lower_infNorm (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel) (A L U_hat X_U X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnonzero : ∀ j : Fin n, L j j ≠ 0)
    (hLU : LUBackwardError n A L U_hat (gamma fp (n + 2)))
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat
      (matMul n X_U (ch14ext_method2Inv n fp L)) (gamma fp (n + 2))
      (fun i j => ∑ k : Fin n, |X_U i k| * |ch14ext_method2Inv n fp L k j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
        infNorm (matMul n (absMatrix n X_U)
          (absMatrix n (ch14ext_method2Inv n fp L))) *
          infNorm (matMul n (absMatrix n L) (absMatrix n U_hat)) := by
  have hγ : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hn2
  have hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual (ch14ext_method2Inv n fp L) L i j| ≤
        gamma fp (n + 2) *
          ∑ k : Fin n, |ch14ext_method2Inv n fp L i k| * |L k j| := by
    intro i j
    simpa [higham14_methodDXLLeftResidual, matMul] using
      ch14ext_method2_left_residual n fp L hn2 hLT hLnonzero i j
  exact ch14ext_methodD_left_residual_infNorm_eps hn0 (gamma fp (n + 2)) hγ
    A L U_hat X_U (ch14ext_method2Inv n fp L) X_hat
    hLU hXL_res hXU_res hProd

end NumStability.Ch14Ext
