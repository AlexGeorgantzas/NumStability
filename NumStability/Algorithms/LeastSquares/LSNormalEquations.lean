-- Algorithms/LeastSquares/LSNormalEquations.lean
--
-- Error analysis of the normal equations method for least squares (Higham §20.4).
--
-- The LS problem min‖b−Ax‖₂ can be solved via the normal equations
-- AᵀAx = Aᵀb. The method forms C = fl(AᵀA), c = fl(Aᵀb), then
-- solves via Cholesky: R̂ᵀR̂ = Ĉ, R̂ᵀy = ĉ, R̂x̂ = y.
--
-- The overall backward error is (AᵀA + ΔA)x̂ = Aᵀb + Δc (eq 20.12)
-- with |ΔA| ≤ γ_m|Aᵀ||A| + γ_{3n+1}|R̂ᵀ||R̂| and |Δc| ≤ γ_m|Aᵀ||b|.
--
-- The forward error bound involves κ(AᵀA) = κ₂(A)² (eq 20.14),
-- explaining why the normal equations method is inferior to QR
-- when A is ill conditioned and the residual is small.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.Cholesky.CholeskySolve

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §20.4  Gram product and vector computation errors
-- ============================================================

/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 386:
    the 2-by-2 normal-equations cross-product example
    `A = [[1, 1], [epsilon, 0]]`. -/
noncomputable def normalEquationsCrossProductExampleA
    (epsilon : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = 0 then 1 else if j = 0 then epsilon else 0

/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 387:
    exact cross product for the example
    `A^T A = [[1 + epsilon^2, 1], [1, 1]]`. -/
theorem normalEquationsCrossProductExample_gram_eq (epsilon : ℝ) :
    (fun i j : Fin 2 =>
        ∑ k : Fin 2,
          normalEquationsCrossProductExampleA epsilon k i *
          normalEquationsCrossProductExampleA epsilon k j) =
      fun i j =>
        if i = 0 then
          if j = 0 then 1 + epsilon ^ 2 else 1
        else
          if j = 0 then 1 else 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [normalEquationsCrossProductExampleA]
    ring
  · norm_num [normalEquationsCrossProductExampleA]
  · norm_num [normalEquationsCrossProductExampleA]
  · norm_num [normalEquationsCrossProductExampleA]

/-- Higham, 2nd ed., Chapter 20, Section 20.4, printed p. 387:
    source model of the rounded cross product in the example,
    `fl(A^T A) = [[1, 1], [1, 1]]`. -/
noncomputable def normalEquationsCrossProductExampleRoundedGram :
    Fin 2 → Fin 2 → ℝ :=
  fun _ _ => 1

/-- The rounded cross product displayed in Higham's Section 20.4 example is
    singular, witnessed by the nonzero vector `[1, -1]`. -/
theorem normalEquationsCrossProductExampleRoundedGram_singular :
    ∃ x : Fin 2 → ℝ,
      x ≠ 0 ∧
      matMulVec 2 normalEquationsCrossProductExampleRoundedGram x = 0 := by
  refine ⟨fun i => if i = 0 then 1 else -1, ?_, ?_⟩
  · intro hx
    have h0 := congrFun hx (0 : Fin 2)
    norm_num at h0
  · ext i
    fin_cases i <;>
      norm_num [matMulVec, normalEquationsCrossProductExampleRoundedGram]

/-- **Error in computing Ĉ = fl(AᵀA)** (Higham §20.4, eq before 20.11).

    When the Gram matrix C = AᵀA is formed in floating-point arithmetic,
    the computed matrix Ĉ satisfies Ĉ = AᵀA + ΔC₁ where
    |ΔC₁_{ij}| ≤ ε · absATA_{ij} componentwise.

    Here absATA_{ij} = ∑_k |A_{ki}|·|A_{kj}| = (|Aᵀ||A|)_{ij},
    which is an n×n matrix. The bound ε = γ(m) reflects the m-term
    inner products in the matrix multiplication.

    This follows from `matMul_error_bound` (MatMul.lean) which already
    supports rectangular dimensions: fl_matMul fp n m n Aᵀ A. -/
structure GramProductError (n : ℕ)
    (C_hat C_exact : Fin n → Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (ε : ℝ) : Prop where
  /-- ε is nonnegative. -/
  eps_nonneg : 0 ≤ ε
  /-- Componentwise error bound: |Ĉ_{ij} − C_{ij}| ≤ ε · (|Aᵀ||A|)_{ij}. -/
  bound : ∀ i j : Fin n, |C_hat i j - C_exact i j| ≤ ε * absATA i j

/-- **Error in computing ĉ = fl(Aᵀb)** (Higham §20.4).

    The computed right-hand side ĉ satisfies ĉ = Aᵀb + Δc where
    |Δc_i| ≤ ε · absATb_i componentwise.

    Here absATb_i = ∑_k |A_{ki}|·|b_k| = (|Aᵀ||b|)_i. The bound ε = γ(m)
    reflects the m-term inner products in the matrix-vector product. -/
structure GramVecError (n : ℕ)
    (c_hat c_exact : Fin n → ℝ)
    (absATb : Fin n → ℝ) (ε : ℝ) : Prop where
  /-- ε is nonnegative. -/
  eps_nonneg : 0 ≤ ε
  /-- Componentwise error bound: |ĉ_i − c_i| ≤ ε · (|Aᵀ||b|)_i. -/
  bound : ∀ i : Fin n, |c_hat i - c_exact i| ≤ ε * absATb i

/-- Concrete bridge for the Gram product contract.

    If `Ĉ` is computed by the existing rounded matrix multiplication kernel as
    `fl(AᵀA)`, then it satisfies `GramProductError` with the standard
    `γ(m)` componentwise bound. -/
theorem gramProductError_from_fl_matMul (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (hm : gammaValid fp m) :
    GramProductError n
      (fl_matMul fp n m n (fun i k => A k i) A)
      (fun i j => ∑ k : Fin m, A k i * A k j)
      (fun i j => ∑ k : Fin m, |A k i| * |A k j|)
      (gamma fp m) := by
  refine ⟨gamma_nonneg fp hm, ?_⟩
  intro i j
  simpa using
    (matMul_error_bound fp n m n (fun i k => A k i) A hm i j)

/-- Concrete bridge for the normal-equations right-hand-side contract.

    If `ĉ` is computed by the existing rounded matrix-vector kernel as
    `fl(Aᵀb)`, then it satisfies `GramVecError` with the standard `γ(m)`
    componentwise bound. -/
theorem gramVecError_from_fl_matVec (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (hm : gammaValid fp m) :
    GramVecError n
      (fl_matVec fp n m (fun i k => A k i) b)
      (fun i => ∑ k : Fin m, A k i * b k)
      (fun i => ∑ k : Fin m, |A k i| * |b k|)
      (gamma fp m) := by
  refine ⟨gamma_nonneg fp hm, ?_⟩
  intro i
  simpa using
    (matVec_error_bound fp n m (fun i k => A k i) b hm i)

-- ============================================================
-- §20.4  Normal equations overall backward error (eq 20.12)
-- ============================================================

/-- **Normal equations overall backward error** (Higham §20.4, eq 20.12).

    Solving min‖b−Ax‖₂ via the normal equations AᵀAx = Aᵀb with
    Cholesky factorization gives:

    (AᵀA + ΔA)x̂ = Aᵀb + Δc

    where the perturbations satisfy the componentwise bounds:
    - |ΔA_{ij}| ≤ ε₁ · absATA_{ij} + ε₂ · ∑_k |R̂_{ki}|·|R̂_{kj}|
    - |Δc_i| ≤ ε₁ · absATb_i

    Here ε₁ = γ(m) is the Gram product/vector error and ε₂ is the
    Cholesky solve error (γ(n+1) + 2γ(n) + γ(n)² from Theorem 10.4).

    Proof: The Cholesky solve gives (Ĉ + ΔC₂₃)x̂ = ĉ (Theorem 10.4).
    Substituting Ĉ = AᵀA + ΔC₁ and ĉ = Aᵀb + Δc gives
    (AᵀA + ΔC₁ + ΔC₂₃)x̂ = Aᵀb + Δc. -/
theorem ls_normal_equations_backward (fp : FPModel) (n : ℕ)
    (ATA : Fin n → Fin n → ℝ) (ATb : Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (C_hat : Fin n → Fin n → ℝ) (c_hat : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (hGram : GramProductError n C_hat ATA absATA (gamma fp m))
    (hGramVec : GramVecError n c_hat ATb absATb (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (_hm : gammaValid fp m)
    (hn1 : gammaValid fp (n + 1)) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (ΔA : Fin n → Fin n → ℝ) (Δc : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + ΔA i j) * x_hat j = ATb i + Δc i) ∧
      (∀ i j, |ΔA i j| ≤
        gamma fp m * absATA i j +
        (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, |Δc i| ≤ gamma fp m * absATb i) := by
  -- Step 1: Cholesky solve gives (Ĉ + ΔC_chol)x̂ = ĉ
  obtain ⟨ΔC_chol, hΔC_bound, hΔC_eq⟩ :=
    cholesky_solve_backward_error_expanded fp n C_hat R_hat c_hat hR_diag hChol hn1
  -- Step 2: Define total perturbation
  -- (AᵀA + ΔC₁ + ΔC_chol)x̂ = Aᵀb + Δc where ΔC₁ = Ĉ − AᵀA
  let ΔC₁ : Fin n → Fin n → ℝ := fun i j => C_hat i j - ATA i j
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔC₁ i j + ΔC_chol i j
  let Δc : Fin n → ℝ := fun i => c_hat i - ATb i
  refine ⟨ΔA, Δc, ?_, ?_, ?_⟩
  · -- Equation: (AᵀA + ΔA)x̂ = Aᵀb + Δc
    -- From Cholesky: ∑_j (Ĉ_{ij} + ΔC_chol_{ij}) · x̂_j = ĉ_i
    -- Ĉ_{ij} + ΔC_chol_{ij} = ATA_{ij} + ΔC₁_{ij} + ΔC_chol_{ij} = ATA_{ij} + ΔA_{ij}
    -- ĉ_i = ATb_i + Δc_i
    intro i
    have hChol_eq := hΔC_eq i
    -- hChol_eq : ∑_j (C_hat i j + ΔC_chol i j) · x̂_j = c_hat i
    -- Rewrite C_hat = ATA + ΔC₁ and c_hat = ATb + Δc
    convert hChol_eq using 1
    · apply Finset.sum_congr rfl; intro j _
      show (ATA i j + (C_hat i j - ATA i j + ΔC_chol i j)) * _ =
           (C_hat i j + ΔC_chol i j) * _
      ring_nf
    · show ATb i + (c_hat i - ATb i) = c_hat i
      ring
  · -- Bound on ΔA: |ΔA_{ij}| ≤ γ_m · absATA_{ij} + ε_chol · ∑|R̂ᵀ||R̂|
    intro i j
    show |C_hat i j - ATA i j + ΔC_chol i j| ≤ _
    calc |C_hat i j - ATA i j + ΔC_chol i j|
        ≤ |C_hat i j - ATA i j| + |ΔC_chol i j| := abs_add_le _ _
      _ ≤ gamma fp m * absATA i j +
          (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ k : Fin n, |R_hat k i| * |R_hat k j| := by
          linarith [hGram.bound i j, hΔC_bound i j]
  · -- Bound on Δc: |Δc_i| ≤ γ_m · absATb_i
    intro i
    show |c_hat i - ATb i| ≤ _
    exact hGramVec.bound i

-- ============================================================
-- §20.4  Forward error bound (eq 20.14)
-- ============================================================

/-- **Normal equations forward error via condition number** (Higham §20.4, eq 20.14).

    The forward error of the normal equations method satisfies
    |x̂ − x| ≤ |(AᵀA)⁻¹| · |ΔA · x̂ + Δc|

    Since κ(AᵀA) = κ₂(A)², this gives ‖x̂−x‖/‖x‖ ≲ κ₂(A)² · u,
    which is worse than the QR method's κ₂(A) · u when the residual
    is small. This explains why QR factorization is generally preferred
    over the normal equations for ill-conditioned problems.

    This is a direct application of `forward_error_from_residual`
    from PerturbationTheory.lean. -/
theorem ls_normal_equations_forward_error (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb x x_hat : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA x i = ATb i)
    (ΔA : Fin n → Fin n → ℝ) (Δc : Fin n → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin n, (ATA i j + ΔA i j) * x_hat j = ATb i + Δc i) :
    ∀ i : Fin n, |x_hat i - x i| ≤
      ∑ j : Fin n, |ATA_inv i j| *
        (∑ k : Fin n, |ΔA j k| * |x_hat k| + |Δc j|) := by
  -- Direct application of Theorem 7.2 (normwise_perturbation_bound).
  intro i; rw [abs_sub_comm]
  exact normwise_perturbation_bound n ATA ATA_inv x x_hat ATb ΔA Δc
    hInv.1 (fun i => hExact i) hPerturbed i

-- ============================================================
-- §19.4  Concrete normal-equations/Cholesky forward certificate
-- ============================================================

/-- Computed solution vector produced by the normal-equations Cholesky solve
    used in `ls_normal_equations_backward`. -/
noncomputable def normalEqCholeskyXHat (fp : FPModel) (n : ℕ)
    (c_hat : Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n R_hat
    (fl_forwardSub fp n (fun i j : Fin n => R_hat j i) c_hat)

/-- Componentwise Gram perturbation radius from the concrete
    normal-equations/Cholesky backward-error theorem. -/
noncomputable def normalEqCholeskyGramBound {m n : ℕ} (fp : FPModel)
    (absATA : Fin n → Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    gamma fp m * absATA i j +
      (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, |R_hat k i| * |R_hat k j|

/-- Componentwise right-hand-side perturbation radius from the concrete
    normal-equations/Cholesky backward-error theorem. -/
noncomputable def normalEqCholeskyRhsBound {m n : ℕ} (fp : FPModel)
    (absATb : Fin n → ℝ) : Fin n → ℝ :=
  fun i => gamma fp m * absATb i

/-- Componentwise forward-error certificate obtained by applying the inverse
    Gram matrix to the normal-equations/Cholesky perturbation radii. -/
noncomputable def normalEqCholeskySolverDx {m n : ℕ} (fp : FPModel)
    (ATA_inv : Fin n → Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i =>
    ∑ j : Fin n, |ATA_inv i j| *
      (∑ k : Fin n,
          normalEqCholeskyGramBound (m := m) fp absATA R_hat j k *
            |x_hat k| +
        normalEqCholeskyRhsBound (m := m) fp absATb j)

/-- The normal-equations/Cholesky Gram perturbation radius is nonnegative
    under the usual nonnegative magnitude hypotheses. -/
theorem normalEqCholeskyGramBound_nonneg {m n : ℕ} (fp : FPModel)
    (absATA : Fin n → Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ)
    (habsATA : ∀ i j : Fin n, 0 ≤ absATA i j)
    (hm : gammaValid fp m) (hn1 : gammaValid fp (n + 1)) :
    ∀ i j : Fin n,
      0 ≤ normalEqCholeskyGramBound (m := m) fp absATA R_hat i j := by
  intro i j
  have hn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  have hγm : 0 ≤ gamma fp m := gamma_nonneg fp hm
  have hγn1 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have hγn : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hcoef :
      0 ≤ gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 := by
    have htwo : 0 ≤ 2 * gamma fp n := mul_nonneg (by norm_num) hγn
    have hsquare : 0 ≤ gamma fp n ^ 2 := sq_nonneg (gamma fp n)
    linarith
  have hsum :
      0 ≤ ∑ k : Fin n, |R_hat k i| * |R_hat k j| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  unfold normalEqCholeskyGramBound
  exact
    add_nonneg
      (mul_nonneg hγm (habsATA i j))
      (mul_nonneg hcoef hsum)

/-- The normal-equations/Cholesky right-hand-side perturbation radius is
    nonnegative under the usual nonnegative magnitude hypotheses. -/
theorem normalEqCholeskyRhsBound_nonneg {m n : ℕ} (fp : FPModel)
    (absATb : Fin n → ℝ)
    (habsATb : ∀ i : Fin n, 0 ≤ absATb i)
    (hm : gammaValid fp m) :
    ∀ i : Fin n, 0 ≤ normalEqCholeskyRhsBound (m := m) fp absATb i := by
  intro i
  unfold normalEqCholeskyRhsBound
  exact mul_nonneg (gamma_nonneg fp hm) (habsATb i)

/-- The normal-equations/Cholesky solver certificate is componentwise
    nonnegative. -/
theorem normalEqCholeskySolverDx_nonneg {m n : ℕ} (fp : FPModel)
    (ATA_inv : Fin n → Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ)
    (habsATA : ∀ i j : Fin n, 0 ≤ absATA i j)
    (habsATb : ∀ i : Fin n, 0 ≤ absATb i)
    (hm : gammaValid fp m) (hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      0 ≤ normalEqCholeskySolverDx
        (m := m) fp ATA_inv absATA absATb R_hat x_hat i := by
  intro i
  unfold normalEqCholeskySolverDx
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (abs_nonneg _)
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro k _
    exact
      mul_nonneg
        (normalEqCholeskyGramBound_nonneg
          (m := m) fp absATA R_hat habsATA hm hn1 j k)
        (abs_nonneg _)
  · exact normalEqCholeskyRhsBound_nonneg (m := m) fp absATb habsATb hm j

/-- Concrete forward-error certificate for the normal-equations/Cholesky
    least-squares solve.

This is the implementation-backed counterpart of the abstract perturbed Gram
certificate: the perturbations are supplied by the repository's local
`ls_normal_equations_backward` theorem, and the componentwise certificate is
obtained by reusing `ls_normal_equations_forward_error`. -/
theorem normal_equations_cholesky_forward_error_certificate {m n : ℕ}
    (fp : FPModel)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb xStar : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA xStar i = ATb i)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (C_hat : Fin n → Fin n → ℝ) (c_hat : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (hGram : GramProductError n C_hat ATA absATA (gamma fp m))
    (hGramVec : GramVecError n c_hat ATb absATb (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |normalEqCholeskyXHat fp n c_hat R_hat i - xStar i| ≤
        normalEqCholeskySolverDx
          (m := m) fp ATA_inv absATA absATb R_hat
          (normalEqCholeskyXHat fp n c_hat R_hat) i := by
  rcases
    ls_normal_equations_backward (m := m) fp n ATA ATb absATA absATb
      C_hat c_hat R_hat hGram hGramVec hChol hR_diag hm hn1 with
    ⟨ΔA, Δc, hPerturbed, hΔA_bound, hΔc_bound⟩
  have hPerturbed' :
      ∀ i : Fin n,
        ∑ j : Fin n,
            (ATA i j + ΔA i j) *
              normalEqCholeskyXHat fp n c_hat R_hat j =
          ATb i + Δc i := by
    simpa [normalEqCholeskyXHat] using hPerturbed
  have hFwd :=
    ls_normal_equations_forward_error n ATA ATA_inv hInv ATb xStar
      (normalEqCholeskyXHat fp n c_hat R_hat) hExact ΔA Δc hPerturbed'
  intro i
  calc
    |normalEqCholeskyXHat fp n c_hat R_hat i - xStar i|
        ≤ ∑ j : Fin n, |ATA_inv i j| *
            (∑ k : Fin n,
                |ΔA j k| *
                  |normalEqCholeskyXHat fp n c_hat R_hat k| +
              |Δc j|) := hFwd i
    _ ≤ normalEqCholeskySolverDx
          (m := m) fp ATA_inv absATA absATb R_hat
          (normalEqCholeskyXHat fp n c_hat R_hat) i := by
        unfold normalEqCholeskySolverDx
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply add_le_add
        · apply Finset.sum_le_sum
          intro k _
          exact
            mul_le_mul_of_nonneg_right
              (hΔA_bound j k)
              (abs_nonneg _)
        · exact hΔc_bound j

-- ============================================================
-- §20.4  Condition number squaring (eq 20.14 explanation)
-- ============================================================

/-- **Condition number squaring for the Gram system** (Higham §20.4).

    For the normal equations AᵀAx = Aᵀb, the condition number of
    the coefficient matrix satisfies κ(AᵀA) ≤ κ₂(A)².

    This is the fundamental reason why the normal equations method
    has κ₂(A)² sensitivity while QR factorization has κ₂(A)
    sensitivity. The QR method works with R (κ₂(R) = κ₂(A)). -/
structure GramConditionSquared (n : ℕ)
    (kappa_A kappa_gram : ℝ) : Prop where
  kappa_ge_one : 1 ≤ kappa_A
  gram_le_squared : kappa_gram ≤ kappa_A ^ 2

/-- **Forward error amplification** (Higham §20.4, eq 20.14).

    Normal equations: forward_err ≤ κ(AᵀA) · ε ≤ κ₂(A)² · ε.
    QR method:        forward_err ≤ κ₂(A) · ε. -/
theorem ne_forward_error_kappa_squared
    (kappa_A kappa_gram eps_backward forward_err : ℝ)
    (_hKappa : 1 ≤ kappa_A)
    (hGram : kappa_gram ≤ kappa_A ^ 2)
    (hForward : forward_err ≤ kappa_gram * eps_backward)
    (hEps : 0 ≤ eps_backward) :
    forward_err ≤ kappa_A ^ 2 * eps_backward := by
  calc forward_err
      ≤ kappa_gram * eps_backward := hForward
    _ ≤ kappa_A ^ 2 * eps_backward :=
        mul_le_mul_of_nonneg_right hGram hEps

end NumStability
