import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Comparisons
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators
open scoped BigOperators Matrix.Norms.Frobenius

/-!
# NormalEquations

Canonical reusable module extracted without change from Higham20NormalEquationsNorms, LSNormalEquations, LSQRSolve.
-/

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
/-- Induced Gram perturbation from a rectangular data perturbation. -/
noncomputable def rectLSGramPerturbation {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j k => rectLSGram (fun i l => A i l + ΔA i l) j k - rectLSGram A j k
/-- Entrywise budget for the Gram perturbation induced by rectangular data
    perturbations. -/
noncomputable def rectLSGramPerturbationEntryBudget {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m,
    (|A i j| * |ΔA i k| + |ΔA i j| * |A i k| + |ΔA i j| * |ΔA i k|)
/-- Coarse Gram perturbation budget from a Frobenius-norm bound
    `‖ΔA‖_F ≤ cA`. -/
noncomputable def rectLSGramPerturbationNormBudget {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (cA : ℝ) : Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, (|A i j| * cA + cA * |A i k| + cA * cA)
theorem rectLSGramPerturbationEntryBudget_nonneg {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) :
    ∀ j k : Fin n, 0 ≤ rectLSGramPerturbationEntryBudget A ΔA j k := by
  intro j k
  unfold rectLSGramPerturbationEntryBudget
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))
theorem rectLSGramPerturbationNormBudget_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {cA : ℝ} (hcA : 0 ≤ cA) :
    ∀ j k : Fin n, 0 ≤ rectLSGramPerturbationNormBudget A cA j k := by
  intro j k
  unfold rectLSGramPerturbationNormBudget
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (abs_nonneg _) hcA)
      (mul_nonneg hcA (abs_nonneg _)))
    (mul_nonneg hcA hcA)
/-- Expansion of the induced rectangular Gram perturbation. -/
theorem rectLSGramPerturbation_eq_sum {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) (j k : Fin n) :
    rectLSGramPerturbation A ΔA j k =
      ∑ i : Fin m,
        (A i j * ΔA i k + ΔA i j * A i k + ΔA i j * ΔA i k) := by
  unfold rectLSGramPerturbation rectLSGram
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
/-- The induced Gram perturbation is bounded entrywise by its exact
    absolute-value expansion budget. -/
theorem rectLSGramPerturbation_abs_le_entryBudget {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) :
    ∀ j k : Fin n,
      |rectLSGramPerturbation A ΔA j k| ≤
        rectLSGramPerturbationEntryBudget A ΔA j k := by
  intro j k
  rw [rectLSGramPerturbation_eq_sum]
  unfold rectLSGramPerturbationEntryBudget
  calc
    |∑ i : Fin m,
        (A i j * ΔA i k + ΔA i j * A i k + ΔA i j * ΔA i k)|
        ≤ ∑ i : Fin m,
            |A i j * ΔA i k + ΔA i j * A i k + ΔA i j * ΔA i k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m,
          (|A i j| * |ΔA i k| + |ΔA i j| * |A i k| +
            |ΔA i j| * |ΔA i k|) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |A i j * ΔA i k + ΔA i j * A i k + ΔA i j * ΔA i k|
              ≤ |A i j * ΔA i k| + |ΔA i j * A i k| +
                  |ΔA i j * ΔA i k| := by
                exact abs_add_three _ _ _
          _ = |A i j| * |ΔA i k| + |ΔA i j| * |A i k| +
                |ΔA i j| * |ΔA i k| := by
                rw [abs_mul, abs_mul, abs_mul]
/-- Frobenius-norm bound for the induced Gram perturbation from the exact
    entrywise budget. -/
theorem rectLSGramPerturbation_frobNorm_le_entryBudget {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) :
    frobNorm (rectLSGramPerturbation A ΔA) ≤
      frobNorm (rectLSGramPerturbationEntryBudget A ΔA) := by
  apply frobNorm_le_of_entry_abs_le
  · exact rectLSGramPerturbationEntryBudget_nonneg A ΔA
  · exact rectLSGramPerturbation_abs_le_entryBudget A ΔA
/-- The induced Gram perturbation is bounded entrywise by the coarse
    Frobenius-norm data-perturbation budget. -/
theorem rectLSGramPerturbation_abs_le_normBudget {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) {cA : ℝ}
    (hΔA : frobNorm ΔA ≤ cA) :
    ∀ j k : Fin n,
      |rectLSGramPerturbation A ΔA j k| ≤
        rectLSGramPerturbationNormBudget A cA j k := by
  intro j k
  have hentry := rectLSGramPerturbation_abs_le_entryBudget A ΔA j k
  calc
    |rectLSGramPerturbation A ΔA j k|
        ≤ rectLSGramPerturbationEntryBudget A ΔA j k := hentry
    _ ≤ rectLSGramPerturbationNormBudget A cA j k := by
        unfold rectLSGramPerturbationEntryBudget rectLSGramPerturbationNormBudget
        apply Finset.sum_le_sum
        intro i _
        have hΔAij : |ΔA i j| ≤ cA :=
          (abs_entry_le_frobNorm ΔA i j).trans hΔA
        have hΔAik : |ΔA i k| ≤ cA :=
          (abs_entry_le_frobNorm ΔA i k).trans hΔA
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hΔAik (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hΔAij (abs_nonneg _)))
          (mul_le_mul hΔAij hΔAik (abs_nonneg _) (le_trans (abs_nonneg _) hΔAik))
/-- Frobenius-norm bound for the induced Gram perturbation from a coarse
    Frobenius-norm data-perturbation radius. -/
theorem rectLSGramPerturbation_frobNorm_le_normBudget {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) {cA : ℝ}
    (hcA : 0 ≤ cA) (hΔA : frobNorm ΔA ≤ cA) :
    frobNorm (rectLSGramPerturbation A ΔA) ≤
      frobNorm (rectLSGramPerturbationNormBudget A cA) := by
  apply frobNorm_le_of_entry_abs_le
  · exact rectLSGramPerturbationNormBudget_nonneg A hcA
  · exact rectLSGramPerturbation_abs_le_normBudget A ΔA hΔA
private theorem frobNormRect_sq_eq_complexMatrixFrobeniusSq_realRect
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    frobNormRect A ^ 2 =
      complexMatrixFrobeniusSq (realRectToCMatrix A) := by
  rw [frobNormRect_sq]
  simp [frobNormSqRect, complexMatrixFrobeniusSq, realRectToCMatrix,
    Real.norm_eq_abs, sq_abs]
/-- Rectangular real Frobenius norm squared is bounded by the number of
columns times the squared Euclidean operator norm. -/
theorem frobNormRect_sq_le_card_mul_complexMatrixOp2_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    frobNormRect A ^ 2 <=
      (n : Real) * complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  rw [frobNormRect_sq_eq_complexMatrixFrobeniusSq_realRect]
  exact complexMatrixFrobeniusSq_le_card_mul_complexMatrixOp2_sq
    (realRectToCMatrix A)
/-- The exact entrywise Gram majorant `|A^T||A|`. -/
noncomputable def higham20NormalEqAbsGram {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => Finset.univ.sum (fun k : Fin m => |A k i| * |A k j|)
/-- The exact entrywise right-hand-side majorant `|A^T||b|`. -/
noncomputable def higham20NormalEqAbsRhs {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) : Fin n -> Real :=
  fun j => Finset.univ.sum (fun i : Fin m => |A i j| * |b i|)
/-- The natural Gram majorant has the source envelope
`|| |A^T||A| ||_F <= n ||A||_2^2`. -/
theorem higham20NormalEqAbsGram_frobNormRect_le {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    frobNormRect (higham20NormalEqAbsGram A) <=
      (n : Real) * complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  let Aabs : Fin m -> Fin n -> Real := absMatrixRect A
  have hprod :
      higham20NormalEqAbsGram A =
        rectMatMul (finiteTranspose Aabs) Aabs := by
    ext i j
    simp [higham20NormalEqAbsGram, rectMatMul, finiteTranspose, Aabs,
      absMatrixRect]
  rw [hprod]
  calc
    frobNormRect (rectMatMul (finiteTranspose Aabs) Aabs) <=
        frobNormRect (finiteTranspose Aabs) * frobNormRect Aabs :=
      frobNormRect_rectMatMul_le _ _
    _ = frobNormRect A ^ 2 := by
      rw [frobNormRect_finiteTranspose]
      have habs : frobNormRect Aabs = frobNormRect A := by
        simpa [Aabs, absMatrixRect] using frobNormRect_abs A
      rw [habs]
      ring
    _ <= (n : Real) * complexMatrixOp2 (realRectToCMatrix A) ^ 2 :=
      frobNormRect_sq_le_card_mul_complexMatrixOp2_sq A
private theorem higham20_realRectMatrixRank_finiteTranspose
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    realRectMatrixRank (finiteTranspose A) = realRectMatrixRank A := by
  unfold realRectMatrixRank complexMatrixRank
  have hmatrix :
      (realRectToCMatrix (finiteTranspose A) :
          Matrix (Fin n) (Fin m) Complex) =
        Matrix.transpose
          (realRectToCMatrix A : Matrix (Fin m) (Fin n) Complex) := by
    ext i j
    rfl
  rw [hmatrix, Matrix.rank_transpose]
private theorem higham20_realRectMatrixRank_le_width
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    realRectMatrixRank A <= n := by
  simpa [realRectMatrixRank, complexMatrixRank] using
    (Matrix.rank_le_width
      (realRectToCMatrix A : Matrix (Fin m) (Fin n) Complex))
/-- The natural RHS majorant has the source envelope
`|| |A^T||b| ||_2 <= sqrt(n) ||A||_2 ||b||_2`. -/
theorem higham20NormalEqAbsRhs_vecNorm2_le {m n : Nat}
    (hn : 0 < n) (hmn : n <= m)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    vecNorm2 (higham20NormalEqAbsRhs A b) <=
      Real.sqrt (n : Real) * complexMatrixOp2 (realRectToCMatrix A) *
        vecNorm2 b := by
  let AT : Fin n -> Fin m -> Real := finiteTranspose A
  have hm : 0 < m := lt_of_lt_of_le hn hmn
  have hATbase :
      rectOpNorm2Le AT (complexMatrixOp2 (realRectToCMatrix AT)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le AT le_rfl
  have hATabs0 :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hm AT (complexMatrixOp2_nonneg _) hATbase
  have hrank : realRectMatrixRank AT <= n := by
    rw [show AT = finiteTranspose A by rfl,
      higham20_realRectMatrixRank_finiteTranspose]
    exact higham20_realRectMatrixRank_le_width A
  have hsqrt :
      Real.sqrt (realRectMatrixRank AT : Real) <= Real.sqrt (n : Real) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrank)
  have hATnorm :
      complexMatrixOp2 (realRectToCMatrix AT) =
        complexMatrixOp2 (realRectToCMatrix A) := by
    simpa [AT] using
      complexMatrixOp2_realRectToCMatrix_finiteTranspose_eq A
  have hATabs :
      rectOpNorm2Le (absMatrixRect AT)
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix A)) := by
    apply rectOpNorm2Le_mono _ hATabs0
    rw [hATnorm]
    exact mul_le_mul_of_nonneg_right hsqrt (complexMatrixOp2_nonneg _)
  have haction :
      higham20NormalEqAbsRhs A b =
        rectMatMulVec (absMatrixRect AT) (absVec m b) := by
    ext j
    simp [higham20NormalEqAbsRhs, rectMatMulVec, absMatrixRect,
      finiteTranspose, AT, absVec]
  rw [haction]
  calc
    vecNorm2 (rectMatMulVec (absMatrixRect AT) (absVec m b)) <=
        (Real.sqrt (n : Real) *
          complexMatrixOp2 (realRectToCMatrix A)) *
            vecNorm2 (absVec m b) := hATabs _
    _ = Real.sqrt (n : Real) *
        complexMatrixOp2 (realRectToCMatrix A) * vecNorm2 b := by
      rw [show vecNorm2 (absVec m b) = vecNorm2 b by
        simpa [absVec] using vecNorm2_abs b]
/-- The absolute Gram majorant of a square factor is bounded by the square
of its Frobenius norm. -/
theorem higham20NormalEqAbsGram_frobNormRect_le_frobNormRect_sq {n : Nat}
    (R : Fin n -> Fin n -> Real) :
    frobNormRect (higham20NormalEqAbsGram R) <= frobNormRect R ^ 2 := by
  let Rabs : Fin n -> Fin n -> Real := absMatrixRect R
  have hprod :
      higham20NormalEqAbsGram R =
        rectMatMul (finiteTranspose Rabs) Rabs := by
    ext i j
    simp [higham20NormalEqAbsGram, rectMatMul, finiteTranspose, Rabs,
      absMatrixRect]
  rw [hprod]
  calc
    frobNormRect (rectMatMul (finiteTranspose Rabs) Rabs) <=
        frobNormRect (finiteTranspose Rabs) * frobNormRect Rabs :=
      frobNormRect_rectMatMul_le _ _
    _ = frobNormRect R ^ 2 := by
      rw [frobNormRect_finiteTranspose]
      have habs : frobNormRect Rabs = frobNormRect R := by
        simpa [Rabs, absMatrixRect] using frobNormRect_abs R
      rw [habs]
      ring

end NumStability
