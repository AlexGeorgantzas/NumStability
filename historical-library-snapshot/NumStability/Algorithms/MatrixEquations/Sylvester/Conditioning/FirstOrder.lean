import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

-- Algorithms/Sylvester/SylvesterPerturbation.lean
--
-- Perturbation theory for the Sylvester equation (Higham §15.3).
-- Eqs 15.22-15.28: linearized perturbation equation, first-order
-- perturbation bound, a posteriori error bound, and Lyapunov specialization.












namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Linearized perturbation equation (§15.3, eq 15.22)
-- ============================================================














































-- ============================================================
-- Structured first-order condition-number surface (§16.3, eqs 16.23-16.24)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    Euclidean norm of the three normalized data perturbation blocks
    `(ΔA / α, ΔB / β, ΔC / γ)`, represented with Frobenius norms for the
    matrix blocks. -/
noncomputable def sylvesterScaledPerturbationTripleNorm (n : ℕ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ) (α β γ : ℝ) : ℝ :=
  Real.sqrt
    (frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
      frobNormSq ΔC / γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    if each normalized perturbation block has Frobenius norm at most `ε`,
    then the stacked normalized perturbation vector has norm at most
    `sqrt 3 * ε`. -/
theorem sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul (n : ℕ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ) (α β γ ε : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ) :
    sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ ≤
      Real.sqrt 3 * ε := by
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
  have hβ2 : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hγ2 : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have hΔA_sq : frobNormSq ΔA ≤ (ε * α) ^ 2 := by
    rw [← frobNorm_sq ΔA]
    nlinarith [frobNorm_nonneg ΔA, hΔA, hε, le_of_lt hα]
  have hΔB_sq : frobNormSq ΔB ≤ (ε * β) ^ 2 := by
    rw [← frobNorm_sq ΔB]
    nlinarith [frobNorm_nonneg ΔB, hΔB, hε, le_of_lt hβ]
  have hΔC_sq : frobNormSq ΔC ≤ (ε * γ) ^ 2 := by
    rw [← frobNorm_sq ΔC]
    nlinarith [frobNorm_nonneg ΔC, hΔC, hε, le_of_lt hγ]
  have hΔA_div : frobNormSq ΔA / α ^ 2 ≤ ε ^ 2 := by
    rw [div_le_iff₀ hα2]
    nlinarith
  have hΔB_div : frobNormSq ΔB / β ^ 2 ≤ ε ^ 2 := by
    rw [div_le_iff₀ hβ2]
    nlinarith
  have hΔC_div : frobNormSq ΔC / γ ^ 2 ≤ ε ^ 2 := by
    rw [div_le_iff₀ hγ2]
    nlinarith
  have hsum :
      frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
          frobNormSq ΔC / γ ^ 2 ≤
        3 * ε ^ 2 := by
    nlinarith
  unfold sylvesterScaledPerturbationTripleNorm
  calc
    Real.sqrt
        (frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
          frobNormSq ΔC / γ ^ 2)
        ≤ Real.sqrt (3 * ε ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * ε := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hε]

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24), certificate form:
    `Ψ` bounds the structured inverse first-order Sylvester perturbation map.
    This is the theorem-facing predicate corresponding to the operator norm
    `‖P^{-1}[α(Xᵀ⊗I) -β(I⊗X) -γI]‖₂ / ‖X‖_F`; a later exact operator-norm
    realization can instantiate this predicate. -/
def SylvesterPsiFirstOrderBound (n : ℕ)
    (A B X : Fin n → Fin n → ℝ) (α β γ Ψ : ℝ) : Prop :=
  ∀ ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ,
    (∀ i j, sylvesterOp n A B ΔX i j =
      ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) →
    frobNorm ΔX ≤
      Ψ * frobNorm X *
        sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23):
    the sharp first-order perturbation estimate follows from the structured
    condition-number certificate (16.24) and the three normwise data budgets. -/
theorem sylvester_relative_first_order_bound_of_psi (n : ℕ)
    (A B X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (α β γ Ψ ε : ℝ)
    (hPsi : SylvesterPsiFirstOrderBound n A B X α β γ Ψ)
    (hX : 0 < frobNorm X)
    (hΨ : 0 ≤ Ψ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j, sylvesterOp n A B ΔX i j =
      ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) :
    frobNorm ΔX / frobNorm X ≤ Real.sqrt 3 * Ψ * ε := by
  have htriple :=
    sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul n
      ΔA ΔB ΔC α β γ ε hα hβ hγ hε hΔA hΔB hΔC
  have hbase := hPsi ΔA ΔB ΔC ΔX hLin
  have hscale_nonneg : 0 ≤ Ψ * frobNorm X :=
    mul_nonneg hΨ (le_of_lt hX)
  have hbound :
      frobNorm ΔX ≤ Ψ * frobNorm X * (Real.sqrt 3 * ε) := by
    exact hbase.trans (mul_le_mul_of_nonneg_left htriple hscale_nonneg)
  rw [div_le_iff₀ hX]
  calc
    frobNorm ΔX ≤ Ψ * frobNorm X * (Real.sqrt 3 * ε) := hbound
    _ = (Real.sqrt 3 * Ψ * ε) * frobNorm X := by ring
















-- ============================================================
-- Lyapunov first-order condition-number surface (§16.3, eq 16.27)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    Euclidean norm of the two normalized Lyapunov data perturbation blocks
    `(DeltaA / alpha, DeltaC / gamma)`, represented with Frobenius norms for
    the matrix blocks. -/
noncomputable def lyapunovScaledPerturbationPairNorm (n : ℕ)
    (ΔA ΔC : Fin n → Fin n → ℝ) (α γ : ℝ) : ℝ :=
  Real.sqrt (frobNormSq ΔA / α ^ 2 + frobNormSq ΔC / γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    if each normalized Lyapunov perturbation block has Frobenius norm at most
    `epsilon`, then the stacked normalized pair has norm at most
    `sqrt 2 * epsilon`. -/
theorem lyapunovScaledPerturbationPairNorm_le_sqrt_two_mul (n : ℕ)
    (ΔA ΔC : Fin n → Fin n → ℝ) (α γ ε : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔC : frobNorm ΔC ≤ ε * γ) :
    lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ ≤
      Real.sqrt 2 * ε := by
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
  have hγ2 : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have hΔA_sq : frobNormSq ΔA ≤ (ε * α) ^ 2 := by
    rw [← frobNorm_sq ΔA]
    nlinarith [frobNorm_nonneg ΔA, hΔA, hε, le_of_lt hα]
  have hΔC_sq : frobNormSq ΔC ≤ (ε * γ) ^ 2 := by
    rw [← frobNorm_sq ΔC]
    nlinarith [frobNorm_nonneg ΔC, hΔC, hε, le_of_lt hγ]
  have hΔA_div : frobNormSq ΔA / α ^ 2 ≤ ε ^ 2 := by
    rw [div_le_iff₀ hα2]
    nlinarith
  have hΔC_div : frobNormSq ΔC / γ ^ 2 ≤ ε ^ 2 := by
    rw [div_le_iff₀ hγ2]
    nlinarith
  have hsum :
      frobNormSq ΔA / α ^ 2 + frobNormSq ΔC / γ ^ 2 ≤
        2 * ε ^ 2 := by
    nlinarith
  unfold lyapunovScaledPerturbationPairNorm
  calc
    Real.sqrt (frobNormSq ΔA / α ^ 2 + frobNormSq ΔC / γ ^ 2)
        ≤ Real.sqrt (2 * ε ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * ε := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hε]

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), certificate form:
    `Psi` bounds the structured inverse first-order Lyapunov perturbation map.
    This is the theorem-facing predicate corresponding to the printed
    vec-permutation operator norm; a later exact inverse/operator-norm
    realization can instantiate this predicate. -/
def LyapunovConditionFirstOrderBound (n : ℕ)
    (A X : Fin n → Fin n → ℝ) (α γ Ψ : ℝ) : Prop :=
  ∀ ΔA ΔC ΔX : Fin n → Fin n → ℝ,
    (∀ i j, lyapunovOp n A ΔX i j =
      ΔC i j - matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) →
    frobNorm ΔX ≤
      Ψ * frobNorm X *
        lyapunovScaledPerturbationPairNorm n ΔA ΔC α γ

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    the Lyapunov first-order relative perturbation estimate follows from the
    condition-number certificate and the two normwise data budgets. -/
theorem lyapunov_relative_first_order_bound_of_condition (n : ℕ)
    (A X ΔA ΔC ΔX : Fin n → Fin n → ℝ)
    (α γ Ψ ε : ℝ)
    (hCond : LyapunovConditionFirstOrderBound n A X α γ Ψ)
    (hX : 0 < frobNorm X)
    (hΨ : 0 ≤ Ψ)
    (hα : 0 < α) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j, lyapunovOp n A ΔX i j =
      ΔC i j - matMul n ΔA X i j - matMul n X (matTranspose ΔA) i j) :
    frobNorm ΔX / frobNorm X ≤ Real.sqrt 2 * Ψ * ε := by
  have hpair :=
    lyapunovScaledPerturbationPairNorm_le_sqrt_two_mul n
      ΔA ΔC α γ ε hα hγ hε hΔA hΔC
  have hbase := hCond ΔA ΔC ΔX hLin
  have hscale_nonneg : 0 ≤ Ψ * frobNorm X :=
    mul_nonneg hΨ (le_of_lt hX)
  have hbound :
      frobNorm ΔX ≤ Ψ * frobNorm X * (Real.sqrt 2 * ε) := by
    exact hbase.trans (mul_le_mul_of_nonneg_left hpair hscale_nonneg)
  rw [div_le_iff₀ hX]
  calc
    frobNorm ΔX ≤ Ψ * frobNorm X * (Real.sqrt 2 * ε) := hbound
    _ = (Real.sqrt 2 * Ψ * ε) * frobNorm X := by ring
















-- ============================================================
-- First-order perturbation bound (§15.3, eq 15.25)
-- ============================================================











































































-- ============================================================
-- A posteriori error bound (§15.3, eq 15.28)
-- ============================================================











































-- ============================================================
-- Lyapunov perturbation (§15.3, eq 15.27)
-- ============================================================

































-- ============================================================
-- Relative perturbation bound (§15.3, eq 15.25 relative form)
-- ============================================================

/-- **Relative perturbation bound** (eq 15.25, relative form):
    ‖ΔX‖_F / ‖X‖_F ≤ (1/sep(A,B)) · ((α+β)‖X‖_F + γ) / ‖X‖_F · ε
    = κ_Sylv(A,B,X) · ε
    where κ_Sylv = ((α+β)‖X‖_F + γ) / (sep(A,B) · ‖X‖_F) is the
    condition number for the Sylvester equation. -/
noncomputable def condSylvester (n : ℕ) (_A _B X : Fin n → Fin n → ℝ)
    (α β γ σ : ℝ) : ℝ :=
  ((α + β) * frobNorm X + γ) /
    (σ * frobNorm X)










































end NumStability
