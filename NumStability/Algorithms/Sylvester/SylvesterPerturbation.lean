-- Algorithms/Sylvester/SylvesterPerturbation.lean
--
-- Perturbation theory for the Sylvester equation (Higham §15.3).
-- Eqs 15.22-15.28: linearized perturbation equation, first-order
-- perturbation bound, a posteriori error bound, and Lyapunov specialization.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.Sylvester.SylvesterSpec

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Linearized perturbation equation (§15.3, eq 15.22)
-- ============================================================

/-- **Linearized perturbation equation** (eq 15.22):
    If AX - XB = C and (A+ΔA)(X+ΔX) - (X+ΔX)(B+ΔB) = C+ΔC, then
      A·ΔX - ΔX·B = ΔC - ΔA·X + X·ΔB + (ΔX·ΔB - ΔA·ΔX).
    The first-order terms are ΔC - ΔA·X + X·ΔB. -/
theorem sylvester_perturbation_equation (n : ℕ)
    (A B C X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (hExact : ∀ i j, sylvesterOp n A B X i j = C i j)
    (hPerturbed : ∀ i j, sylvesterOp n
      (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j')
      (fun i' j' => X i' j' + ΔX i' j') i j = C i j + ΔC i j) :
    ∀ i j, sylvesterOp n A B ΔX i j =
      ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j
      - matMul n ΔA ΔX i j + matMul n ΔX ΔB i j := by
  intro i j
  have hE := hExact i j
  have hP := hPerturbed i j
  unfold sylvesterOp at hE hP ⊢
  unfold matMul at hE hP ⊢
  simp only [add_mul, mul_add, Finset.sum_add_distrib] at hP
  linarith

/-- **First-order perturbation equation interface**
    (eq 15.22, dropping second-order terms):
    A·ΔX - ΔX·B = ΔC - ΔA·X + X·ΔB.

    The linearized equation is supplied as `hLin`; the nonlinear perturbation
    identity above records where the omitted second-order terms come from. -/
theorem sylvester_perturbation_first_order (n : ℕ)
    (A B X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (hLin : ∀ i j, sylvesterOp n A B ΔX i j =
      ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) :
    ∀ i j, sylvesterOp n A B ΔX i j =
      ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j :=
  hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.22):
    source-numbered aliases for the full and first-order Sylvester
    perturbation identities. -/
alias H16_eq16_22_sylvester_perturbation_equation :=
  sylvester_perturbation_equation

alias H16_eq16_22_sylvester_perturbation_first_order :=
  sylvester_perturbation_first_order

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

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-numbered aliases for the primitive structured Sylvester first-order
    condition-number surface. -/
noncomputable abbrev H16_eq16_23_sylvesterScaledPerturbationTripleNorm :=
  sylvesterScaledPerturbationTripleNorm

alias H16_eq16_23_sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul :=
  sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul

abbrev H16_eq16_24_SylvesterPsiFirstOrderBound :=
  SylvesterPsiFirstOrderBound

alias H16_eq16_23_sylvester_relative_first_order_bound_of_psi :=
  sylvester_relative_first_order_bound_of_psi

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

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered aliases for the primitive structured Lyapunov first-order
    condition-number surface. -/
noncomputable abbrev H16_eq16_27_lyapunovScaledPerturbationPairNorm :=
  lyapunovScaledPerturbationPairNorm

alias H16_eq16_27_lyapunovScaledPerturbationPairNorm_le_sqrt_two_mul :=
  lyapunovScaledPerturbationPairNorm_le_sqrt_two_mul

abbrev H16_eq16_27_LyapunovConditionFirstOrderBound :=
  LyapunovConditionFirstOrderBound

alias H16_eq16_27_lyapunov_relative_first_order_bound_of_condition :=
  lyapunov_relative_first_order_bound_of_condition

-- ============================================================
-- First-order perturbation bound (§15.3, eq 15.25)
-- ============================================================

/-- **First-order perturbation bound** (eq 15.25):
    If A·ΔX - ΔX·B = ΔC - ΔA·X + X·ΔB and sep(A,B) ≥ σ > 0, then
      ‖ΔX‖_F ≤ (1/σ) · ((α+β)‖X‖_F + γ) · ε
    where ‖ΔA‖_F ≤ εα, ‖ΔB‖_F ≤ εβ, ‖ΔC‖_F ≤ εγ.

    This combines the sep bound ‖ΔX‖_F ≤ (1/σ)‖T(ΔX)‖_F with the
    triangle inequality on the RHS. -/
theorem sylvester_perturbation_bound (n : ℕ)
    (A B X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hSep : SepLowerBound n A B σ)
    (α β γ ε : ℝ) (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hγ : 0 ≤ γ) (_hε : 0 ≤ ε)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j, sylvesterOp n A B ΔX i j =
      ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j)
    (hΔX_ne : frobNormSq ΔX ≠ 0) :
    frobNorm ΔX ≤
      (1 / σ) * ((α + β) * frobNorm X + γ) * ε := by
  -- Step 1: sep bound gives σ‖ΔX‖_F ≤ ‖A·ΔX - ΔX·B‖_F
  have hSepBound : σ * frobNorm ΔX ≤
      frobNorm (sylvesterOp n A B ΔX) := by
    have h := hSep.2 ΔX hΔX_ne
    -- h : σ² · ‖ΔX‖²_F ≤ ‖T(ΔX)‖²_F
    -- Take sqrt: σ · ‖ΔX‖_F ≤ ‖T(ΔX)‖_F
    have hσ_nn : 0 ≤ σ := le_of_lt hσ
    rw [← frobNorm_sq, ← frobNorm_sq] at h
    have h1 : σ * frobNorm ΔX ≥ 0 :=
      mul_nonneg hσ_nn (frobNorm_nonneg ΔX)
    nlinarith [sq_nonneg (σ * frobNorm ΔX -
                  frobNorm (sylvesterOp n A B ΔX)),
               frobNorm_nonneg (sylvesterOp n A B ΔX)]
  -- Step 2: ‖T(ΔX)‖_F = ‖RHS‖_F ≤ ‖ΔC‖_F + ‖ΔA·X‖_F + ‖X·ΔB‖_F
  --         ≤ εγ + εα‖X‖_F + ‖X‖_Fεβ = ε((α+β)‖X‖_F + γ)
  have hRHS : frobNorm (sylvesterOp n A B ΔX) ≤
      ((α + β) * frobNorm X + γ) * ε := by
    -- Rewrite T(ΔX) using the linearized equation
    have hReq :
        frobNorm (sylvesterOp n A B ΔX) =
        frobNorm (fun i j =>
          ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) := by
      congr 1; ext i j; exact hLin i j
    rw [hReq]
    -- ‖ΔC - ΔA·X + X·ΔB‖_F = ‖(ΔC + X·ΔB) + (-ΔA·X)‖_F
    -- ≤ ‖ΔC + X·ΔB‖_F + ‖ΔA·X‖_F ≤ (‖ΔC‖_F + ‖X·ΔB‖_F) + ‖ΔA·X‖_F
    -- Write as ΔC + (X·ΔB - ΔA·X)
    have h_rw : (fun i j => ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) =
        (fun i j => ΔC i j + (matMul n X ΔB i j - matMul n ΔA X i j)) := by
      ext i j; ring
    rw [h_rw]
    -- Triangle: ‖ΔC + (X·ΔB - ΔA·X)‖_F ≤ ‖ΔC‖_F + ‖X·ΔB - ΔA·X‖_F
    have htri1 := frobNorm_add_le ΔC
      (fun i j => matMul n X ΔB i j - matMul n ΔA X i j)
    -- ‖X·ΔB - ΔA·X‖_F ≤ ‖X·ΔB‖_F + ‖ΔA·X‖_F
    have htri2 := frobNorm_sub_le (matMul n X ΔB) (matMul n ΔA X)
    -- ‖ΔA·X‖_F ≤ ‖ΔA‖_F · ‖X‖_F ≤ εα · ‖X‖_F
    have hAX : frobNorm (matMul n ΔA X) ≤
        ε * α * frobNorm X :=
      le_trans (frobNorm_matMul_le ΔA X)
        (mul_le_mul_of_nonneg_right hΔA (frobNorm_nonneg X))
    -- ‖X·ΔB‖_F ≤ ‖X‖_F · ‖ΔB‖_F ≤ ‖X‖_F · εβ
    have hXB : frobNorm (matMul n X ΔB) ≤
        frobNorm X * (ε * β) :=
      le_trans (frobNorm_matMul_le X ΔB)
        (mul_le_mul_of_nonneg_left hΔB (frobNorm_nonneg X))
    linarith
  -- Step 3: Combine: σ‖ΔX‖_F ≤ ε((α+β)‖X‖_F + γ), so ‖ΔX‖_F ≤ (1/σ)ε((α+β)‖X‖_F + γ)
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  rw [show (1 / σ) * ((α + β) *
        frobNorm X + γ) * ε =
      ((α + β) * frobNorm X + γ) * ε / σ from by ring]
  rw [le_div_iff₀ hσ]
  linarith

-- ============================================================
-- A posteriori error bound (§15.3, eq 15.28)
-- ============================================================

/-- **A posteriori error bound** (eq 15.28):
    If AX - XB = C and X̂ is an approximate solution, then
      ‖X - X̂‖_F ≤ (1/sep(A,B)) · ‖R‖_F
    where R = C - (AX̂ - X̂B) is the residual.

    This is the fundamental error-residual relationship: the error
    is bounded by the residual divided by sep(A,B). -/
theorem sylvester_aposteriori_bound (n : ℕ)
    (A B C X X_hat : Fin n → Fin n → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hSep : SepLowerBound n A B σ)
    (hExact : ∀ i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : frobNormSq (fun i j => X i j - X_hat i j) ≠ 0) :
    frobNorm (fun i j => X i j - X_hat i j) ≤
      (1 / σ) * frobNorm (sylvesterResidual n A B C X_hat) := by
  -- E = X - X̂ satisfies A·E - E·B = R (residual)
  have hE_eq : ∀ i j, sylvesterOp n A B (fun i' j' => X i' j' - X_hat i' j') i j =
      sylvesterResidual n A B C X_hat i j := by
    intro i j
    have h := hExact i j
    unfold sylvesterOp matMul at h ⊢
    unfold sylvesterResidual sylvesterOp matMul
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]; linarith
  -- sep bound: σ‖E‖_F ≤ ‖A·E - E·B‖_F = ‖R‖_F
  have hSepBound := hSep.2 _ hE_ne
  have hσ_nn : 0 ≤ σ := le_of_lt hσ
  rw [← frobNorm_sq, ← frobNorm_sq] at hSepBound
  -- σ · ‖E‖_F ≤ ‖T(E)‖_F = ‖R‖_F
  have hReq :
      frobNorm (sylvesterOp n A B (fun i' j' => X i' j' - X_hat i' j')) =
      frobNorm (sylvesterResidual n A B C X_hat) := by
    congr 1; ext i j; exact hE_eq i j
  rw [show (1 / σ) * frobNorm (sylvesterResidual n A B C X_hat) =
      frobNorm (sylvesterResidual n A B C X_hat) / σ
      from by ring]
  rw [le_div_iff₀ hσ, ← hReq]
  -- Need: σ · ‖E‖_F ≤ ‖T(E)‖_F
  -- From hSepBound: σ² · ‖E‖²_F ≤ ‖T(E)‖²_F
  nlinarith [sq_nonneg (σ *
               frobNorm (fun i j => X i j - X_hat i j) -
               frobNorm (sylvesterOp n A B (fun i' j' => X i' j' - X_hat i' j'))),
             frobNorm_nonneg (sylvesterOp n A B (fun i' j' => X i' j' - X_hat i' j'))]

-- ============================================================
-- Lyapunov perturbation (§15.3, eq 15.27)
-- ============================================================

/-- **Lyapunov perturbation bound** (eq 15.27):
    For the Lyapunov equation AX + XAᵀ = C (B = -Aᵀ), the perturbation
    ΔB = -ΔAᵀ is determined by ΔA, giving the tighter bound
      ‖ΔX‖_F ≤ (1/sep(A,-Aᵀ)) · (2α‖X‖_F + γ) · ε
    where ‖ΔA‖_F ≤ εα and ‖ΔC‖_F ≤ εγ.

    The factor 2α replaces (α+β) since β = α for the Lyapunov case. -/
theorem lyapunov_perturbation_bound (n : ℕ)
    (A X ΔA ΔC ΔX : Fin n → Fin n → ℝ)
    (σ : ℝ) (hσ : 0 < σ)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) σ)
    (α γ ε : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    -- ΔB = -ΔAᵀ, and ‖ΔAᵀ‖_F = ‖ΔA‖_F ≤ εα
    (hLin : ∀ i j, sylvesterOp n A (fun i' j' => -matTranspose A i' j') ΔX i j =
      ΔC i j - matMul n ΔA X i j +
      matMul n X (fun i' j' => -matTranspose ΔA i' j') i j)
    (hΔX_ne : frobNormSq ΔX ≠ 0) :
    frobNorm ΔX ≤
      (1 / σ) * (2 * α * frobNorm X + γ) * ε := by
  -- ‖-ΔAᵀ‖_F = ‖ΔA‖_F (negation + transpose preserve Frobenius norm)
  have hΔB : frobNorm (fun i j => -matTranspose ΔA i j) ≤ ε * α := by
    rw [show (fun i j => -matTranspose ΔA i j) =
        (fun i j => -(matTranspose ΔA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hΔA
  have h := sylvester_perturbation_bound n A _ X ΔA
    (fun i j => -matTranspose ΔA i j) ΔC ΔX σ hσ hSep α α γ ε hα hα hγ hε
    hΔA hΔB hΔC hLin hΔX_ne
  linarith

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

/-- The relative perturbation bound in terms of κ_Sylv. -/
theorem sylvester_relative_perturbation (n : ℕ)
    (A B X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hSep : SepLowerBound n A B σ)
    (α β γ ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j, sylvesterOp n A B ΔX i j =
      ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j)
    (hΔX_ne : frobNormSq ΔX ≠ 0)
    (hX_ne : frobNorm X ≠ 0)
    (hX_pos : 0 < frobNorm X) :
    frobNorm ΔX /
      frobNorm X ≤
      condSylvester n A B X α β γ σ * ε := by
  have habs := sylvester_perturbation_bound n A B X ΔA ΔB ΔC ΔX σ hσ hSep
    α β γ ε hα hβ hγ hε hΔA hΔB hΔC hLin hΔX_ne
  -- habs: ‖ΔX‖ ≤ (1/σ)((α+β)‖X‖+γ)ε
  -- Goal: ‖ΔX‖/‖X‖ ≤ κ·ε where κ = ((α+β)‖X‖+γ)/(σ·‖X‖)
  -- Divide habs by ‖X‖: ‖ΔX‖/‖X‖ ≤ (1/σ)((α+β)‖X‖+γ)ε/‖X‖ = κ·ε
  unfold condSylvester
  rw [div_le_iff₀ hX_pos]
  calc frobNorm ΔX
      ≤ 1 / σ * ((α + β) * frobNorm X + γ) * ε := habs
    _ = ((α + β) * frobNorm X + γ) /
          (σ * frobNorm X) * ε *
          frobNorm X := by
        field_simp

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered aliases for the base sep-certificate Sylvester
    perturbation bound and condition-number expression. -/
noncomputable abbrev H16_eq16_25_condSylvester := condSylvester

alias H16_eq16_25_sylvester_perturbation_bound :=
  sylvester_perturbation_bound

alias H16_eq16_25_sylvester_relative_perturbation :=
  sylvester_relative_perturbation

end NumStability
