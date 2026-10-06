import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Source.Higham.Chapter13.Theorem05.Recurrences

/-!
# Source.Higham.Chapter13.Theorem05.ErrorAnalysis

This module formalizes the source-facing Chapter 13 statements for
`Theorem05.ErrorAnalysis`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.2  Theorem 13.5 proof-step equations
-- ============================================================

/-- Higham, 2nd ed., Chapter 13, Section 13.1, equation (13.4):
    source-facing unpacking of the matrix-multiplication first-order model. -/
theorem higham13_eq13_4_from_matmul_spec {m n p : Type*} [Fintype n]
    (u c₁ normA normB normDelta : ℝ)
    (A : Matrix m n ℝ) (B : Matrix n p ℝ) (Chat DeltaC : Matrix m p ℝ)
    (h : MatMulFirstOrderSpec u c₁ normA normB normDelta A B Chat DeltaC) :
    Chat = A * B + DeltaC ∧
      MatMulFirstOrderBound u c₁ normA normB normDelta :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.1, equation (13.5):
    source-facing unpacking of the left triangular-solve first-order model. -/
theorem higham13_eq13_5_from_triangular_solve_spec {m p : Type*} [Fintype m]
    (u c₂ normT normXhat normDeltaB : ℝ)
    (T : Matrix m m ℝ) (B DeltaB Xhat : Matrix m p ℝ)
    (h : TriangularSolveFirstOrderSpec u c₂ normT normXhat normDeltaB
      T B DeltaB Xhat) :
    T * Xhat = B + DeltaB ∧
      TriangularSolveFirstOrderBound u c₂ normT normXhat normDeltaB :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.8):
    the off-diagonal block `Û₁₂` solve residual obtained from the triangular
    solve model (13.5). -/
theorem higham13_eq13_8_from_triangular_solve_spec {r s : Type*} [Fintype r]
    (u c₂ normLhat11 normUhat12 normDeltaA12 : ℝ)
    (Lhat11 : Matrix r r ℝ) (A12 DeltaA12 Uhat12 : Matrix r s ℝ)
    (h : TriangularSolveFirstOrderSpec u c₂ normLhat11 normUhat12 normDeltaA12
      Lhat11 A12 DeltaA12 Uhat12) :
    Lhat11 * Uhat12 = A12 + DeltaA12 ∧
      TriangularSolveFirstOrderBound u c₂ normLhat11 normUhat12 normDeltaA12 :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.9):
    the off-diagonal block `L̂₂₁` right-solve residual, using the transpose/right
    orientation of the triangular-solve model (13.5). -/
theorem higham13_eq13_9_from_right_triangular_solve_spec {r s : Type*} [Fintype r]
    (u c₂ normUhat11 normLhat21 normDeltaA21 : ℝ)
    (Uhat11 : Matrix r r ℝ) (A21 DeltaA21 Lhat21 : Matrix s r ℝ)
    (h : RightTriangularSolveFirstOrderSpec u c₂ normUhat11 normLhat21 normDeltaA21
      Uhat11 A21 DeltaA21 Lhat21) :
    Lhat21 * Uhat11 = A21 + DeltaA21 ∧
      TriangularSolveFirstOrderBound u c₂ normUhat11 normLhat21 normDeltaA21 :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.6):
    source-facing unpacking of the block-level LU first-order model. -/
theorem higham13_eq13_6_from_local_lu_spec {r : Type*} [Fintype r]
    (u c₃ normLhat normUhat normDeltaA : ℝ)
    (A DeltaA Lhat Uhat : Matrix r r ℝ)
    (h : LocalLUFirstOrderSpec u c₃ normLhat normUhat normDeltaA
      A DeltaA Lhat Uhat) :
    Lhat * Uhat = A + DeltaA ∧
      LocalLUFirstOrderBound u c₃ normLhat normUhat normDeltaA :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.10):
    source-facing unpacking of the computed subtraction residual model. -/
theorem higham13_eq13_10_from_subtraction_spec {m p : Type*}
    (u normA normComputed normF : ℝ)
    (A Computed F Shat : Matrix m p ℝ)
    (h : SubtractionFirstOrderSpec u normA normComputed normF A Computed F Shat) :
    Shat = A - Computed + F ∧ normF ≤ u * (normA + normComputed) :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equations (13.12a)--(13.12b):
    source-facing unpacking of the recursive induction hypothesis for the
    trailing Schur-complement factorization. -/
theorem higham13_eq13_12_from_induction_spec {r : Type*} [Fintype r]
    (u δ θ normShat normLhat22 normUhat22 normDeltaShat : ℝ)
    (Shat DeltaShat Lhat22 Uhat22 : Matrix r r ℝ)
    (h : PartitionedLUFirstOrderSpec u δ θ normShat normLhat22 normUhat22
      normDeltaShat Shat DeltaShat Lhat22 Uhat22) :
    Lhat22 * Uhat22 = Shat + DeltaShat ∧
      FirstOrderLe u
        (u * (δ * normShat + θ * normLhat22 * normUhat22))
        normDeltaShat :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.11a):
    combining the computed product `Ĉ = P + ΔC` with the computed subtraction
    `Ŝ = A₂₂ - Ĉ + F` gives `Ŝ = A₂₂ - P + (F - ΔC)`.

    This additive form is the exact algebraic core of the displayed
    `Ŝ = A₂₂ - L̂₂₁ Û₁₂ + ΔS`; for the source matrices, instantiate
    `P` with `L̂₂₁ Û₁₂` and `ΔS` with `F - ΔC`. -/
theorem higham13_eq13_11a_subtraction_error {α : Type*} [AddCommGroup α]
    (Shat A22 Chat F product DeltaC : α)
    (hsub : Shat = A22 - Chat + F)
    (hprod : Chat = product + DeltaC) :
    Shat = A22 - product + (F - DeltaC) := by
  rw [hsub, hprod]
  abel

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.11b), scalar
    first-order norm form.

    Equation (13.10) gives the subtraction error `F`, while (13.4) gives
    `Ĉ = L̂₂₁ Û₁₂ + ΔC`.  If `‖ΔS‖ ≤ ‖ΔC‖ + ‖F‖`, `‖Ĉ‖` is bounded by the
    product term plus `‖ΔC‖`, and the product error is first-order, then the
    displayed `‖ΔS‖` bound holds with an explicit second-order witness. -/
theorem higham13_eq13_11b_trailing_schur_error_firstOrder
    (normDeltaS normDeltaC normF normA22 normChat normL21 normU12 u c₁ : ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁)
    (_hA22 : 0 ≤ normA22) (hL21 : 0 ≤ normL21) (hU12 : 0 ≤ normU12)
    (hDeltaS : normDeltaS ≤ normDeltaC + normF)
    (hDeltaC : FirstOrderLe u (c₁ * u * normL21 * normU12) normDeltaC)
    (hF : normF ≤ u * (normA22 + normChat))
    (hChat : normChat ≤ normL21 * normU12 + normDeltaC) :
    FirstOrderLe u
      (u * (normA22 + normL21 * normU12 + c₁ * (normL21 * normU12)))
      normDeltaS := by
  rcases hDeltaC with ⟨K, hK, hDeltaC_bound⟩
  refine ⟨K * (1 + u) + c₁ * (normL21 * normU12), ?_, ?_⟩
  · have hu1 : 0 ≤ 1 + u := by linarith
    have hLU : 0 ≤ normL21 * normU12 := mul_nonneg hL21 hU12
    exact add_nonneg (mul_nonneg hK hu1) (mul_nonneg hc₁ hLU)
  · have hF_expanded :
        normF ≤ u * (normA22 + normL21 * normU12 + normDeltaC) := by
      have hinside : normA22 + normChat ≤
          normA22 + normL21 * normU12 + normDeltaC := by
        linarith
      exact le_trans hF (mul_le_mul_of_nonneg_left hinside hu)
    have hmain :
        normDeltaS ≤ normDeltaC +
          u * (normA22 + normL21 * normU12 + normDeltaC) := by
      linarith
    nlinarith [hmain, hDeltaC_bound]

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.11), assembled
    from the matrix-multiplication model (13.4) and subtraction model (13.10).

    The exact identity uses `ΔS = F - ΔC`, where `ΔC` is the product residual
    for `Ĉ = L̂₂₁Û₁₂ + ΔC` and `F` is the subtraction residual for
    `Ŝ = A₂₂ - Ĉ + F`.  The scalar conclusion is the first-order source bound
    for `‖ΔS‖`, retaining the norm aggregation assumptions explicitly. -/
theorem higham13_eq13_11_from_matmul_subtraction_specs
    {r s t : Type*} [Fintype r]
    (u c₁ normA22 normChat normF normL21 normU12 normDeltaC normDeltaS : ℝ)
    (Lhat21 : Matrix s r ℝ) (Uhat12 : Matrix r t ℝ)
    (A22 Chat DeltaC F Shat : Matrix s t ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁)
    (hA22 : 0 ≤ normA22) (hL21 : 0 ≤ normL21) (hU12 : 0 ≤ normU12)
    (hmul : MatMulFirstOrderSpec u c₁ normL21 normU12 normDeltaC
      Lhat21 Uhat12 Chat DeltaC)
    (hsub : SubtractionFirstOrderSpec u normA22 normChat normF A22 Chat F Shat)
    (hDeltaS : normDeltaS ≤ normDeltaC + normF)
    (hChat : normChat ≤ normL21 * normU12 + normDeltaC) :
    Shat = A22 - Lhat21 * Uhat12 + (F - DeltaC) ∧
      FirstOrderLe u
        (u * (normA22 + normL21 * normU12 + c₁ * (normL21 * normU12)))
        normDeltaS := by
  refine ⟨?_, ?_⟩
  · exact higham13_eq13_11a_subtraction_error
      Shat A22 Chat F (Lhat21 * Uhat12) DeltaC hsub.equation hmul.equation
  · exact higham13_eq13_11b_trailing_schur_error_firstOrder
      normDeltaS normDeltaC normF normA22 normChat normL21 normU12 u c₁
      hu hc₁ hA22 hL21 hU12 hDeltaS
      (by simpa [MatMulFirstOrderBound] using hmul.norm_bound)
      hsub.norm_bound hChat

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 proof boundary:
    rounded Schur-complement update, first-order scalar form.

    The recovered Pro audit of Higham Theorem 13.6 identified this as the
    first local layer needed before the recursive DHS factorization theorem:
    the product model (13.4) and subtraction model (13.10) assemble to
    `S_hat = A22 - L21_hat * U12_hat + DeltaS`, with the displayed
    first-order Schur-update bound. -/
theorem dhs_schur_update_firstOrder
    {r s t : Type*} [Fintype r]
    (u c₁ normA22 normChat normF normL21 normU12 normDeltaC normDeltaS : ℝ)
    (Lhat21 : Matrix s r ℝ) (Uhat12 : Matrix r t ℝ)
    (A22 Chat DeltaC F Shat : Matrix s t ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁)
    (hA22 : 0 ≤ normA22) (hL21 : 0 ≤ normL21) (hU12 : 0 ≤ normU12)
    (hmul : MatMulFirstOrderSpec u c₁ normL21 normU12 normDeltaC
      Lhat21 Uhat12 Chat DeltaC)
    (hsub : SubtractionFirstOrderSpec u normA22 normChat normF A22 Chat F Shat)
    (hDeltaS : normDeltaS ≤ normDeltaC + normF)
    (hChat : normChat ≤ normL21 * normU12 + normDeltaC) :
    Shat = A22 - Lhat21 * Uhat12 + (F - DeltaC) ∧
      FirstOrderLe u
        (u * (normA22 + normL21 * normU12 + c₁ * (normL21 * normU12)))
        normDeltaS :=
  higham13_eq13_11_from_matmul_subtraction_specs
    u c₁ normA22 normChat normF normL21 normU12 normDeltaC normDeltaS
    Lhat21 Uhat12 A22 Chat DeltaC F Shat hu hc₁ hA22 hL21 hU12 hmul
    hsub hDeltaS hChat

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.13), scalar
    first-order aggregation form.

    This combines the local trailing Schur perturbation `ΔS` with an already
    expanded recursive factorization perturbation `ΔŜ` to obtain the displayed
    first-order `ΔA₂₂` bound.  The theorem is deliberately scalar: the exact
    matrix identities around (13.12a) and the expansion of `‖Ŝ‖` from (13.10)
    remain separate proof-step obligations. -/
theorem higham13_eq13_13_trailing_block_error_firstOrder
    (normDeltaA22 normDeltaS normDeltaShat normA22 normL21U12 normL22U22
      u c₁ δ θ : ℝ)
    (hDeltaA22 : normDeltaA22 ≤ normDeltaS + normDeltaShat)
    (hDeltaS : FirstOrderLe u
      (u * (normA22 + normL21U12 + c₁ * normL21U12))
      normDeltaS)
    (hDeltaShat : FirstOrderLe u
      (u * (δ * normA22 + δ * normL21U12 + θ * normL22U22))
      normDeltaShat) :
    FirstOrderLe u
      (u * ((1 + δ) * normA22 + (1 + c₁ + δ) * normL21U12 +
        θ * normL22U22))
      normDeltaA22 := by
  refine (FirstOrderLe.add hDeltaS hDeltaShat hDeltaA22).mono_leading ?_
  ring_nf
  exact le_rfl

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.13), exact
    additive identity behind the trailing block.

    If `Ŝ = A₂₂ - P + ΔS` and the recursive factorization gives
    `Q = Ŝ + ΔŜ`, then `P + Q = A₂₂ + (ΔS + ΔŜ)`.  For the source display,
    instantiate `P` with `L̂₂₁Û₁₂` and `Q` with `L̂₂₂Û₂₂`. -/
theorem higham13_eq13_13_trailing_block_identity {α : Type*} [AddCommGroup α]
    (product recursiveProduct Shat A22 DeltaS DeltaShat : α)
    (hShat : Shat = A22 - product + DeltaS)
    (hRecursive : recursiveProduct = Shat + DeltaShat) :
    product + recursiveProduct = A22 + (DeltaS + DeltaShat) := by
  rw [hRecursive, hShat]
  abel

/-- Higham, 2nd ed., Chapter 13, Section 13.2, equation (13.13), assembled
    from the product/subtraction specs and the recursive induction spec.

    This is the source proof step after (13.11)--(13.12): the exact trailing
    block residual follows by adding the local Schur perturbation `ΔS = F - ΔC`
    to the recursive perturbation `ΔŜ`, and the scalar first-order bound follows
    from the local Eq. (13.11) bound plus an explicitly expanded induction
    bound.  The hypotheses still expose the norm aggregation and `Ŝ`-to-`A₂₂`
    expansion assumptions, so this is not the full computed-factor theorem. -/
theorem higham13_eq13_13_from_matmul_subtraction_induction_specs
    {r s : Type*} [Fintype r] [Fintype s]
    (u c₁ δ θ normA22 normChat normF normL21 normU12 normDeltaC normDeltaS
      normShat normLhat22 normUhat22 normL22U22 normDeltaShat normDeltaA22 : ℝ)
    (Lhat21 : Matrix s r ℝ) (Uhat12 : Matrix r s ℝ)
    (A22 Chat DeltaC F Shat DeltaShat Lhat22 Uhat22 : Matrix s s ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁)
    (hA22 : 0 ≤ normA22) (hL21 : 0 ≤ normL21) (hU12 : 0 ≤ normU12)
    (hmul : MatMulFirstOrderSpec u c₁ normL21 normU12 normDeltaC
      Lhat21 Uhat12 Chat DeltaC)
    (hsub : SubtractionFirstOrderSpec u normA22 normChat normF A22 Chat F Shat)
    (hind : PartitionedLUFirstOrderSpec u δ θ normShat normLhat22 normUhat22
      normDeltaShat Shat DeltaShat Lhat22 Uhat22)
    (hDeltaS : normDeltaS ≤ normDeltaC + normF)
    (hChat : normChat ≤ normL21 * normU12 + normDeltaC)
    (hDeltaA22 : normDeltaA22 ≤ normDeltaS + normDeltaShat)
    (hDeltaShat : FirstOrderLe u
      (u * (δ * normA22 + δ * (normL21 * normU12) + θ * normL22U22))
      normDeltaShat) :
    (Lhat21 * Uhat12 + Lhat22 * Uhat22 =
      A22 + ((F - DeltaC) + DeltaShat)) ∧
      FirstOrderLe u
        (u * ((1 + δ) * normA22 + (1 + c₁ + δ) * (normL21 * normU12) +
          θ * normL22U22))
        normDeltaA22 := by
  have hEq11 :=
    higham13_eq13_11_from_matmul_subtraction_specs
      u c₁ normA22 normChat normF normL21 normU12 normDeltaC normDeltaS
      Lhat21 Uhat12 A22 Chat DeltaC F Shat hu hc₁ hA22 hL21 hU12 hmul
      hsub hDeltaS hChat
  refine ⟨?_, ?_⟩
  · exact higham13_eq13_13_trailing_block_identity
      (Lhat21 * Uhat12) (Lhat22 * Uhat22) Shat A22 (F - DeltaC) DeltaShat
      hEq11.1 hind.equation
  · exact higham13_eq13_13_trailing_block_error_firstOrder
      normDeltaA22 normDeltaS normDeltaShat normA22 (normL21 * normU12)
      normL22U22 u c₁ δ θ hDeltaA22 hEq11.2 hDeltaShat

/-- Higham, 2nd ed., Chapter 13, Section 13.2, Theorem 13.5 proof:
    exact block-matrix residual identity.

    If the four computed block residual equations hold for `(1,1)`, `(1,2)`,
    `(2,1)`, and `(2,2)`, then the assembled computed block factors satisfy
    `L̂ Û = A + ΔA`, with `ΔA` assembled blockwise.  This is the exact algebraic
    bridge from equations (13.6), (13.8), (13.9), and (13.13) to the theorem's
    matrix residual statement. -/
theorem higham13_theorem13_5_block_residual_identity
    {m n α : Type*} [Fintype m] [Fintype n] [CommRing α]
    (L11 U11 A11 DeltaA11 : Matrix m m α)
    (U12 A12 DeltaA12 : Matrix m n α)
    (L21 A21 DeltaA21 : Matrix n m α)
    (L22 U22 A22 DeltaA22 : Matrix n n α)
    (h11 : L11 * U11 = A11 + DeltaA11)
    (h12 : L11 * U12 = A12 + DeltaA12)
    (h21 : L21 * U11 = A21 + DeltaA21)
    (h22 : L21 * U12 + L22 * U22 = A22 + DeltaA22) :
    Matrix.fromBlocks L11 0 L21 L22 * Matrix.fromBlocks U11 U12 0 U22 =
      Matrix.fromBlocks A11 A12 A21 A22 +
        Matrix.fromBlocks DeltaA11 DeltaA12 DeltaA21 DeltaA22 := by
  rw [Matrix.fromBlocks_multiply]
  simp [h11, h12, h21, h22]
  ext i j
  cases i <;> cases j <;> rfl

/-- Higham, 2nd ed., Chapter 13, Section 13.2, Theorem 13.5 proof:
    exact assembled residual identity obtained directly from the source-facing
    computed-operation specs for (13.6), (13.8), and (13.9), plus the trailing
    block residual equation (13.13). -/
theorem higham13_theorem13_5_block_residual_identity_from_specs
    {r s : Type*} [Fintype r] [Fintype s]
    (u c₂ c₃ normLhat11 normUhat11 normDeltaA11
      normUhat12 normDeltaA12 normLhat21 normDeltaA21 : ℝ)
    (Lhat11 Uhat11 A11 DeltaA11 : Matrix r r ℝ)
    (Uhat12 A12 DeltaA12 : Matrix r s ℝ)
    (Lhat21 A21 DeltaA21 : Matrix s r ℝ)
    (Lhat22 Uhat22 A22 DeltaA22 : Matrix s s ℝ)
    (h11 : LocalLUFirstOrderSpec u c₃ normLhat11 normUhat11 normDeltaA11
      A11 DeltaA11 Lhat11 Uhat11)
    (h12 : TriangularSolveFirstOrderSpec u c₂ normLhat11 normUhat12 normDeltaA12
      Lhat11 A12 DeltaA12 Uhat12)
    (h21 : RightTriangularSolveFirstOrderSpec u c₂ normUhat11 normLhat21 normDeltaA21
      Uhat11 A21 DeltaA21 Lhat21)
    (h22 : Lhat21 * Uhat12 + Lhat22 * Uhat22 = A22 + DeltaA22) :
    Matrix.fromBlocks Lhat11 0 Lhat21 Lhat22 *
        Matrix.fromBlocks Uhat11 Uhat12 0 Uhat22 =
      Matrix.fromBlocks A11 A12 A21 A22 +
        Matrix.fromBlocks DeltaA11 DeltaA12 DeltaA21 DeltaA22 := by
  exact higham13_theorem13_5_block_residual_identity
    Lhat11 Uhat11 A11 DeltaA11 Uhat12 A12 DeltaA12 Lhat21 A21 DeltaA21
    Lhat22 Uhat22 A22 DeltaA22 h11.equation h12.equation h21.equation h22

-- ============================================================
-- §13.2  Theorem 13.5 scalar one-step aggregation
-- ============================================================

/-- **Theorem 13.5 scalar one-step aggregation** (Demmel--Higham).
    Given per-block backward errors from BLAS-3 assumptions (13.4)--(13.6),
    the overall backward error satisfies the recurrence bound. -/
theorem partitioned_lu_backward_error_step
    (normΔA₁₁ normΔA₁₂ normΔA₂₁ normΔA₂₂ : ℝ)
    (normA normL normU u : ℝ)
    (c₁ c₂ c₃ δ_prev θ_prev : ℝ)
    (hu : 0 ≤ u) (_hc₁ : 0 ≤ c₁) (_hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hδ : 0 ≤ δ_prev) (_hθ : 0 ≤ θ_prev)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    -- Per-block error bounds (eqs. 13.6, 13.8, 13.9, 13.13):
    (h₁₁ : normΔA₁₁ ≤ c₃ * u * normL * normU)
    (h₁₂ : normΔA₁₂ ≤ c₂ * u * normL * normU)
    (h₂₁ : normΔA₂₁ ≤ c₂ * u * normL * normU)
    (h₂₂ : normΔA₂₂ ≤ u * ((1 + δ_prev) * normA +
        (1 + c₁ + δ_prev + θ_prev) * normL * normU)) :
    max (max normΔA₁₁ normΔA₁₂) (max normΔA₂₁ normΔA₂₂) ≤
      u * ((1 + δ_prev) * normA +
        max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) * normL * normU) := by
  have hLU : 0 ≤ normL * normU := mul_nonneg hL hU
  have hθ_max : c₃ ≤ max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) :=
    le_trans (le_max_left c₃ c₂) (le_max_left _ _)
  have hθ_max2 : c₂ ≤ max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) :=
    le_trans (le_max_right c₃ c₂) (le_max_left _ _)
  have hθ_max3 : 1 + c₁ + δ_prev + θ_prev ≤
      max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev) := le_max_right _ _
  set M := max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev)
  have hM_nonneg : 0 ≤ M := le_trans hc₃ hθ_max
  have hRHS_nonneg : 0 ≤ (1 + δ_prev) * normA := by nlinarith
  -- Helper: if x ≤ c * u * normL * normU and c ≤ M, then x ≤ RHS
  have haux : ∀ c, c ≤ M → c * u * normL * normU ≤
      u * ((1 + δ_prev) * normA + M * normL * normU) := by
    intro c hc
    have h1 : c * (u * (normL * normU)) ≤ M * (u * (normL * normU)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hu hLU)
    nlinarith
  apply max_le <;> apply max_le
  · exact le_trans h₁₁ (haux c₃ hθ_max)
  · exact le_trans h₁₂ (haux c₂ hθ_max2)
  · exact le_trans h₂₁ (haux c₂ hθ_max2)
  · calc normΔA₂₂
        ≤ u * ((1 + δ_prev) * normA + (1 + c₁ + δ_prev + θ_prev) * normL * normU) := h₂₂
      _ ≤ u * ((1 + δ_prev) * normA + M * normL * normU) := by
          apply mul_le_mul_of_nonneg_left _ hu
          linarith [mul_le_mul_of_nonneg_right hθ_max3 hLU]

/-- **Theorem 13.5 recurrence step**, scalar norm-level form.

    This is the previous aggregation lemma specialized to Higham's recurrence
    constants `δ` and `θ`: if the leading, off-diagonal, and trailing block
    errors satisfy the source first-order bounds for one partitioned-LU step,
    the combined block error satisfies the next `δ`/`θ` bound.  It is still a
    scalar proof-step theorem, not the full implementation-facing theorem with
    computed block matrices and `O(u^2)` witnesses. -/
theorem higham13_theorem13_5_recurrence_step
    (m : ℕ)
    (normΔA₁₁ normΔA₁₂ normΔA₂₁ normΔA₂₂ : ℝ)
    (normA normL normU u c₁ c₂ c₃ : ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (h₁₁ : normΔA₁₁ ≤ c₃ * u * normL * normU)
    (h₁₂ : normΔA₁₂ ≤ c₂ * u * normL * normU)
    (h₂₁ : normΔA₂₁ ≤ c₂ * u * normL * normU)
    (h₂₂ : normΔA₂₂ ≤
      u * ((1 + blockErrorDelta (m + 1)) * normA +
        (1 + c₁ + blockErrorDelta (m + 1) +
          blockErrorTheta c₁ c₂ c₃ (m + 1)) * normL * normU)) :
    max (max normΔA₁₁ normΔA₁₂) (max normΔA₂₁ normΔA₂₂) ≤
      u * (blockErrorDelta (m + 2) * normA +
        blockErrorTheta c₁ c₂ c₃ (m + 2) * normL * normU) := by
  rw [blockErrorDelta_succ_succ, blockErrorTheta_succ_succ]
  exact partitioned_lu_backward_error_step
    normΔA₁₁ normΔA₁₂ normΔA₂₁ normΔA₂₂ normA normL normU u c₁ c₂ c₃
    (blockErrorDelta (m + 1)) (blockErrorTheta c₁ c₂ c₃ (m + 1))
    hu hc₁ hc₂ hc₃ (blockErrorDelta_nonneg (m + 1))
    (blockErrorTheta_nonneg_of_c3_nonneg c₁ c₂ c₃ hc₃ (m + 1))
    hA hL hU h₁₁ h₁₂ h₂₁ h₂₂

/-- **Theorem 13.5 recurrence step with `+ O(u^2)` terms**, scalar norm-level
    form.

    This lifts `higham13_theorem13_5_recurrence_step` to the repository's
    explicit `FirstOrderLe` interpretation of Higham's displayed first-order
    bounds.  If all four block errors satisfy their first-order source bounds,
    then the combined block error satisfies the next recurrence bound with its
    own explicit second-order witness.  The theorem is still scalar recurrence
    infrastructure: it does not yet model the computed block factors in
    equations (13.8)--(13.13). -/
theorem higham13_theorem13_5_recurrence_step_firstOrder
    (m : ℕ)
    (normΔA₁₁ normΔA₁₂ normΔA₂₁ normΔA₂₂ : ℝ)
    (normA normL normU u c₁ c₂ c₃ : ℝ)
    (hu : 0 ≤ u) (_hc₁ : 0 ≤ c₁) (_hc₂ : 0 ≤ c₂) (_hc₃ : 0 ≤ c₃)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (h₁₁ : FirstOrderLe u (c₃ * u * normL * normU) normΔA₁₁)
    (h₁₂ : FirstOrderLe u (c₂ * u * normL * normU) normΔA₁₂)
    (h₂₁ : FirstOrderLe u (c₂ * u * normL * normU) normΔA₂₁)
    (h₂₂ : FirstOrderLe u
      (u * ((1 + blockErrorDelta (m + 1)) * normA +
        (1 + c₁ + blockErrorDelta (m + 1) +
          blockErrorTheta c₁ c₂ c₃ (m + 1)) * normL * normU))
      normΔA₂₂) :
    FirstOrderLe u
      (u * (blockErrorDelta (m + 2) * normA +
        blockErrorTheta c₁ c₂ c₃ (m + 2) * normL * normU))
      (max (max normΔA₁₁ normΔA₁₂) (max normΔA₂₁ normΔA₂₂)) := by
  rw [blockErrorDelta_succ_succ, blockErrorTheta_succ_succ]
  have hLU : 0 ≤ normL * normU := mul_nonneg hL hU
  set δ_prev := blockErrorDelta (m + 1)
  set θ_prev := blockErrorTheta c₁ c₂ c₃ (m + 1)
  set M := max (max c₃ c₂) (1 + c₁ + δ_prev + θ_prev)
  have hθ_max : c₃ ≤ M := by
    exact le_trans (le_max_left c₃ c₂) (le_max_left _ _)
  have hθ_max2 : c₂ ≤ M := by
    exact le_trans (le_max_right c₃ c₂) (le_max_left _ _)
  have hθ_max3 : 1 + c₁ + δ_prev + θ_prev ≤ M := le_max_right _ _
  have haux : ∀ c, c ≤ M → c * u * normL * normU ≤
      u * ((1 + δ_prev) * normA + M * normL * normU) := by
    intro c hc
    have h1 : c * (u * (normL * normU)) ≤ M * (u * (normL * normU)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hu hLU)
    have hδ : 0 ≤ δ_prev := by
      dsimp [δ_prev]
      exact blockErrorDelta_nonneg (m + 1)
    have hAterm : 0 ≤ u * ((1 + δ_prev) * normA) :=
      mul_nonneg hu (mul_nonneg (by linarith) hA)
    nlinarith
  have h₁₁' : FirstOrderLe u (u * ((1 + δ_prev) * normA + M * normL * normU))
      normΔA₁₁ :=
    h₁₁.mono_leading (by
      dsimp [δ_prev, θ_prev, M]
      exact haux c₃ hθ_max)
  have h₁₂' : FirstOrderLe u (u * ((1 + δ_prev) * normA + M * normL * normU))
      normΔA₁₂ :=
    h₁₂.mono_leading (by
      dsimp [δ_prev, θ_prev, M]
      exact haux c₂ hθ_max2)
  have h₂₁' : FirstOrderLe u (u * ((1 + δ_prev) * normA + M * normL * normU))
      normΔA₂₁ :=
    h₂₁.mono_leading (by
      dsimp [δ_prev, θ_prev, M]
      exact haux c₂ hθ_max2)
  have h₂₂' : FirstOrderLe u (u * ((1 + δ_prev) * normA + M * normL * normU))
      normΔA₂₂ := by
    apply h₂₂.mono_leading
    apply mul_le_mul_of_nonneg_left _ hu
    nlinarith [mul_le_mul_of_nonneg_right hθ_max3 hLU]
  exact FirstOrderLe.max_same
    (FirstOrderLe.max_same h₁₁' h₁₂')
    (FirstOrderLe.max_same h₂₁' h₂₂')

/-- Higham, 2nd ed., Chapter 13, Section 13.2, Theorem 13.5 proof step:
    packaged exact residual identity and first-order recurrence bound.

    This combines the source-facing residual specs for (13.6), (13.8), and
    (13.9), an already-proved trailing-block residual equation for (13.13), and
    the scalar first-order trailing-block bound into the two conclusions used by
    the theorem proof: the assembled block factors satisfy
    `L̂Û = A + ΔA`, and the blockwise max of the perturbation norms satisfies
    the next `δ`/`θ` recurrence bound with an explicit `O(u^2)` witness.

    The hypotheses deliberately require the local specs to have already been
    expressed with the common global majorants `normL` and `normU`, and require
    the trailing-block first-order premise separately.  Therefore this is an
    integration proof step, not the full computed partitioned-LU theorem. -/
theorem higham13_theorem13_5_residual_and_recurrence_from_specs
    {r s : Type*} [Fintype r] [Fintype s]
    (m : ℕ)
    (u c₁ c₂ c₃ normA normL normU
      normDeltaA11 normDeltaA12 normDeltaA21 normDeltaA22 : ℝ)
    (Lhat11 Uhat11 A11 DeltaA11 : Matrix r r ℝ)
    (Uhat12 A12 DeltaA12 : Matrix r s ℝ)
    (Lhat21 A21 DeltaA21 : Matrix s r ℝ)
    (Lhat22 Uhat22 A22 DeltaA22 : Matrix s s ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (h11 : LocalLUFirstOrderSpec u c₃ normL normU normDeltaA11
      A11 DeltaA11 Lhat11 Uhat11)
    (h12 : TriangularSolveFirstOrderSpec u c₂ normL normU normDeltaA12
      Lhat11 A12 DeltaA12 Uhat12)
    (h21 : RightTriangularSolveFirstOrderSpec u c₂ normU normL normDeltaA21
      Uhat11 A21 DeltaA21 Lhat21)
    (h22_residual : Lhat21 * Uhat12 + Lhat22 * Uhat22 = A22 + DeltaA22)
    (h22_bound : FirstOrderLe u
      (u * ((1 + blockErrorDelta (m + 1)) * normA +
        (1 + c₁ + blockErrorDelta (m + 1) +
          blockErrorTheta c₁ c₂ c₃ (m + 1)) * normL * normU))
      normDeltaA22) :
    (Matrix.fromBlocks Lhat11 0 Lhat21 Lhat22 *
        Matrix.fromBlocks Uhat11 Uhat12 0 Uhat22 =
      Matrix.fromBlocks A11 A12 A21 A22 +
        Matrix.fromBlocks DeltaA11 DeltaA12 DeltaA21 DeltaA22) ∧
      FirstOrderLe u
        (u * (blockErrorDelta (m + 2) * normA +
          blockErrorTheta c₁ c₂ c₃ (m + 2) * normL * normU))
        (max (max normDeltaA11 normDeltaA12)
          (max normDeltaA21 normDeltaA22)) := by
  refine ⟨?_, ?_⟩
  · exact higham13_theorem13_5_block_residual_identity_from_specs
      u c₂ c₃ normL normU normDeltaA11 normU normDeltaA12 normL
      normDeltaA21 Lhat11 Uhat11 A11 DeltaA11 Uhat12 A12 DeltaA12
      Lhat21 A21 DeltaA21 Lhat22 Uhat22 A22 DeltaA22 h11 h12 h21
      h22_residual
  · have h11_bound : FirstOrderLe u (c₃ * u * normL * normU) normDeltaA11 := by
      simpa [LocalLUFirstOrderBound] using h11.norm_bound
    have h12_bound : FirstOrderLe u (c₂ * u * normL * normU) normDeltaA12 := by
      simpa [TriangularSolveFirstOrderBound] using h12.norm_bound
    have h21_bound : FirstOrderLe u (c₂ * u * normL * normU) normDeltaA21 := by
      simpa [TriangularSolveFirstOrderBound, mul_assoc, mul_left_comm, mul_comm]
        using h21.norm_bound
    exact higham13_theorem13_5_recurrence_step_firstOrder
      m normDeltaA11 normDeltaA12 normDeltaA21 normDeltaA22 normA normL normU
      u c₁ c₂ c₃ hu hc₁ hc₂ hc₃ hA hL hU h11_bound h12_bound h21_bound
      h22_bound

/-- Higham, 2nd ed., Chapter 13, Section 13.2, Theorem 13.5 induction step:
    spec-shaped version of the residual/recurrence package.

    Under the same source proof-step hypotheses as
    `higham13_theorem13_5_residual_and_recurrence_from_specs`, the assembled
    2-by-2 block factorization satisfies the repository's recursive
    `PartitionedLUFirstOrderSpec` at the next `δ`/`θ` constants.  This is the
    direct Lean analogue of the induction-step conclusion in the proof; it still
    leaves the construction of the full computed factor sequence and global norm
    instantiation to the final theorem. -/
theorem higham13_theorem13_5_partitioned_step_spec_from_specs
    {r s : Type*} [Fintype r] [Fintype s]
    (m : ℕ)
    (u c₁ c₂ c₃ normA normL normU
      normDeltaA11 normDeltaA12 normDeltaA21 normDeltaA22 : ℝ)
    (Lhat11 Uhat11 A11 DeltaA11 : Matrix r r ℝ)
    (Uhat12 A12 DeltaA12 : Matrix r s ℝ)
    (Lhat21 A21 DeltaA21 : Matrix s r ℝ)
    (Lhat22 Uhat22 A22 DeltaA22 : Matrix s s ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (h11 : LocalLUFirstOrderSpec u c₃ normL normU normDeltaA11
      A11 DeltaA11 Lhat11 Uhat11)
    (h12 : TriangularSolveFirstOrderSpec u c₂ normL normU normDeltaA12
      Lhat11 A12 DeltaA12 Uhat12)
    (h21 : RightTriangularSolveFirstOrderSpec u c₂ normU normL normDeltaA21
      Uhat11 A21 DeltaA21 Lhat21)
    (h22_residual : Lhat21 * Uhat12 + Lhat22 * Uhat22 = A22 + DeltaA22)
    (h22_bound : FirstOrderLe u
      (u * ((1 + blockErrorDelta (m + 1)) * normA +
        (1 + c₁ + blockErrorDelta (m + 1) +
          blockErrorTheta c₁ c₂ c₃ (m + 1)) * normL * normU))
      normDeltaA22) :
    PartitionedLUFirstOrderSpec u (blockErrorDelta (m + 2))
      (blockErrorTheta c₁ c₂ c₃ (m + 2)) normA normL normU
      (max (max normDeltaA11 normDeltaA12) (max normDeltaA21 normDeltaA22))
      (Matrix.fromBlocks A11 A12 A21 A22)
      (Matrix.fromBlocks DeltaA11 DeltaA12 DeltaA21 DeltaA22)
      (Matrix.fromBlocks Lhat11 0 Lhat21 Lhat22)
      (Matrix.fromBlocks Uhat11 Uhat12 0 Uhat22) := by
  rcases higham13_theorem13_5_residual_and_recurrence_from_specs
      m u c₁ c₂ c₃ normA normL normU normDeltaA11 normDeltaA12 normDeltaA21
      normDeltaA22 Lhat11 Uhat11 A11 DeltaA11 Uhat12 A12 DeltaA12
      Lhat21 A21 DeltaA21 Lhat22 Uhat22 A22 DeltaA22 hu hc₁ hc₂ hc₃
      hA hL hU h11 h12 h21 h22_residual h22_bound with
    ⟨hResidual, hBound⟩
  exact ⟨hResidual, hBound⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 factorization route:
    two-budget recursive first-order step.

    This is the named DHS-facing composition requested by the recovered Pro
    audit.  It uses the rounded Schur-update layer
    `dhs_schur_update_firstOrder`, the recursive trailing-factor induction
    equation, and the existing Higham 13.5 partitioned-LU recurrence to produce
    the next partitioned first-order factorization spec.  It still assumes the
    local residual specs and scalar norm majorants explicitly; it does not hide
    the remaining implementation kernels inside the theorem statement. -/
theorem dhs_block_lu_factorization_twoBudget_firstOrder
    {r s : Type*} [Fintype r] [Fintype s]
    (m : ℕ)
    (u c₁ c₂ c₃ normA normL normU
      normChat normF normDeltaA11 normDeltaA12 normDeltaA21 normDeltaC
      normDeltaS normDeltaShat normDeltaA22 normShat normLhat22
      normUhat22 : ℝ)
    (Lhat11 Uhat11 A11 DeltaA11 : Matrix r r ℝ)
    (Uhat12 A12 DeltaA12 : Matrix r s ℝ)
    (Lhat21 A21 DeltaA21 : Matrix s r ℝ)
    (Lhat22 Uhat22 A22 Chat DeltaC F Shat DeltaShat : Matrix s s ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (h11 : LocalLUFirstOrderSpec u c₃ normL normU normDeltaA11
      A11 DeltaA11 Lhat11 Uhat11)
    (h12 : TriangularSolveFirstOrderSpec u c₂ normL normU normDeltaA12
      Lhat11 A12 DeltaA12 Uhat12)
    (h21 : RightTriangularSolveFirstOrderSpec u c₂ normU normL normDeltaA21
      Uhat11 A21 DeltaA21 Lhat21)
    (hmul : MatMulFirstOrderSpec u c₁ normL normU normDeltaC
      Lhat21 Uhat12 Chat DeltaC)
    (hsub : SubtractionFirstOrderSpec u normA normChat normF A22 Chat F Shat)
    (hind : PartitionedLUFirstOrderSpec u (blockErrorDelta (m + 1))
      (blockErrorTheta c₁ c₂ c₃ (m + 1)) normShat normLhat22 normUhat22
      normDeltaShat Shat DeltaShat Lhat22 Uhat22)
    (hDeltaS : normDeltaS ≤ normDeltaC + normF)
    (hChat : normChat ≤ normL * normU + normDeltaC)
    (hDeltaA22 : normDeltaA22 ≤ normDeltaS + normDeltaShat)
    (hDeltaShat : FirstOrderLe u
      (u * (blockErrorDelta (m + 1) * normA +
        blockErrorDelta (m + 1) * (normL * normU) +
        blockErrorTheta c₁ c₂ c₃ (m + 1) * (normL * normU)))
      normDeltaShat) :
    PartitionedLUFirstOrderSpec u (blockErrorDelta (m + 2))
      (blockErrorTheta c₁ c₂ c₃ (m + 2)) normA normL normU
      (max (max normDeltaA11 normDeltaA12)
        (max normDeltaA21 normDeltaA22))
      (Matrix.fromBlocks A11 A12 A21 A22)
      (Matrix.fromBlocks DeltaA11 DeltaA12 DeltaA21 ((F - DeltaC) + DeltaShat))
      (Matrix.fromBlocks Lhat11 0 Lhat21 Lhat22)
      (Matrix.fromBlocks Uhat11 Uhat12 0 Uhat22) := by
  have hSchur :=
    dhs_schur_update_firstOrder
      u c₁ normA normChat normF normL normU normDeltaC normDeltaS
      Lhat21 Uhat12 A22 Chat DeltaC F Shat hu hc₁ hA hL hU hmul hsub
      hDeltaS hChat
  have hTrailingResidual :
      Lhat21 * Uhat12 + Lhat22 * Uhat22 = A22 + ((F - DeltaC) + DeltaShat) :=
    higham13_eq13_13_trailing_block_identity
      (Lhat21 * Uhat12) (Lhat22 * Uhat22) Shat A22 (F - DeltaC) DeltaShat
      hSchur.1 hind.equation
  have hTrailingBoundLocal :
      FirstOrderLe u
        (u * ((1 + blockErrorDelta (m + 1)) * normA +
          (1 + c₁ + blockErrorDelta (m + 1)) * (normL * normU) +
          blockErrorTheta c₁ c₂ c₃ (m + 1) * (normL * normU)))
        normDeltaA22 :=
    higham13_eq13_13_trailing_block_error_firstOrder
      normDeltaA22 normDeltaS normDeltaShat normA (normL * normU)
      (normL * normU) u c₁ (blockErrorDelta (m + 1))
      (blockErrorTheta c₁ c₂ c₃ (m + 1))
      hDeltaA22 hSchur.2 hDeltaShat
  have hTrailingBound : FirstOrderLe u
      (u * ((1 + blockErrorDelta (m + 1)) * normA +
        (1 + c₁ + blockErrorDelta (m + 1) +
          blockErrorTheta c₁ c₂ c₃ (m + 1)) * normL * normU))
      normDeltaA22 :=
    hTrailingBoundLocal.mono_leading (by
      ring_nf
      exact le_rfl)
  exact
    higham13_theorem13_5_partitioned_step_spec_from_specs
      m u c₁ c₂ c₃ normA normL normU normDeltaA11 normDeltaA12
      normDeltaA21 normDeltaA22 Lhat11 Uhat11 A11 DeltaA11
      Uhat12 A12 DeltaA12 Lhat21 A21 DeltaA21 Lhat22 Uhat22
      A22 ((F - DeltaC) + DeltaShat) hu hc₁ hc₂ hc₃ hA hL hU
      h11 h12 h21 hTrailingResidual hTrailingBound

/-!
### Complete computed-factor induction for Theorem 13.5

The one-step theorem above is the algebraic induction step.  The following
certificate records an actual recursive execution of Algorithm 13.1: the base
case is the block-level factorization model (13.6), while a successor stores
the two triangular solves, the rounded matrix product and subtraction, and a
certificate for the computed trailing factorization.  The scalar norm fields
are source-style norm majorants.  In particular, `c₁`, `c₂`, and `c₃` may be
chosen as common upper envelopes for the dimension-dependent constants in
(13.4)--(13.6) over the recursive stages.
-/

/-- A recursive computed execution of the partitioned outer-product LU
    factorization used in Higham's Theorem 13.5.

    The result indices are the actual input matrix, assembled perturbation,
    and computed factors.  The successor constructor mirrors equations
    (13.8)--(13.13).  Its last three inequalities are ordinary norm laws:
    the computed product is bounded by product plus residual, the rounded
    Schur complement is bounded by its summands, and the two trailing factor
    norms are bounded by the full-factor norm majorants. -/
inductive PartitionedLUComputationFirstOrder
    (u c₁ c₂ c₃ : ℝ) :
    {ι : Type} → [Fintype ι] → ℕ →
      ℝ → ℝ → ℝ → ℝ →
      Matrix ι ι ℝ → Matrix ι ι ℝ → Matrix ι ι ℝ → Matrix ι ι ℝ → Prop
  | base {ι : Type} [Fintype ι]
      (normA normL normU normDeltaA : ℝ)
      (A DeltaA Lhat Uhat : Matrix ι ι ℝ)
      (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
      (hlocal : LocalLUFirstOrderSpec u c₃ normL normU normDeltaA
        A DeltaA Lhat Uhat) :
      PartitionedLUComputationFirstOrder u c₁ c₂ c₃ 1
        normA normL normU normDeltaA A DeltaA Lhat Uhat
  | step {r s : Type} [Fintype r] [Fintype s]
      (m : ℕ)
      (normA normL normU normChat normF normDeltaA11 normDeltaA12
        normDeltaA21 normDeltaC normDeltaS normDeltaShat normDeltaA22
        normShat normLhat22 normUhat22 : ℝ)
      (Lhat11 Uhat11 A11 DeltaA11 : Matrix r r ℝ)
      (Uhat12 A12 DeltaA12 : Matrix r s ℝ)
      (Lhat21 A21 DeltaA21 : Matrix s r ℝ)
      (Lhat22 Uhat22 A22 Chat DeltaC F Shat DeltaShat : Matrix s s ℝ)
      (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
      (hChat_nonneg : 0 ≤ normChat)
      (hShat : 0 ≤ normShat) (hLhat22 : 0 ≤ normLhat22)
      (hUhat22 : 0 ≤ normUhat22)
      (h11 : LocalLUFirstOrderSpec u c₃ normL normU normDeltaA11
        A11 DeltaA11 Lhat11 Uhat11)
      (h12 : TriangularSolveFirstOrderSpec u c₂ normL normU normDeltaA12
        Lhat11 A12 DeltaA12 Uhat12)
      (h21 : RightTriangularSolveFirstOrderSpec u c₂ normU normL normDeltaA21
        Uhat11 A21 DeltaA21 Lhat21)
      (hmul : MatMulFirstOrderSpec u c₁ normL normU normDeltaC
        Lhat21 Uhat12 Chat DeltaC)
      (hsub : SubtractionFirstOrderSpec u normA normChat normF
        A22 Chat F Shat)
      (htail : PartitionedLUComputationFirstOrder u c₁ c₂ c₃ (m + 1)
        normShat normLhat22 normUhat22 normDeltaShat
        Shat DeltaShat Lhat22 Uhat22)
      (hDeltaS : normDeltaS ≤ normDeltaC + normF)
      (hChat : normChat ≤ normL * normU + normDeltaC)
      (hShatTriangle : normShat ≤ normA + normChat + normF)
      (hDeltaA22 : normDeltaA22 ≤ normDeltaS + normDeltaShat)
      (hLhat22_le : normLhat22 ≤ normL)
      (hUhat22_le : normUhat22 ≤ normU) :
      PartitionedLUComputationFirstOrder u c₁ c₂ c₃ (m + 2)
        normA normL normU
        (max (max normDeltaA11 normDeltaA12) (max normDeltaA21 normDeltaA22))
        (Matrix.fromBlocks A11 A12 A21 A22)
        (Matrix.fromBlocks DeltaA11 DeltaA12 DeltaA21 ((F - DeltaC) + DeltaShat))
        (Matrix.fromBlocks Lhat11 0 Lhat21 Lhat22)
        (Matrix.fromBlocks Uhat11 Uhat12 0 Uhat22)

/-- In the rounded Schur update, the excess over the zeroth-order source
    majorant `‖A‖ + ‖L̂‖‖Û‖` is a nonnegative multiple of `u`.

    This is the norm estimate that Higham invokes after (13.10).  Keeping its
    coefficient existential makes the later multiplication by `u δ` visibly
    second order rather than silently discarding it. -/
theorem higham13_theorem13_5_schur_norm_linear_majorant
    (u c₁ normA normL normU normChat normF normDeltaC normShat : ℝ)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hChat_nonneg : 0 ≤ normChat)
    (hDeltaC : FirstOrderLe u (c₁ * u * normL * normU) normDeltaC)
    (hF : normF ≤ u * (normA + normChat))
    (hChat : normChat ≤ normL * normU + normDeltaC)
    (hShat : normShat ≤ normA + normChat + normF) :
    ∃ C : ℝ, 0 ≤ C ∧
      normShat ≤ normA + normL * normU + C * u := by
  rcases hDeltaC with ⟨K, hK, hDeltaC⟩
  let C := c₁ * normL * normU + K * u + normA + normChat
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  calc
    normShat ≤ normA + normChat + normF := hShat
    _ ≤ normA + (normL * normU + normDeltaC) +
        u * (normA + normChat) := by linarith
    _ ≤ normA + (normL * normU +
        (c₁ * u * normL * normU + K * u ^ 2)) +
        u * (normA + normChat) := by linarith
    _ = normA + normL * normU + C * u := by
      dsimp [C]
      ring

/-- The recursive (13.12b) perturbation bound expressed with the full-matrix
    norm majorants.  The `C*u` excess in the Schur norm becomes part of the
    explicit `O(u^2)` witness after multiplication by `u*δ`. -/
theorem higham13_theorem13_5_recursive_error_global_majorant
    (u δ θ normA normL normU normShat normLhat22 normUhat22
      normDeltaShat : ℝ)
    (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hL : 0 ≤ normL) (hUhat22 : 0 ≤ normUhat22)
    (hind : FirstOrderLe u
      (u * (δ * normShat + θ * normLhat22 * normUhat22))
      normDeltaShat)
    (hSchur : ∃ C : ℝ, 0 ≤ C ∧
      normShat ≤ normA + normL * normU + C * u)
    (hLhat22_le : normLhat22 ≤ normL)
    (hUhat22_le : normUhat22 ≤ normU) :
    FirstOrderLe u
      (u * (δ * normA + δ * (normL * normU) +
        θ * (normL * normU))) normDeltaShat := by
  rcases hind with ⟨K, hK, hind⟩
  rcases hSchur with ⟨C, hC, hSchur⟩
  have hTailProduct : normLhat22 * normUhat22 ≤ normL * normU :=
    mul_le_mul hLhat22_le hUhat22_le hUhat22 hL
  have hThetaTail : θ * normLhat22 * normUhat22 ≤ θ * (normL * normU) := by
    calc
      θ * normLhat22 * normUhat22 = θ * (normLhat22 * normUhat22) := by ring
      _ ≤ θ * (normL * normU) := mul_le_mul_of_nonneg_left hTailProduct hθ
  refine ⟨K + δ * C, add_nonneg hK (mul_nonneg hδ hC), ?_⟩
  calc
    normDeltaShat ≤
        u * (δ * normShat + θ * normLhat22 * normUhat22) + K * u ^ 2 := hind
    _ ≤ u * (δ * (normA + normL * normU + C * u) +
        θ * (normL * normU)) + K * u ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hSchur hδ)
            hThetaTail) hu)
        le_rfl
    _ = u * (δ * normA + δ * (normL * normU) +
        θ * (normL * normU)) + (K + δ * C) * u ^ 2 := by ring

/-- Complete matrix/computed-factor induction for Higham's Theorem 13.5.

    Unlike the preceding one-step lemmas, this theorem consumes a recursive
    computation certificate and proves the final specification for the actual
    assembled `A`, `ΔA`, `L̂`, and `Û`. -/
theorem PartitionedLUComputationFirstOrder.to_spec
    {ι : Type} [Fintype ι] {m : ℕ}
    {u c₁ c₂ c₃ normA normL normU normDeltaA : ℝ}
    {A DeltaA Lhat Uhat : Matrix ι ι ℝ}
    (hcomp : PartitionedLUComputationFirstOrder u c₁ c₂ c₃ m
      normA normL normU normDeltaA A DeltaA Lhat Uhat)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) :
    PartitionedLUFirstOrderSpec u (blockErrorDelta m)
      (blockErrorTheta c₁ c₂ c₃ m) normA normL normU normDeltaA
      A DeltaA Lhat Uhat := by
  induction hcomp with
  | base normA normL normU normDeltaA A DeltaA Lhat Uhat hA hL hU hlocal =>
      refine ⟨hlocal.equation, ?_⟩
      simp only [blockErrorDelta, blockErrorTheta]
      have hb : FirstOrderLe u (c₃ * u * normL * normU) normDeltaA := by
        simpa [LocalLUFirstOrderBound] using hlocal.norm_bound
      convert hb using 1
      ring
  | step m normA normL normU normChat normF normDeltaA11 normDeltaA12
      normDeltaA21 normDeltaC normDeltaS normDeltaShat normDeltaA22
      normShat normLhat22 normUhat22 Lhat11 Uhat11 A11 DeltaA11
      Uhat12 A12 DeltaA12 Lhat21 A21 DeltaA21 Lhat22 Uhat22 A22
      Chat DeltaC F Shat DeltaShat hA hL hU hChat_nonneg hShat
      hLhat22 hUhat22 h11 h12 h21 hmul hsub htail hDeltaS hChat
      hShatTriangle hDeltaA22 hLhat22_le hUhat22_le ih =>
      have hSchurMajorant : ∃ C : ℝ, 0 ≤ C ∧
          normShat ≤ normA + normL * normU + C * u :=
        higham13_theorem13_5_schur_norm_linear_majorant
          u c₁ normA normL normU normChat normF normDeltaC normShat
          hu hc₁ hA hL hU hChat_nonneg hmul.norm_bound hsub.norm_bound
          hChat hShatTriangle
      have hDeltaShatGlobal : FirstOrderLe u
          (u * (blockErrorDelta (m + 1) * normA +
            blockErrorDelta (m + 1) * (normL * normU) +
            blockErrorTheta c₁ c₂ c₃ (m + 1) * (normL * normU)))
          normDeltaShat :=
        higham13_theorem13_5_recursive_error_global_majorant
          u (blockErrorDelta (m + 1))
          (blockErrorTheta c₁ c₂ c₃ (m + 1))
          normA normL normU normShat normLhat22 normUhat22 normDeltaShat
          hu (blockErrorDelta_nonneg (m + 1))
          (blockErrorTheta_nonneg_of_c3_nonneg c₁ c₂ c₃ hc₃ (m + 1))
          hL hUhat22 ih.norm_bound hSchurMajorant hLhat22_le hUhat22_le
      exact dhs_block_lu_factorization_twoBudget_firstOrder
        m u c₁ c₂ c₃ normA normL normU normChat normF normDeltaA11
        normDeltaA12 normDeltaA21 normDeltaC normDeltaS normDeltaShat
        normDeltaA22 normShat normLhat22 normUhat22 Lhat11 Uhat11 A11
        DeltaA11 Uhat12 A12 DeltaA12 Lhat21 A21 DeltaA21 Lhat22 Uhat22
        A22 Chat DeltaC F Shat DeltaShat hu hc₁ hc₂ hc₃ hA hL hU h11
        h12 h21 hmul hsub ih hDeltaS hChat hDeltaA22 hDeltaShatGlobal

/-- **Theorem 13.5 / equation (13.7)** for an actual recursively computed
    partitioned LU execution.  The conclusion exposes both the assembled
    matrix residual and the advertised first-order backward-error bound. -/
theorem higham13_theorem13_5_eq13_7_from_computation
    {ι : Type} [Fintype ι] {m : ℕ}
    {u c₁ c₂ c₃ normA normL normU normDeltaA : ℝ}
    {A DeltaA Lhat Uhat : Matrix ι ι ℝ}
    (hcomp : PartitionedLUComputationFirstOrder u c₁ c₂ c₃ m
      normA normL normU normDeltaA A DeltaA Lhat Uhat)
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) :
    (Lhat * Uhat = A + DeltaA) ∧
      FirstOrderLe u
        (u * (blockErrorDelta m * normA +
          blockErrorTheta c₁ c₂ c₃ m * normL * normU)) normDeltaA := by
  have hspec := hcomp.to_spec hu hc₁ hc₂ hc₃
  exact ⟨hspec.equation, hspec.norm_bound⟩

end NumStability
