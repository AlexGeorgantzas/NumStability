-- Algorithms/ComplexBackwardError.lean
--
-- Higham Chapter 3, Problem 3.7.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace NumStability

open scoped BigOperators

/-!
# Complex Backward-Error Analogues

Higham Chapter 3, Problem 3.7 asks for complex analogues of the real
backward-error results (3.4) and (3.11).  Section 3.6 explains the transfer
principle: complex basic-operation errors have the same relative-error form as
the real model, with constants adjusted appropriately.  This file formalizes
the algebraic backward-error consequences of such a complex relative-error
expansion.
-/

/-- Complex dot product using the same bilinear convention as the real
Chapter 3 dot-product statements. -/
noncomputable def complexDotProduct (n : ℕ)
    (x y : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, x i * y i

/-- Source-shaped complex componentwise relative-error expansion for a dot
product:

`computed = sum_i x_i y_i (1 + eta_i)`, with `||eta_i|| <= gamma`. -/
def complexDotProductRelErrorExpansion (n : ℕ)
    (computed : ℂ) (x y : Fin n → ℂ) (gamma : ℝ) : Prop :=
  ∃ eta : Fin n → ℂ,
    (∀ i, ‖eta i‖ ≤ gamma) ∧
      computed = ∑ i : Fin n, x i * y i * (1 + eta i)

/-- **Problem 3.7, complex analogue of (3.4), y-perturbation form.**

A complex dot-product relative-error expansion is the exact dot product of
`x` with a componentwise perturbed `y`, with perturbations bounded in complex
modulus. -/
theorem complexDotProduct_backward_stable_y
    {n : ℕ} {computed : ℂ} {x y : Fin n → ℂ} {gamma : ℝ}
    (_hgamma_nonneg : 0 ≤ gamma)
    (h : complexDotProductRelErrorExpansion n computed x y gamma) :
    ∃ Δy : Fin n → ℂ,
      (∀ i, ‖Δy i‖ ≤ gamma * ‖y i‖) ∧
        computed = ∑ i : Fin n, x i * (y i + Δy i) := by
  rcases h with ⟨eta, heta, hcomputed⟩
  refine ⟨fun i => y i * eta i, ?_, ?_⟩
  · intro i
    calc
      ‖y i * eta i‖ = ‖y i‖ * ‖eta i‖ := norm_mul _ _
      _ ≤ ‖y i‖ * gamma :=
          mul_le_mul_of_nonneg_left (heta i) (norm_nonneg _)
      _ = gamma * ‖y i‖ := by ring
  · rw [hcomputed]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- **Problem 3.7, complex analogue of (3.4), x-perturbation form.**

Equivalently, the perturbation can be assigned to the first vector. -/
theorem complexDotProduct_backward_stable_x
    {n : ℕ} {computed : ℂ} {x y : Fin n → ℂ} {gamma : ℝ}
    (_hgamma_nonneg : 0 ≤ gamma)
    (h : complexDotProductRelErrorExpansion n computed x y gamma) :
    ∃ Δx : Fin n → ℂ,
      (∀ i, ‖Δx i‖ ≤ gamma * ‖x i‖) ∧
        computed = ∑ i : Fin n, (x i + Δx i) * y i := by
  rcases h with ⟨eta, heta, hcomputed⟩
  refine ⟨fun i => x i * eta i, ?_, ?_⟩
  · intro i
    calc
      ‖x i * eta i‖ = ‖x i‖ * ‖eta i‖ := norm_mul _ _
      _ ≤ ‖x i‖ * gamma :=
          mul_le_mul_of_nonneg_left (heta i) (norm_nonneg _)
      _ = gamma * ‖x i‖ := by ring
  · rw [hcomputed]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Complex matrix-vector product. -/
noncomputable def complexMatVec (m n : ℕ)
    (A : Fin m → Fin n → ℂ) (x : Fin n → ℂ) : Fin m → ℂ :=
  fun i => ∑ j : Fin n, A i j * x j

/-- Row-wise complex dot-product relative-error expansions for a computed
matrix-vector product. -/
def complexMatVecRelErrorRows (m n : ℕ)
    (computed : Fin m → ℂ) (A : Fin m → Fin n → ℂ)
    (x : Fin n → ℂ) (gamma : ℝ) : Prop :=
  ∀ i : Fin m,
    complexDotProductRelErrorExpansion n (computed i) (A i) x gamma

/-- **Problem 3.7, complex analogue of (3.11).**

If every computed row dot product has a complex componentwise relative-error
expansion with radius `gamma`, then the computed matrix-vector product is an
exact product `(A + DeltaA)x`, with componentwise complex-modulus backward
error `||DeltaA_ij|| <= gamma ||A_ij||`. -/
theorem complexMatVec_backward_error
    {m n : ℕ} {computed : Fin m → ℂ}
    {A : Fin m → Fin n → ℂ} {x : Fin n → ℂ} {gamma : ℝ}
    (hgamma_nonneg : 0 ≤ gamma)
    (hrows : complexMatVecRelErrorRows m n computed A x gamma) :
    ∃ ΔA : Fin m → Fin n → ℂ,
      (∀ i j, ‖ΔA i j‖ ≤ gamma * ‖A i j‖) ∧
        ∀ i, computed i = ∑ j : Fin n, (A i j + ΔA i j) * x j := by
  let ΔA : Fin m → Fin n → ℂ :=
    fun i => Classical.choose
      (complexDotProduct_backward_stable_x hgamma_nonneg (hrows i))
  have hΔA :
      ∀ i,
        (∀ j, ‖ΔA i j‖ ≤ gamma * ‖A i j‖) ∧
          computed i = ∑ j : Fin n, (A i j + ΔA i j) * x j := by
    intro i
    exact Classical.choose_spec
      (complexDotProduct_backward_stable_x hgamma_nonneg (hrows i))
  exact ⟨ΔA, fun i j => (hΔA i).1 j, fun i => (hΔA i).2⟩

end NumStability
