import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace NumStability

open scoped BigOperators

/-!
# Combined triangular solve

Reusable backward-error theorem for a forward substitution followed by a back
substitution. The result is source-independent even though Higham's Corollary
8.6 is one application.
-/

/-- **Combined triangular solve backward error** (Higham §8.1, Corollary 8.6).

    Given A = LU where L is lower triangular and U is upper triangular,
    solve Ax = b by: (1) forward substitution Ly = b, (2) back substitution Ux = y.

    The computed solution x̂ satisfies (L + ΔL)(U + ΔU)x̂ = b with
    componentwise bounds |ΔL| ≤ γ(n)|L| and |ΔU| ≤ γ(n)|U|.

    Proof: `forwardSub_backward_error` gives ΔL with (L+ΔL)ŷ = b.
    `backSub_backward_error` gives ΔU with (U+ΔU)x̂ = ŷ.
    Substituting the second into the first yields the result. -/
theorem triangularSolve_backward_error (fp : FPModel) (n : ℕ)
    (L U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hU : ∀ i, U i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    let y_hat := fl_forwardSub fp n L b
    let x_hat := fl_backSub fp n U y_hat
    ∃ (ΔL ΔU : Fin n → Fin n → ℝ),
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      (∀ i j, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) *
        (∑ j : Fin n, (U k j + ΔU k j) * x_hat j) = b i := by
  intro y_hat x_hat
  -- Forward substitution: (L + ΔL)ŷ = b
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    forwardSub_backward_error fp n L b hL hLT hn
  -- Back substitution: (U + ΔU)x̂ = ŷ
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ :=
    backSub_backward_error fp n U y_hat hU hUT hn
  refine ⟨ΔL, ΔU, hΔL_bound, hΔU_bound, ?_⟩
  intro i
  -- (L+ΔL)ŷ = b gives: ∑_k (L+ΔL)_{ik} * ŷ_k = b_i
  -- (U+ΔU)x̂ = ŷ gives: ŷ_k = ∑_j (U+ΔU)_{kj} * x̂_j
  -- Substitute: ∑_k (L+ΔL)_{ik} * (∑_j (U+ΔU)_{kj} * x̂_j) = b_i
  rw [← hΔL_eq i]
  apply Finset.sum_congr rfl
  intro k _
  rw [hΔU_eq k]

end NumStability
