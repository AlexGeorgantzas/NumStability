import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# CholeskyDemmel (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Cholesky.CholeskyDemmel`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

/-- **Cholesky success under a scaled spectral gap** (Higham §10.1, Theorem 10.7).

    Let `A + ΔA = D (H + E) D` be the scaled, perturbed matrix, where `D`
    is the positive diagonal scaling, `H` is the scaled matrix with
    Rayleigh lower bound `lam`, and `E = D⁻¹ ΔA D⁻¹` is the scaled backward
    error with quadratic form bounded by `t‖x‖²`. If the spectral gap
    `t < lam` holds, then the perturbed scaled matrix is SPD and therefore
    has a genuine Cholesky factorization: the algorithm succeeds.

    This closes the "min-eigenvalue → PD" step of Theorem 10.7 as an honest
    theorem (previously only the sign consequence `0 < lam_min` was proved).
    The remaining upstream obligation is the derivation of the concrete
    threshold `t = n γ_{n+1}/(1-γ_{n+1})` from the componentwise backward
    error, which is supplied here as the hypothesis `hE`. -/
theorem cholesky_succeeds_of_scaled_perturbation (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : ∀ i j, H i j = H j i)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam : ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        lam * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R := by
  have hHE_spd : IsSymPosDef n (fun i j => H i j + E i j) := by
    refine ⟨fun i j => ?_, ?_⟩
    · show H i j + E i j = H j i + E j i
      rw [hH_sym i j, hE_sym i j]
    exact quadForm_add_pos_of_perturbation n H E lam t hlam hE hlt
  have hDHED_spd : IsSymPosDef n (fun i j => D i * (H i j + E i j) * D j) :=
    isSymPosDef_diagCongr n D (fun i j => H i j + E i j) hD_pos hHE_spd
  exact cholesky_existence n _ hDHED_spd

end NumStability
