import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

#check NumStability.one_step_refinement_error_identity

open NumStability

example (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x x0 d_hat r_hat : Fin n → ℝ)
    (DeltaA_solve : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x0 j)
    (hsolve : ∀ i, ∑ j : Fin n,
      (A i j + DeltaA_solve i j) * d_hat j = r_hat i)
    (x1 : Fin n → ℝ) (hx1 : ∀ i, x1 i = x0 i + d_hat i) :
    ∀ i : Fin n,
      ∑ j : Fin n, A i j * (x j - x1 j) =
        ∑ j : Fin n, DeltaA_solve i j * d_hat j + (r i - r_hat i) := by
  exact one_step_refinement_error_identity n A x x0 d_hat r_hat
    DeltaA_solve b hAx r hr hsolve x1 hx1
