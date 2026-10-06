import NumStability.Algorithms.LU.GaussianElimination

#check NumStability.lu_backward_error_gamma

open NumStability

example (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n)) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j =
        A i j + ΔA i j) := by
  exact lu_backward_error_gamma fp n A L_hat U_hat hn hLU
