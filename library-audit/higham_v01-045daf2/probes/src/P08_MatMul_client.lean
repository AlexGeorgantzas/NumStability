import NumStability.Algorithms.MatMul

#check NumStability.matMul_error_bound

open NumStability

example (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    ∀ i : Fin m, ∀ j : Fin p,
      |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j| ≤
        gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
  exact matMul_error_bound fp m n p A B hn
