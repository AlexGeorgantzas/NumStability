import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

#check NumStability.forwardSub_backward_error

open NumStability

example (fp : FPModel) (n : ℕ) (L : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * fl_forwardSub fp n L b j = b i := by
  exact forwardSub_backward_error fp n L b hL hLT hn
