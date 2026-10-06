import NumStability.Analysis.Summation.ErrorBounds

#check NumStability.fl_sum_error

open NumStability


example (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp n) ∧
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0 =
        ∑ i : Fin n, v i * (1 + θ i) := by
  exact fl_sum_error fp n v hn
