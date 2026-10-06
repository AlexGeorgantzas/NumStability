import NumStability.Algorithms.DotProduct

#check NumStability.dotProduct_error_bound

open NumStability

example (fp : FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hn : gammaValid fp n) :
    |fl_dotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp n * ∑ i : Fin n, |x i| * |y i| := by
  exact dotProduct_error_bound fp n x y hn
