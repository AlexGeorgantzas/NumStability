import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations

#check NumStability.RectLSNormalEquations.isLeastSquaresMinimizer

open NumStability

example {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {b : Fin m → ℝ} {x : Fin n → ℝ}
    (h : RectLSNormalEquations A b x) :
    IsLeastSquaresMinimizer A b x := by
  exact h.isLeastSquaresMinimizer
