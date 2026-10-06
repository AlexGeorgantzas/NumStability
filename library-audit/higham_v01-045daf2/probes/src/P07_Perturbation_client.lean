import NumStability.Analysis.PerturbationTheory

#check NumStability.forward_error_from_residual

open NumStability

example (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (x y b : Fin n → ℝ) (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    ∀ i, |x i - y i| ≤
      ∑ j : Fin n, |A_inv i j| * |residualVec n A y b j| := by
  exact forward_error_from_residual n A A_inv x y b hInv hAx
