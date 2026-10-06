import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion

#check NumStability.inversion_residual_bound

open NumStability

example (n : ℕ) (fp : FPModel)
    (A A_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hInv : IsRightInverse n A A_inv) (hn : gammaValid fp n) :
    let x_hat := fl_matVec fp n n A_inv b
    ∀ i, |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n *
        ∑ j : Fin n, |A i j| *
          (∑ k : Fin n, |A_inv j k| * |b k|) := by
  exact inversion_residual_bound n fp A A_inv b hInv hn
