import NumStability.Analysis.Rounding

#check NumStability.gamma_nonneg

open NumStability

example (fp : FPModel) {n : ℕ} (hn : gammaValid fp n) :
    0 ≤ gamma fp n := by
  exact gamma_nonneg fp hn
