import Mathlib

namespace HighamBench

/-- The square of the Frobenius norm, written entrywise as in Theorem 3.2. -/
noncomputable def p40FrobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The positive spectral part obtained by replacing every negative eigenvalue by zero. -/
noncomputable def p40SpectralPositivePart {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (lambda : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Q * Matrix.diagonal (fun i => max (lambda i) 0) * Q.transpose

/-- The square of the weighted Frobenius norm from equation (1.2), with `S = W^(1/2)`. -/
noncomputable def p40WeightedFrobeniusSq {n : ℕ}
    (S A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  p40FrobeniusSq (S * A * S)

/-- Formula (3.3), expressed using `Sinv = W^(-1/2)`. -/
noncomputable def p40WeightedPsdProjection {n : ℕ}
    (Sinv Q : Matrix (Fin n) (Fin n) ℝ) (lambda : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Sinv * p40SpectralPositivePart Q lambda * Sinv

end HighamBench
