import Mathlib

namespace HighamBenchCandidate

/-- The Euclidean norm of a real vector. -/
noncomputable def euclideanNorm {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin k, (v i) ^ 2)

/-- The Frobenius norm of a real matrix. -/
noncomputable def frobeniusNorm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (M i j) ^ 2)

/-- With the right-hand side fixed, zero minimizes the perturbed least-squares
residual over every possible solution vector. -/
def zeroIsLeastSquaresSolution {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    euclideanNorm (b - M.mulVec (0 : Fin n → ℝ)) ≤
      euclideanNorm (b - M.mulVec x)

/-- The value of the matrix-only backward error at the zero vector. -/
noncomputable def zeroBackwardErrorValue {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : ℝ :=
  if b = 0 then 0 else euclideanNorm (A.transpose.mulVec b) / euclideanNorm b

theorem target :
    ∀ (m n : ℕ) (_ : n ≤ m)
      (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      ∃ ΔA : Matrix (Fin m) (Fin n) ℝ,
        zeroIsLeastSquaresSolution (A + ΔA) b ∧
        frobeniusNorm ΔA = zeroBackwardErrorValue A b ∧
        ∀ E : Matrix (Fin m) (Fin n) ℝ,
          zeroIsLeastSquaresSolution (A + E) b →
            zeroBackwardErrorValue A b ≤ frobeniusNorm E := by
  sorry

end HighamBenchCandidate
