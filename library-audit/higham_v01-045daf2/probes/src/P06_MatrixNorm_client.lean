import NumStability.Analysis.MatrixNorms.Lp

#check NumStability.complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm

open NumStability

example {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A
      ((n : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A) := by
  exact complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm hp A
