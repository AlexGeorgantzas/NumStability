import NumStability.Analysis.VectorNorms.Basic

#check NumStability.complexVecLpNorm_two_ofLp_eq

open NumStability

example {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) (WithLp.ofLp x) = ‖x‖ := by
  exact complexVecLpNorm_two_ofLp_eq x
