import NumStability.Analysis.ConditionEstimatorLowerBound

#check NumStability.condOneNumber_ge_scaled_estimator

open NumStability

example {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) :
    oneNorm A * lapackNormEstimator hn B ≤ condOneNumber A B := by
  exact condOneNumber_ge_scaled_estimator hn A B
