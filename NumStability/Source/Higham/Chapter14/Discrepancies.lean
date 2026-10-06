import NumStability.Algorithms.MatrixInversion

namespace NumStability

/-!
# Higham Chapter 14 source corrections

Checked witnesses for statements whose printed hypotheses or signs are
inconsistent with their stated conclusions.
-/

/-- The signed ratio printed in Section 14.6 cannot be the asserted
    nonnegative condition number without an absolute value in the denominator.
    The one-by-one matrix `[-1]` gives the raw value `-1`. -/
theorem higham14_hadamardConditionNumberRaw_negative_one_counterexample :
    higham14_hadamardConditionNumberRaw
        (fun _ : Fin 1 => fun _ : Fin 1 => (-1 : ℝ)) = -1 := by
  simp [higham14_hadamardConditionNumberRaw, higham14_rowNorm2,
    vecNorm2, vecNorm2Sq]

end NumStability
