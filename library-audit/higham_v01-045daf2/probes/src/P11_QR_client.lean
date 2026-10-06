import NumStability.Algorithms.LinearSystems.QR.GivensSpec

#check NumStability.givensRotation_orthogonal

open NumStability

example (n : ℕ) (p q : Fin n) (c s : ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsOrthogonal n (givensRotation n p q c s) := by
  exact givensRotation_orthogonal n p q c s hpq hcs
