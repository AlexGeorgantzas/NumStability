import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Existence

Canonical destination for 1 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.CholeskyPSD` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **SPD Cholesky as pivoted Cholesky** (Higham §10.3, Theorem 10.9, part b, full rank case).

    For SPD matrices, the Cholesky factorization from Theorem 10.1 satisfies
    PivotedCholeskySpec with identity permutation and rank r = n.
    All diagonal entries are strictly positive and no rows are zero. -/
theorem spd_pivoted_cholesky (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      PivotedCholeskySpec n A R id n := by
  obtain ⟨R, hR⟩ := cholesky_existence n A hSPD
  exact ⟨R,
    { perm := Function.bijective_id
      R_upper := hR.R_upper
      R_diag_pos := fun i _ => hR.R_diag_pos i
      R_rank_zero := fun i _ hri => absurd hri (by omega)
      product_eq := fun i j => hR.product_eq i j }⟩

end NumStability
