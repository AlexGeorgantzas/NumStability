import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# InteriorMass

Canonical destination for 1 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Per-stage interior mass from the full scaled certificate**
    (Theorem 10.7 sharp route, certificate restriction): a single
    quadratic-form certificate `ε` on the full scaled defect restricts
    to every leading block by zero-padding — the stage-`k` interior
    mass hypothesis of `fl_cholesky_pivot_pos_step_sharp` follows for
    all stages at once. -/
theorem stage_interior_mass_from_full {n : ℕ}
    (Δ : Fin n → Fin n → ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ)
    (hcert : ∀ z : Fin n → ℝ,
      |∑ i : Fin n, ∑ j : Fin n, z i *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j| ≤
      ε * ∑ i : Fin n, z i ^ 2)
    (hnz : ∀ i j : Fin n, a i = 0 ∨ a j = 0 → Δ i j = 0)
    (k : ℕ) (hk : k ≤ n) (y : Fin k → ℝ) :
    |∑ i : Fin k, ∑ j : Fin k, y i *
      Δ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j| ≤
      ε * ∑ i : Fin k, a ⟨i.val, by omega⟩ * y i ^ 2 := by
  refine scaled_interior_mass_normwise_quad
    (fun i j : Fin k => Δ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    (fun i : Fin k => a ⟨i.val, by omega⟩) (fun i => ha _) ε
    ?_ y (fun i j h => hnz _ _ h)
  intro z
  have hpad := hcert
    (fun i : Fin n => if h : i.val < k then z ⟨i.val, h⟩ else 0)
  have hq := quadForm_zero_pad_eq
    (fun i j : Fin n => Δ i j /
      (Real.sqrt (a i) * Real.sqrt (a j))) k hk z
  have hs := sum_sq_zero_pad_eq k hk z
  rw [hq, hs] at hpad
  exact hpad

end NumStability
