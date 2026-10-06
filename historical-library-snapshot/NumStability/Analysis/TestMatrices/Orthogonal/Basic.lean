import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.RandomSVD.Basic

/-!
# NumStability Analysis TestMatrices Orthogonal Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- A finite product of orthogonal matrices is orthogonal. -/
theorem matrixListProduct_isOrthogonal {n : ℕ}
    (Ps : List (Fin n → Fin n → ℝ))
    (hPs : ∀ P ∈ Ps, IsOrthogonal n P) :
    IsOrthogonal n (matrixListProduct Ps) := by
  induction Ps with
  | nil => exact IsOrthogonal.id n
  | cons P Ps ih =>
      exact (hPs P (by simp)).mul
        (ih (fun Q hQ => hPs Q (by simp [hQ])))

/-- Higham, 2nd ed., Section 28.3, p. 517, Theorem 28.1 (deterministic
orthogonality component): an orthogonal sign diagonal times the embedded
Householder transformations is orthogonal.  This theorem assumes only the
elementary orthogonality premises, not the source's probabilistic Haar
conclusion. -/
theorem higham28_theorem28_1_product_orthogonal {n : ℕ}
    (D : Fin n → Fin n → ℝ) (Ps : List (Fin n → Fin n → ℝ))
    (hD : IsOrthogonal n D)
    (hPs : ∀ P ∈ Ps, IsOrthogonal n P) :
    IsOrthogonal n (stewartOrthogonalProduct D Ps) := by
  exact hD.mul (matrixListProduct_isOrthogonal Ps hPs)

end NumStability
