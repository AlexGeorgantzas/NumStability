import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# NumStability Analysis TestMatrices RandomSVD Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.3, p. 517: `A = U Σ Vᵀ`. -/
noncomputable def randsvdMatrix {m n : ℕ} (U : RSqMat m) (σ : ℕ → ℝ)
    (V : RSqMat n) : RMat m n :=
  U * (rectangularDiagonal (m := m) (n := n) σ) * V.transpose

/-- The deterministic product in Stewart's Theorem 28.1: `Q = D P₁...Pₙ₋₁`. -/
noncomputable def stewartOrthogonalProduct {n : ℕ}
    (D : Fin n → Fin n → ℝ) (Ps : List (Fin n → Fin n → ℝ)) :
    Fin n → Fin n → ℝ :=
  matMul n D (matrixListProduct Ps)

end NumStability
