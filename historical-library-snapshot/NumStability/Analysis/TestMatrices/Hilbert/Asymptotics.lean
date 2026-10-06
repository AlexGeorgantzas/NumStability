import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# NumStability Analysis TestMatrices Hilbert Asymptotics

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Asymptotics` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open Filter Asymptotics

/-- The shifted Hilbert family `1/(i+j+2)` from p. 514. -/
noncomputable def shiftedHilbertMatrix (n : ℕ) : RSqMat n :=
  fun i j => 1 / (i.val + j.val + 2 : ℕ)

/-- A log-scale formulation of the leading exponential content in
`det(Hₙ) ~ 2^{-2n²}`. -/
def HilbertDetLeadingLogRate : Prop :=
  Tendsto
    (fun n : ℕ => Real.log (Matrix.det (hilbertMatrix n)) / (n : ℝ) ^ 2)
    atTop (nhds (-2 * Real.log 2))

/-- Precise Big-O reading of `‖H̃ₙ‖₂ = π + O(1/log n)`. -/
def ShiftedHilbertNormAsymptotic : Prop :=
  (fun n : ℕ => opNorm2 (shiftedHilbertMatrix n) - Real.pi) =O[atTop]
    (fun n : ℕ => 1 / Real.log n)

end NumStability
