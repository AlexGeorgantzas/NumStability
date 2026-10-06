import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import NumStability.Analysis.LinearOperators.NumericalRadius.Core.Basic

/-!
# Analysis.LinearOperators.NumericalRadius.Core.Internal.EuclideanSpaceNotation

R07 canonical `internal` leaf. Unsupported private notation required by the nearest reusable owner (`_private.NumStability.Analysis.NumericalRadius.0.NumStability.term𝔼`); the leaf is deliberately internal and is never advertised by a public aggregate.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.NumericalRadius`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

/-- The complex Euclidean space `ℂⁿ` used as the ambient inner-product space for
the numerical range.  A local abbreviation to keep signatures short. -/
local notation "𝔼" => EuclideanSpace ℂ (Fin n)

end

end NumStability
