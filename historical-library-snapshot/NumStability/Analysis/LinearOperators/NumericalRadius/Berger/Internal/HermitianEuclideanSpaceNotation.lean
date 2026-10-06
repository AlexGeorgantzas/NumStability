import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian
import NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Hermitian
import NumStability.Analysis.LinearOperators.NumericalRadius.Core.Basic

/-!
# Analysis.LinearOperators.NumericalRadius.Berger.Internal.HermitianEuclideanSpaceNotation

R07 canonical `internal` leaf. Unsupported private notation required by the nearest reusable owner (`_private.NumStability.Analysis.BergerInequality.0.NumStability.term𝔼`); the leaf is deliberately internal and is never advertised by a public aggregate.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.BergerInequality`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

end

end NumStability
