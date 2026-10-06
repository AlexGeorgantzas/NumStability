import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteDimensional

R07 canonical `reusable` leaf. Declaration-level review groups 1 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrix_complex_finiteDimensional`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Finite complex `CStarMatrix` spaces are finite-dimensional complex vector
spaces.  The proof unfolds the type synonym to the finite Pi-space
`m → n → ℂ`. -/
noncomputable instance cstarMatrix_complex_finiteDimensional
    {m n : Type*} [Fintype m] [Fintype n] :
    FiniteDimensional ℂ (CStarMatrix m n ℂ) := by
  change FiniteDimensional ℂ (m → n → ℂ)
  infer_instance

end NumStability
