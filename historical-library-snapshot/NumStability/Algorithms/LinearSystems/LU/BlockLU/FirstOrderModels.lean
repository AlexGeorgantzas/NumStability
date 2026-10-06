import Mathlib.Data.Matrix.Basic
import NumStability.Analysis.FirstOrder.FixedPrecision

/-!
# First-order local models for block LU

Reusable proposition-valued interfaces for rounded matrix multiplication,
left and right triangular solves, local and partitioned LU, subtraction, block
solves, and diagonal-block solves. Each specification pairs an exact residual
equation with a fixed-precision `FirstOrderLe` norm bound.

These source-neutral contracts model the local kernels used by block-LU error
analysis. Their Chapter 13 equation correspondence and numbered conclusions
belong in `NumStability.Source.Higham.Chapter13`.
-/

namespace NumStability

open scoped Matrix

/-- Matrix multiplication assumption (Higham, 2nd ed., Chapter 13, eq. 13.4)
    recorded at the scalar norm level. -/
def MatMulFirstOrderBound (u c₁ normA normB normDelta : ℝ) : Prop :=
  FirstOrderLe u (c₁ * u * normA * normB) normDelta

/-- Full matrix residual specification for Higham's matrix-multiplication model
    (Chapter 13, eq. 13.4): `Ĉ = A B + ΔC`, together with the scalar
    first-order norm bound. -/
structure MatMulFirstOrderSpec {m n p : Type*} [Fintype n]
    (u c₁ normA normB normDelta : ℝ)
    (A : Matrix m n ℝ) (B : Matrix n p ℝ)
    (Chat DeltaC : Matrix m p ℝ) : Prop where
  equation : Chat = A * B + DeltaC
  norm_bound : MatMulFirstOrderBound u c₁ normA normB normDelta

/-- Triangular multiple-right-hand-side solve assumption (Higham, 2nd ed.,
    Chapter 13, eq. 13.5), recorded at the scalar norm level. -/
def TriangularSolveFirstOrderBound (u c₂ normT normXhat normDeltaB : ℝ) : Prop :=
  FirstOrderLe u (c₂ * u * normT * normXhat) normDeltaB

/-- Full matrix residual specification for Higham's triangular-solve model
    (Chapter 13, eq. 13.5): `T X̂ = B + ΔB`, together with the scalar
    first-order norm bound. -/
structure TriangularSolveFirstOrderSpec {m p : Type*} [Fintype m]
    (u c₂ normT normXhat normDeltaB : ℝ)
    (T : Matrix m m ℝ) (B DeltaB Xhat : Matrix m p ℝ) : Prop where
  equation : T * Xhat = B + DeltaB
  norm_bound : TriangularSolveFirstOrderBound u c₂ normT normXhat normDeltaB

/-- Right-looking variant of the triangular-solve residual specification,
    used for proof steps such as Higham's equation (13.9):
    `X̂ T = B + ΔB`, with the same scalar first-order norm bound as (13.5).
    This is the transpose/right-solve orientation of the model assumption. -/
structure RightTriangularSolveFirstOrderSpec {m p : Type*} [Fintype p]
    (u c₂ normT normXhat normDeltaB : ℝ)
    (T : Matrix p p ℝ) (B DeltaB Xhat : Matrix m p ℝ) : Prop where
  equation : Xhat * T = B + DeltaB
  norm_bound : TriangularSolveFirstOrderBound u c₂ normT normXhat normDeltaB

/-- Block-level LU assumption (Higham, 2nd ed., Chapter 13, eq. 13.6), recorded
    at the scalar norm level. -/
def LocalLUFirstOrderBound (u c₃ normLhat normUhat normDeltaA : ℝ) : Prop :=
  FirstOrderLe u (c₃ * u * normLhat * normUhat) normDeltaA

/-- Full matrix residual specification for the block-level LU model
    (Chapter 13, eq. 13.6): `L̂ Û = A + ΔA`, together with the scalar
    first-order norm bound. -/
structure LocalLUFirstOrderSpec {r : Type*} [Fintype r]
    (u c₃ normLhat normUhat normDeltaA : ℝ)
    (A DeltaA Lhat Uhat : Matrix r r ℝ) : Prop where
  equation : Lhat * Uhat = A + DeltaA
  norm_bound : LocalLUFirstOrderBound u c₃ normLhat normUhat normDeltaA

/-- Full matrix residual specification for the subtraction step in Higham's
    Theorem 13.5 proof (Chapter 13, eq. 13.10): `Ŝ = A₂₂ - Ĉ + F`, together
    with the first-order subtraction-error bound. -/
structure SubtractionFirstOrderSpec {m p : Type*}
    (u normA normComputed normF : ℝ)
    (A Computed F Shat : Matrix m p ℝ) : Prop where
  equation : Shat = A - Computed + F
  norm_bound : normF ≤ u * (normA + normComputed)

/-- Recursive partitioned-LU first-order backward-error specification used as
    the induction hypothesis in Higham's Theorem 13.5 proof (Chapter 13,
    eqs. 13.12a--13.12b): `L̂ Û = Ŝ + ΔŜ`, together with the scalar
    first-order bound from equation (13.7) at the smaller block size. -/
structure PartitionedLUFirstOrderSpec {r : Type*} [Fintype r]
    (u δ θ normA normLhat normUhat normDeltaA : ℝ)
    (A DeltaA Lhat Uhat : Matrix r r ℝ) : Prop where
  equation : Lhat * Uhat = A + DeltaA
  norm_bound : FirstOrderLe u
    (u * (δ * normA + θ * normLhat * normUhat)) normDeltaA

/-- Block-LU step-2 assumption for Algorithm 13.3 (Higham, 2nd ed.,
    Chapter 13, eq. 13.14), recorded at the scalar norm level. -/
def BlockSolveFirstOrderBound (u c₄ normLhat21 normA11 normE21 : ℝ) : Prop :=
  FirstOrderLe u (c₄ * u * normLhat21 * normA11) normE21

/-- Full matrix residual specification for Algorithm 13.3 step 2
    (Higham, 2nd ed., Chapter 13, eq. 13.14): `L̂₂₁ A₁₁ = A₂₁ + E₂₁`,
    together with the scalar first-order norm bound. -/
structure BlockSolveFirstOrderSpec {r s : Type*} [Fintype r]
    (u c₄ normLhat21 normA11 normE21 : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 : Matrix r r ℝ) : Prop where
  equation : Lhat21 * A11 = A21 + E21
  norm_bound : BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21

/-- Diagonal-block solve assumption for block back substitution (Higham, 2nd ed.,
    Chapter 13, eq. 13.15), recorded at the scalar norm level. -/
def DiagonalBlockSolveFirstOrderBound (u c₅ normUii normDeltaUii : ℝ) : Prop :=
  FirstOrderLe u (c₅ * u * normUii) normDeltaUii

/-- Full residual specification for the diagonal-block solve model
    (Higham, 2nd ed., Chapter 13, eq. 13.15):
    `(Uᵢᵢ + ΔUᵢᵢ) X̂ = D`, together with the scalar first-order perturbation
    bound on `ΔUᵢᵢ`.  The source states the single-RHS case; the matrix
    right-hand side keeps the same residual equation reusable. -/
structure DiagonalBlockSolveFirstOrderSpec {r p : Type*} [Fintype r]
    (u c₅ normUii normDeltaUii : ℝ)
    (Uii DeltaUii : Matrix r r ℝ) (Xhat D : Matrix r p ℝ) : Prop where
  equation : (Uii + DeltaUii) * Xhat = D
  norm_bound : DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii

end NumStability
