import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation TwoNorm Dixon Algebra CondEstimators

Canonical destination for material split out of
`NumStability.Algorithms.Ch15CondEstimators` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open scoped Matrix

namespace Ch15

/-- The `M`-quadratic form `xᵀ M x`, written through `matMulVec`. -/
noncomputable def quadForm {n : ℕ} (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i * matMulVec n M x i

/-- **The Gram matrix `BᵀB` is a (two-sided) inverse of `A Aᵀ`.**

    If `B` is a two-sided inverse of `A` (so `B = A⁻¹`), then `(A Aᵀ)⁻¹ = Bᵀ B`.
    Concretely `Bᵀ B = (A⁻¹)ᵀ A⁻¹`, and this is the inverse appearing in Dixon's
    quadratic form `xᵀ(AAᵀ)⁻¹x` (Higham §15.5, eq. (15.7)).  Proved at matrix
    level from `A · B = I` and `B · A = I`. -/
theorem gram_inv_of_isInverse {n : ℕ} {A B : Fin n → Fin n → ℝ}
    (hR : IsRightInverse n A B) (hL : IsLeftInverse n A B) :
    IsInverse n (matMul n A (matTranspose A))
      (matMul n (matTranspose B) B) := by
  -- Work at Mathlib matrix level.
  set AM : Matrix (Fin n) (Fin n) ℝ := Matrix.of A with hAM
  set BM : Matrix (Fin n) (Fin n) ℝ := Matrix.of B with hBM
  have hAB : AM * BM = 1 := by
    ext i j; simpa [hAM, hBM, Matrix.mul_apply, Matrix.one_apply] using hR i j
  have hBA : BM * AM = 1 := by
    ext i j; simpa [hAM, hBM, Matrix.mul_apply, Matrix.one_apply] using hL i j
  -- `Bᵀ` is a two-sided inverse of `Aᵀ`.
  have hAtBt : AMᵀ * BMᵀ = 1 := by
    rw [← Matrix.transpose_mul]; rw [hBA]; simp
  have hBtAt : BMᵀ * AMᵀ = 1 := by
    rw [← Matrix.transpose_mul]; rw [hAB]; simp
  -- `(A Aᵀ)(Bᵀ B) = A (Aᵀ Bᵀ) B = A B = I`, and symmetrically.
  have hprod_right : (AM * AMᵀ) * (BMᵀ * BM) = 1 := by
    calc (AM * AMᵀ) * (BMᵀ * BM)
        = AM * (AMᵀ * BMᵀ) * BM := by
          simp only [Matrix.mul_assoc]
      _ = AM * BM := by rw [hAtBt]; simp
      _ = 1 := hAB
  have hprod_left : (BMᵀ * BM) * (AM * AMᵀ) = 1 := by
    calc (BMᵀ * BM) * (AM * AMᵀ)
        = BMᵀ * (BM * AM) * AMᵀ := by
          simp only [Matrix.mul_assoc]
      _ = BMᵀ * AMᵀ := by rw [hBA]; simp
      _ = 1 := hBtAt
  -- Translate the matrix identities to the repository predicates.
  have hAAt : matMul n A (matTranspose A) = fun i j => (AM * AMᵀ) i j := by
    ext i j; simp [matMul, matTranspose, hAM, Matrix.mul_apply]
  have hBtB : matMul n (matTranspose B) B = fun i j => (BMᵀ * BM) i j := by
    ext i j; simp [matMul, matTranspose, hBM, Matrix.mul_apply]
  constructor
  · -- left inverse: `(BᵀB)(AAᵀ) = I`
    intro i j
    rw [hAAt, hBtB]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hprod_left
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  · -- right inverse: `(AAᵀ)(BᵀB) = I`
    intro i j
    rw [hAAt, hBtB]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hprod_right
    simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- **Dixon's algebraic identity** (the identity underlying (15.7), Higham §15.5).

    The Dixon quadratic form of the inverse Gram matrix is the squared norm of the
    inverse acting on `x`:
        `xᵀ (Bᵀ B) x = ‖B x‖₂²`,
    where `B = A⁻¹`.  Combined with `gram_inv_of_isInverse` (which identifies
    `Bᵀ B = (A Aᵀ)⁻¹`), this is exactly
        `xᵀ (A Aᵀ)⁻¹ x = ‖A⁻¹ x‖₂²`,
    the `k = 1` content of Dixon's estimate.  Purely algebraic; no randomness. -/
theorem dixon_quadForm_gram_eq {n : ℕ} (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    quadForm (matMul n (matTranspose B) B) x = vecNorm2Sq (matMulVec n B x) := by
  unfold quadForm vecNorm2Sq
  -- Let `z = B x`.  `xᵀ(BᵀB)x = ∑ₖ zₖ² = ‖z‖²`.
  set z : Fin n → ℝ := matMulVec n B x with hz
  have hmv : ∀ i : Fin n,
      matMulVec n (matMul n (matTranspose B) B) x i =
        matMulVec n (matTranspose B) z i := by
    intro i; rw [hz]; exact matMulVec_matMul n (matTranspose B) B x i
  calc
    (∑ i : Fin n, x i * matMulVec n (matMul n (matTranspose B) B) x i)
        = ∑ i : Fin n, x i * matMulVec n (matTranspose B) z i := by
          exact Finset.sum_congr rfl (fun i _ => by rw [hmv i])
    _ = ∑ i : Fin n, x i * ∑ k : Fin n, B k i * z k := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          unfold matMulVec matTranspose; rfl
    _ = ∑ i : Fin n, ∑ k : Fin n, x i * (B k i * z k) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ i : Fin n, x i * (B k i * z k) := Finset.sum_comm
    _ = ∑ k : Fin n, z k * ∑ i : Fin n, B k i * x i := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ k : Fin n, z k * z k := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have : (∑ i : Fin n, B k i * x i) = z k := by rw [hz]; unfold matMulVec; rfl
          rw [this]
    _ = ∑ k : Fin n, z k ^ 2 := Finset.sum_congr rfl (fun k _ => by ring)

end Ch15
end NumStability
