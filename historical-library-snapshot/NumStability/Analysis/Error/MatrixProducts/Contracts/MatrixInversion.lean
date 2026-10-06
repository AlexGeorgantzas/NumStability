import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Analysis Error MatrixProducts Contracts MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Matrix product error bound** (Δ-notation, Higham §14.1).

    If Ĉ = fl(A₁ · A₂) then |Ĉ − A₁A₂| ≤ ε · (|A₁| · |A₂|).
    This predicate captures the general statement for any computed product. -/
def MatProdError (n : ℕ) (C_hat : Fin n → Fin n → ℝ)
    (C_exact : Fin n → Fin n → ℝ) (ε : ℝ)
    (absProduct : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |C_hat i j - C_exact i j| ≤ ε * absProduct i j

/-- Componentwise matrix-product-shaped bounds imply an infinity-norm bound
    with the absolute product retained. -/
theorem higham14_infNorm_le_of_componentwise_abs_matmul_bound {n : ℕ}
    {R A B : Fin n → Fin n → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hR : ∀ i j : Fin n,
      |R i j| ≤ ε * ∑ k : Fin n, |A i k| * |B k j|) :
    infNorm R ≤
      ε * infNorm (matMul n (absMatrix n A) (absMatrix n B)) := by
  let M := matMul n (absMatrix n A) (absMatrix n B)
  have hM_nonneg : ∀ i j : Fin n, 0 ≤ M i j := by
    intro i j
    dsimp [M, matMul, absMatrix]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |R i j|
          ≤ ∑ j : Fin n, ε * M i j := by
            apply Finset.sum_le_sum
            intro j _
            simpa [M, matMul, absMatrix] using hR i j
      _ = ε * ∑ j : Fin n, M i j := by
            rw [Finset.mul_sum]
      _ = ε * ∑ j : Fin n, |M i j| := by
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            exact (abs_of_nonneg (hM_nonneg i j)).symm
      _ ≤ ε * infNorm M := by
            exact mul_le_mul_of_nonneg_left (row_sum_le_infNorm M i) hε
  · exact mul_nonneg hε (infNorm_nonneg M)

/-- Componentwise matrix-product-shaped bounds imply an infinity-norm bound
    in terms of the two ordinary infinity norms. -/
theorem higham14_infNorm_le_of_componentwise_matmul_bound {n : ℕ}
    (hn : 0 < n) {R A B : Fin n → Fin n → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hR : ∀ i j : Fin n,
      |R i j| ≤ ε * ∑ k : Fin n, |A i k| * |B k j|) :
    infNorm R ≤ ε * infNorm A * infNorm B := by
  have hbase :=
    higham14_infNorm_le_of_componentwise_abs_matmul_bound
      (n := n) (R := R) (A := A) (B := B) hε hR
  have hmul :
      infNorm (matMul n (absMatrix n A) (absMatrix n B)) ≤
        infNorm A * infNorm B := by
    simpa [infNorm_absMatrix hn A, infNorm_absMatrix hn B] using
      infNorm_matMul_le hn (absMatrix n A) (absMatrix n B)
  calc
    infNorm R ≤
        ε * infNorm (matMul n (absMatrix n A) (absMatrix n B)) := hbase
    _ ≤ ε * (infNorm A * infNorm B) :=
        mul_le_mul_of_nonneg_left hmul hε
    _ = ε * infNorm A * infNorm B := by ring

/-- Scalar gamma collapse used in Higham Chapter 14, Problem 14.5:
    `u + gamma_n <= gamma_{n+1}`. -/
lemma higham14_unit_roundoff_add_gamma_le_gamma_succ
    (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    fp.u + gamma fp n ≤ gamma fp (n + 1) := by
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega : 1 ≤ n + 1) hn1
  have hvalidn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  have hγ_sum : gamma fp 1 + gamma fp n + gamma fp 1 * gamma fp n ≤
      gamma fp (n + 1) := by
    have h := gamma_sum_le fp 1 n (by simpa [Nat.add_comm] using hn1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hu_le_γ1 : fp.u ≤ gamma fp 1 :=
    u_le_gamma fp one_pos hvalid1
  have hγprod_nonneg : 0 ≤ gamma fp 1 * gamma fp n :=
    mul_nonneg (gamma_nonneg fp hvalid1) (gamma_nonneg fp hvalidn)
  linarith

/-- Scalar gamma collapse used by the Method 2 strict-tail dot-product adapter:
    `u + (1 + u) * gamma_n <= gamma_{n+1}`. -/
lemma higham14_unit_roundoff_add_one_plus_u_mul_gamma_le_gamma_succ
    (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    fp.u + (1 + fp.u) * gamma fp n ≤ gamma fp (n + 1) := by
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega : 1 ≤ n + 1) hn1
  have hvalidn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  have hγ_sum : gamma fp 1 + gamma fp n + gamma fp 1 * gamma fp n ≤
      gamma fp (n + 1) := by
    have h := gamma_sum_le fp 1 n (by simpa [Nat.add_comm] using hn1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hu_le_γ1 : fp.u ≤ gamma fp 1 :=
    u_le_gamma fp one_pos hvalid1
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hvalidn
  have hu_gamma_le : fp.u * gamma fp n ≤ gamma fp 1 * gamma fp n :=
    mul_le_mul_of_nonneg_right hu_le_γ1 hγn_nonneg
  nlinarith

/-- Scalar gamma collapse for a rounded strict-tail dot product followed by one
    rounded scalar multiplication and then the Method 2 diagonal factor:
    `u + (1 + u) * (gamma_n + u * (1 + gamma_n)) <= gamma_{n+2}`. -/
lemma higham14_unit_roundoff_add_one_plus_u_mul_rounded_gamma_le_gamma_succ_succ
    (fp : FPModel) (n : ℕ) (hn2 : gammaValid fp (n + 2)) :
    fp.u + (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) ≤
      gamma fp (n + 2) := by
  let C : ℝ := gamma fp n + fp.u * (1 + gamma fp n)
  let D : ℝ := fp.u + (1 + fp.u) * C
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega : 1 ≤ n + 2) hn2
  have hvalidn : gammaValid fp n :=
    gammaValid_mono fp (by omega : n ≤ n + 2) hn2
  have hvalidn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega : n + 1 ≤ n + 2) hn2
  have hvalidn1p1 : gammaValid fp ((n + 1) + 1) := by
    simpa [Nat.add_assoc] using hn2
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hvalidn
  have hu_abs_gamma1 : |fp.u| ≤ gamma fp 1 := by
    simpa [abs_of_nonneg fp.u_nonneg] using u_le_gamma fp one_pos hvalid1
  have hγn_abs : |gamma fp n| ≤ gamma fp n := by
    simp [abs_of_nonneg hγn_nonneg]
  obtain ⟨θ1, hθ1, hprod1⟩ :=
    gamma_mul fp n 1 (gamma fp n) fp.u hγn_abs hu_abs_gamma1 hvalidn1
  have hC_eq : C = θ1 := by
    have hC_prod : C = (1 + gamma fp n) * (1 + fp.u) - 1 := by
      simp [C]
      ring
    have hprod1' : (1 + gamma fp n) * (1 + fp.u) - 1 = θ1 := by
      linarith
    exact hC_prod.trans hprod1'
  have hC_nonneg : 0 ≤ C := by
    have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by linarith
    dsimp [C]
    exact add_nonneg hγn_nonneg (mul_nonneg fp.u_nonneg honeγ_nonneg)
  have hC_abs : |C| ≤ gamma fp (n + 1) := by
    rw [hC_eq]
    exact hθ1
  obtain ⟨θ2, hθ2, hprod2⟩ :=
    gamma_mul fp (n + 1) 1 C fp.u hC_abs hu_abs_gamma1 hvalidn1p1
  have hD_eq : D = θ2 := by
    have hD_prod : D = (1 + C) * (1 + fp.u) - 1 := by
      simp [D]
      ring
    have hprod2' : (1 + C) * (1 + fp.u) - 1 = θ2 := by
      linarith
    exact hD_prod.trans hprod2'
  have hD_nonneg : 0 ≤ D := by
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    dsimp [D]
    exact add_nonneg fp.u_nonneg (mul_nonneg honeu_nonneg hC_nonneg)
  have hD_le : D ≤ gamma fp ((n + 1) + 1) := by
    rw [hD_eq]
    have hθ2_nonneg : 0 ≤ θ2 := by
      rwa [← hD_eq]
    simpa [abs_of_nonneg hθ2_nonneg] using hθ2
  simpa [D, C, Nat.add_assoc] using hD_le

end NumStability
