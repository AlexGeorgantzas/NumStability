import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2.Method2Loop
import NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MethodDUpperCertificate

/-!
# Chapter14 Section03 LUFactorInversion MethodD MethodDProductDischarge

Canonical destination for material split out of
`NumStability.Algorithms.Ch14MethodDProductDischarge` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

/-- **Higham §3.5 (eq 3.13) fl-matmul certificate for Method D's product step.**

    The computed inverse `X̂ = fl_matMul fp X_U X_L` (the concrete column-by-column
    floating-point product of the reversal-conjugated upper Method 2 inverse
    `X_U = ch14ext_method2InvUpper n fp U` and the wave-2 lower Method 2 inverse
    `X_L = ch14ext_method2Inv n fp L`) satisfies the componentwise product-error
    certificate

        |X̂ᵢⱼ − (X_U X_L)ᵢⱼ| ≤ γ_{n+2} · (|X_U||X_L|)ᵢⱼ

    DERIVED from `matMul_error_bound` (which gives the bound at `γ_n`) and lifted
    to the shared Method D accumulator `γ_{n+2}` by accumulator monotonicity
    (`gamma_mono`, valid since `n ≤ n+2` and the weight `(|X_U||X_L|)ᵢⱼ ≥ 0`).
    This is exactly the `hProd` slot of `ch14ext_methodD_left_residual_both`,
    now DISCHARGED. -/
theorem ch14ext_methodD_prod_error_flMatMul (n : ℕ) (fp : FPModel)
    (L U : Fin n → Fin n → ℝ) (hn2 : gammaValid fp (n + 2)) :
    MatProdError n
      (fl_matMul fp n n n
        (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
      (matMul n (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
      (gamma fp (n + 2))
      (fun i j => ∑ k : Fin n,
        |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j|) := by
  intro i j
  have hnv : gammaValid fp n := gammaValid_mono fp (by omega) hn2
  have hb := matMul_error_bound fp n n n
    (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) hnv i j
  have hw_nonneg :
      0 ≤ ∑ k : Fin n,
        |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- `matMul n X_U X_L i j` is defeq `∑ k, X_U i k * X_L k j`, matching `matMul_error_bound`.
  show |fl_matMul fp n n n
        (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i j -
      ∑ k : Fin n,
        ch14ext_method2InvUpper n fp U i k * ch14ext_method2Inv n fp L k j| ≤
      gamma fp (n + 2) *
        ∑ k : Fin n,
          |ch14ext_method2InvUpper n fp U i k| * |ch14ext_method2Inv n fp L k j|
  exact hb.trans (mul_le_mul_of_nonneg_right (gamma_mono fp (by omega) hn2) hw_nonneg)

/-- **Higham (14.23), Method D left residual — product step DISCHARGED.**

    The printed `(4γ + 2γ²)` componentwise Method D envelope for the CONCRETE
    computed inverse

        X̂ := fl_matMul fp n n n X_U X_L ,
        X_U := ch14ext_method2InvUpper n fp U ,   X_L := ch14ext_method2Inv n fp L,

    with THREE of the four Method D certificates now discharged internally:

      * the UPPER-triangular inverse LEFT residual (reversal-conjugated Method 2
        loop, `ch14ext_method2Upper_left_residual`);
      * the LOWER-triangular inverse LEFT residual (wave-2 Method 2 loop,
        `ch14ext_method2_left_residual`);
      * the product-formation certificate (this file's
        `ch14ext_methodD_prod_error_flMatMul`).

    Compared with `ch14ext_methodD_left_residual_both`, the `hProd` hypothesis is
    ELIMINATED (X̂ is now the honest floating-point product, not a free matrix).

    The SINGLE remaining hypothesis is the genuine upstream LU backward-error
    certificate `hLU` (Higham Thm 9.3).  Per the file header's strength note, the
    repo has no unconditional `LUBackwardError` producer for arbitrary `A` from
    the GE loop (the concrete-loop chain needs undischarged per-stage
    budget/dominance bounds, and the exact producer would force `A = L̂Û`), so
    `hLU` is retained exactly as Higham states it. -/
theorem ch14ext_methodD_left_residual_prodFree (n : ℕ) (fp : FPModel)
    (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnz : ∀ j : Fin n, L j j ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hLU : LUBackwardError n A L U (gamma fp (n + 2))) :
    ∀ i j : Fin n,
      |∑ k : Fin n,
          fl_matMul fp n n n
            (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i k
            * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |ch14ext_method2InvUpper n fp U i q|
                * |ch14ext_method2Inv n fp L q p|) *
              (∑ r : Fin n, |L p r| * |U r j|) :=
  ch14ext_methodD_left_residual_both n fp A L U
    (fl_matMul fp n n n
      (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
    hn2 hLT hLnz hUT hUnz hLU
    (ch14ext_methodD_prod_error_flMatMul n fp L U hn2)

/-- **Higham (14.23), Method D left residual — product step DISCHARGED, normwise.**

    Infinity-norm companion of `ch14ext_methodD_left_residual_prodFree`: same
    concrete computed inverse `X̂ = fl_matMul fp X_U X_L`, same three internally
    discharged certificates, same single remaining `hLU` hypothesis. -/
theorem ch14ext_methodD_left_residual_prodFree_infNorm (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel) (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hLnz : ∀ j : Fin n, L j j ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hLU : LUBackwardError n A L U (gamma fp (n + 2))) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n,
        fl_matMul fp n n n
          (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i k
          * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
        infNorm (matMul n (absMatrix n (ch14ext_method2InvUpper n fp U))
          (absMatrix n (ch14ext_method2Inv n fp L))) *
          infNorm (matMul n (absMatrix n L) (absMatrix n U)) :=
  ch14ext_methodD_left_residual_both_infNorm n hn0 fp A L U
    (fl_matMul fp n n n
      (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L))
    hn2 hLT hLnz hUT hUnz hLU
    (ch14ext_methodD_prod_error_flMatMul n fp L U hn2)

/-- **Higham (14.23), Method D from the Chapter 9 Doolittle computation
    certificate.**

    This is the implementation-facing componentwise endpoint.  The formerly
    free `LUBackwardError` hypothesis is derived from `DoolittleLU` by the
    proved Chapter 9 backward-error theorem, then weakened from `gamma_n` to
    the common `gamma_(n+2)` budget used by the two concrete triangular-inverse
    loops.  The only extra condition is that the computed upper factor has
    nonzero diagonal, exactly the successful-factorization condition needed by
    the reciprocal steps. -/
theorem ch14ext_methodD_left_residual_doolittle (n : ℕ) (fp : FPModel)
    (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hD : DoolittleLU n A L U fp) :
    ∀ i j : Fin n,
      |∑ k : Fin n,
          fl_matMul fp n n n
            (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i k
            * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |ch14ext_method2InvUpper n fp U i q|
                * |ch14ext_method2Inv n fp L q p|) *
              (∑ r : Fin n, |L p r| * |U r j|) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn2
  have hLU_n : LUBackwardError n A L U (gamma fp n) :=
    DoolittleLU.to_LUBackwardError n fp A L U hn hD
  have hLU : LUBackwardError n A L U (gamma fp (n + 2)) :=
    higham9_LUBackwardError_mono hLU_n (gamma_mono fp (by omega) hn2)
  exact ch14ext_methodD_left_residual_prodFree n fp A L U hn2
    hD.L_upper_zero (fun j => by rw [hD.L_diag j]; norm_num)
    hD.U_lower_zero hUnz hLU

/-- Infinity-norm companion to
    `ch14ext_methodD_left_residual_doolittle`. -/
theorem ch14ext_methodD_left_residual_doolittle_infNorm
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L U : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hUnz : ∀ j : Fin n, U j j ≠ 0)
    (hD : DoolittleLU n A L U fp) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n,
        fl_matMul fp n n n
          (ch14ext_method2InvUpper n fp U) (ch14ext_method2Inv n fp L) i k
          * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp (n + 2) + 2 * gamma fp (n + 2) ^ 2) *
        infNorm (matMul n (absMatrix n (ch14ext_method2InvUpper n fp U))
          (absMatrix n (ch14ext_method2Inv n fp L))) *
          infNorm (matMul n (absMatrix n L) (absMatrix n U)) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn2
  have hLU_n : LUBackwardError n A L U (gamma fp n) :=
    DoolittleLU.to_LUBackwardError n fp A L U hn hD
  have hLU : LUBackwardError n A L U (gamma fp (n + 2)) :=
    higham9_LUBackwardError_mono hLU_n (gamma_mono fp (by omega) hn2)
  exact ch14ext_methodD_left_residual_prodFree_infNorm n hn0 fp A L U hn2
    hD.L_upper_zero (fun j => by rw [hD.L_diag j]; norm_num)
    hD.U_lower_zero hUnz hLU

end Ch14Ext
end NumStability
