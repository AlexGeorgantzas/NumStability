import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

/-!
# Chapter05 Equation14 MatrixPolynomialForms Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham (5.14), `P₁(X) = a₀I + a₁X + ⋯ + aₙXⁿ`, with complex
scalar coefficients stored in descending order. -/
noncomputable def complexMatrixPolyP1Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List ℂ → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | a :: rest => a • X ^ rest.length + complexMatrixPolyP1Desc n X rest

/-- Higham (5.14), `P₂(α) = A₀ + A₁α + ⋯ + Aₙαⁿ`, with complex
matrix coefficients stored in descending order. -/
noncomputable def complexMatrixPolyP2Desc (n : ℕ) (α : ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest =>
      (α ^ rest.length) • A + complexMatrixPolyP2Desc n α rest

/-- Higham (5.14), `P₃(X) = A₀ + A₁X + ⋯ + AₙXⁿ`, over complex
matrices, with descending matrix coefficients. -/
noncomputable def complexMatrixPolyP3Desc (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  | [] => 0
  | A :: rest =>
      A * X ^ rest.length + complexMatrixPolyP3Desc n X rest

/-- Higham (5.14), `P3(X) = A_0 + A_1 X + ... + A_n X^n`, represented with
descending matrix coefficients `[A_n, ..., A_0]`. -/
noncomputable def matrixPolyP3Desc (n : ℕ) (X : Fin n → Fin n → ℝ) :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => zeroMatrix n
  | A :: rest =>
      matAdd n (matMul n A (matPow n X rest.length))
        (matrixPolyP3Desc n X rest)

/-- The scalar majorant `ptilde_3(||X||)` for the matrix polynomial in
Problem 5.6, using the infinity norm and descending matrix coefficients. -/
noncomputable def matrixPolyP3InfNormMajorant (n : ℕ)
    (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) : ℝ :=
  polyDesc (infNorm X) (coeffsDesc.map infNorm)

/-- The scalar majorant `ptilde_3(||X||)` for the matrix polynomial in
Problem 5.6, using the one norm and descending matrix coefficients. -/
noncomputable def matrixPolyP3OneNormMajorant (n : ℕ)
    (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) : ℝ :=
  polyDesc (oneNorm X) (coeffsDesc.map oneNorm)

theorem matrixPolyP3InfNormMajorant_nonneg
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    0 ≤ matrixPolyP3InfNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      simp [matrixPolyP3InfNormMajorant, polyDesc]
  | cons A rest ih =>
      have hterm :
          0 ≤ infNorm A * infNorm X ^ rest.length :=
        mul_nonneg (infNorm_nonneg A)
          (pow_nonneg (infNorm_nonneg X) _)
      simpa [matrixPolyP3InfNormMajorant, polyDesc] using
        add_nonneg hterm ih

theorem matrixPolyP3OneNormMajorant_nonneg
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    0 ≤ matrixPolyP3OneNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      simp [matrixPolyP3OneNormMajorant, polyDesc]
  | cons A rest ih =>
      have hterm :
          0 ≤ oneNorm A * oneNorm X ^ rest.length :=
        mul_nonneg (oneNorm_nonneg A)
          (pow_nonneg (oneNorm_nonneg X) _)
      simpa [matrixPolyP3OneNormMajorant, polyDesc] using
        add_nonneg hterm ih

theorem matrixPolyP3Desc_infNorm_le_majorant
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ))
    (hnpos : 0 < n) :
    infNorm (matrixPolyP3Desc n X coeffsDesc) ≤
      matrixPolyP3InfNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      simpa [matrixPolyP3Desc, matrixPolyP3InfNormMajorant, polyDesc]
        using le_of_eq (infNorm_zeroMatrix n)
  | cons A rest ih =>
      let term : Fin n → Fin n → ℝ := matMul n A (matPow n X rest.length)
      let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
      have hadd :
          infNorm (matAdd n term tail) ≤ infNorm term + infNorm tail := by
        simpa [matAdd] using infNorm_add_le term tail
      have hmul :
          infNorm term ≤ infNorm A * infNorm (matPow n X rest.length) := by
        simpa [term] using
          infNorm_matMul_le hnpos A (matPow n X rest.length)
      have hpow :
          infNorm (matPow n X rest.length) ≤ infNorm X ^ rest.length :=
        infNorm_matPow_le hnpos X rest.length
      have hterm :
          infNorm term ≤ infNorm A * infNorm X ^ rest.length :=
        le_trans hmul
          (mul_le_mul_of_nonneg_left hpow (infNorm_nonneg A))
      calc
        infNorm (matrixPolyP3Desc n X (A :: rest))
            = infNorm (matAdd n term tail) := rfl
        _ ≤ infNorm term + infNorm tail := hadd
        _ ≤ infNorm A * infNorm X ^ rest.length +
              matrixPolyP3InfNormMajorant n X rest :=
            add_le_add hterm ih
        _ = matrixPolyP3InfNormMajorant n X (A :: rest) := by
            simp [matrixPolyP3InfNormMajorant, polyDesc]

theorem matrixPolyP3Desc_oneNorm_le_majorant
    (n : ℕ) (X : Fin n → Fin n → ℝ)
    (coeffsDesc : List (Fin n → Fin n → ℝ)) :
    oneNorm (matrixPolyP3Desc n X coeffsDesc) ≤
      matrixPolyP3OneNormMajorant n X coeffsDesc := by
  induction coeffsDesc with
  | nil =>
      have hone_zero : oneNorm (zeroMatrix n) = 0 := by
        unfold oneNorm
        simpa [zeroMatrix] using infNorm_zeroMatrix n
      simpa [matrixPolyP3Desc, matrixPolyP3OneNormMajorant, polyDesc]
        using le_of_eq hone_zero
  | cons A rest ih =>
      let term : Fin n → Fin n → ℝ := matMul n A (matPow n X rest.length)
      let tail : Fin n → Fin n → ℝ := matrixPolyP3Desc n X rest
      have hadd :
          oneNorm (matAdd n term tail) ≤ oneNorm term + oneNorm tail := by
        simpa [matAdd] using oneNorm_add_le term tail
      have hmul :
          oneNorm term ≤ oneNorm A * oneNorm (matPow n X rest.length) := by
        simpa [term] using
          oneNorm_matMul_le A (matPow n X rest.length)
      have hpow :
          oneNorm (matPow n X rest.length) ≤ oneNorm X ^ rest.length :=
        oneNorm_matPow_le X rest.length
      have hterm :
          oneNorm term ≤ oneNorm A * oneNorm X ^ rest.length :=
        le_trans hmul
          (mul_le_mul_of_nonneg_left hpow (oneNorm_nonneg A))
      calc
        oneNorm (matrixPolyP3Desc n X (A :: rest))
            = oneNorm (matAdd n term tail) := rfl
        _ ≤ oneNorm term + oneNorm tail := hadd
        _ ≤ oneNorm A * oneNorm X ^ rest.length +
              matrixPolyP3OneNormMajorant n X rest :=
            add_le_add hterm ih
        _ = matrixPolyP3OneNormMajorant n X (A :: rest) := by
            simp [matrixPolyP3OneNormMajorant, polyDesc]

end NumStability
