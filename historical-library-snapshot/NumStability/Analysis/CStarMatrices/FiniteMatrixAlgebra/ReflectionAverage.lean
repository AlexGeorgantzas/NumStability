import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ProjectionReflection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularMultiplication
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.ReflectionAverage

R07 canonical `reusable` leaf. Declaration-level review groups 4 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrix_commute_projection_of_commute_reflection`, `NumStability.cstarMatrix_reflectionAverage_commute_of_involutive`, `NumStability.cstarMatrix_reflectionAverage_compression_of_fixed`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- If a square matrix `R` fixes the compression column on the left and the
compression row on the right, then replacing `D` by the reflection average
`(D + RDR)/2` does not change the compressed matrix. -/
theorem cstarMatrix_reflectionAverage_compression_of_fixed
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (W : CStarMatrix β α ℂ) (R D : CStarMatrix α α ℂ)
    (V : CStarMatrix α β ℂ)
    (hWR : W * R = W) (hRV : R * V = V) :
    W * ((1 / 2 : ℂ) • (D + R * D * R)) * V =
      W * D * V := by
  have hRDR_compress :
      W * (R * D * R) * V = W * D * V := by
    calc
      W * (R * D * R) * V =
          W * ((R * D * R) * V) := by
            rw [cstarMatrix_mul_assoc_rect W (R * D * R) V]
      _ = W * ((R * D) * (R * V)) := by
            rw [cstarMatrix_mul_assoc_rect (R * D) R V]
      _ = W * ((R * D) * V) := by
            rw [hRV]
      _ = W * (R * (D * V)) := by
            rw [cstarMatrix_mul_assoc_rect R D V]
      _ = (W * R) * (D * V) := by
            rw [← cstarMatrix_mul_assoc_rect W R (D * V)]
      _ = W * (D * V) := by
            rw [hWR]
      _ = W * D * V := by
            rw [← cstarMatrix_mul_assoc_rect W D V]
  have hsum :
      W * (D + R * D * R) * V =
        W * D * V + W * D * V := by
    calc
      W * (D + R * D * R) * V =
          (W * D + W * (R * D * R)) * V := by
            rw [cstarMatrix_mul_add_rect W D (R * D * R)]
      _ = W * D * V + W * (R * D * R) * V := by
            rw [cstarMatrix_add_mul_rect (W * D) (W * (R * D * R)) V]
      _ = W * D * V + W * D * V := by
            rw [hRDR_compress]
  calc
    W * ((1 / 2 : ℂ) • (D + R * D * R)) * V =
        ((1 / 2 : ℂ) • (W * (D + R * D * R))) * V := by
          rw [cstarMatrix_mul_smul_rect (1 / 2 : ℂ) W (D + R * D * R)]
    _ = (1 / 2 : ℂ) • (W * (D + R * D * R) * V) := by
          rw [cstarMatrix_smul_mul_rect (1 / 2 : ℂ)
            (W * (D + R * D * R)) V]
    _ = (1 / 2 : ℂ) • (W * D * V + W * D * V) := by
          rw [hsum]
    _ = W * D * V := by
          ext i j
          simp
          ring

/-- The reflection average `(D + RDR)/2` is fixed by conjugation with `R`
whenever `R^2 = I`. -/
theorem cstarMatrix_reflectionAverage_conj_of_involutive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R D : CStarMatrix ι ι ℂ) (hR : R * R = 1) :
    R * ((1 / 2 : ℂ) • (D + R * D * R)) * R =
      (1 / 2 : ℂ) • (D + R * D * R) := by
  have hsecond :
      R * (R * D * R) * R = D := by
    calc
      R * (R * D * R) * R =
          R * ((R * D * R) * R) := by
            rw [cstarMatrix_mul_assoc_rect R (R * D * R) R]
      _ = R * ((R * D) * (R * R)) := by
            rw [cstarMatrix_mul_assoc_rect (R * D) R R]
      _ = R * ((R * D) * 1) := by
            rw [hR]
      _ = R * (R * D) := by
            rw [cstarMatrix_mul_one_rect (R * D)]
      _ = (R * R) * D := by
            rw [← cstarMatrix_mul_assoc_rect R R D]
      _ = 1 * D := by
            rw [hR]
      _ = D := by
            rw [cstarMatrix_one_mul_rect D]
  have hsum :
      R * (D + R * D * R) * R = R * D * R + D := by
    calc
      R * (D + R * D * R) * R =
          (R * D + R * (R * D * R)) * R := by
            rw [cstarMatrix_mul_add_rect R D (R * D * R)]
      _ = R * D * R + R * (R * D * R) * R := by
            rw [cstarMatrix_add_mul_rect (R * D) (R * (R * D * R)) R]
      _ = R * D * R + D := by
            rw [hsecond]
  calc
    R * ((1 / 2 : ℂ) • (D + R * D * R)) * R =
        ((1 / 2 : ℂ) • (R * (D + R * D * R))) * R := by
          rw [cstarMatrix_mul_smul_rect (1 / 2 : ℂ) R (D + R * D * R)]
    _ = (1 / 2 : ℂ) • (R * (D + R * D * R) * R) := by
          rw [cstarMatrix_smul_mul_rect (1 / 2 : ℂ)
            (R * (D + R * D * R)) R]
    _ = (1 / 2 : ℂ) • (R * D * R + D) := by
          rw [hsum]
    _ = (1 / 2 : ℂ) • (D + R * D * R) := by
          ext i j
          simp [add_comm]

/-- The reflection average `(D + RDR)/2` commutes with `R` whenever
`R^2 = I`. -/
theorem cstarMatrix_reflectionAverage_commute_of_involutive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R D : CStarMatrix ι ι ℂ) (hR : R * R = 1) :
    R * ((1 / 2 : ℂ) • (D + R * D * R)) =
      ((1 / 2 : ℂ) • (D + R * D * R)) * R := by
  let E : CStarMatrix ι ι ℂ := (1 / 2 : ℂ) • (D + R * D * R)
  have hconj : R * E * R = E := by
    dsimp [E]
    exact cstarMatrix_reflectionAverage_conj_of_involutive R D hR
  have hleft : (R * E * R) * R = R * E := by
    calc
      (R * E * R) * R = (R * E) * (R * R) := by
        rw [cstarMatrix_mul_assoc_rect (R * E) R R]
      _ = (R * E) * 1 := by
        rw [hR]
      _ = R * E := by
        rw [cstarMatrix_mul_one_rect (R * E)]
  have hmul := congrArg (fun X : CStarMatrix ι ι ℂ => X * R) hconj
  calc
    R * E = (R * E * R) * R := by
      rw [hleft]
    _ = E * R := hmul

/-- Commutation with the reflection `2P - I` implies commutation with the
projection `P`. -/
theorem cstarMatrix_commute_projection_of_commute_reflection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E : CStarMatrix ι ι ℂ)
    (hRE :
      cstarMatrixProjectionReflection P * E =
        E * cstarMatrixProjectionReflection P) :
    P * E = E * P := by
  ext i j
  have hREij := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hRE
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply, sub_mul, mul_sub, Finset.sum_sub_distrib] at hREij
  have hcancel := congrArg (fun z : ℂ => z + E i j) hREij
  ring_nf at hcancel
  have hsum_cancel :
      (∑ x, P i x * E x j * 2) =
        (∑ x, E i x * P x j * 2) := by
    have htmp :
        (∑ x, P i x * E x j * 2) + E i j =
          (∑ x, E i x * P x j * 2) + E i j := by
      calc
        (∑ x, P i x * E x j * 2) + E i j =
            E i j + ∑ x, E i x * P x j * 2 := hcancel
        _ = (∑ x, E i x * P x j * 2) + E i j := by
            rw [add_comm]
    exact add_right_cancel htmp
  have hcancel' : (2 : ℂ) * (P * E) i j = (2 : ℂ) * (E * P) i j := by
    simpa [CStarMatrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm,
      mul_assoc] using hsum_cancel
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ htwo hcancel'

end NumStability
