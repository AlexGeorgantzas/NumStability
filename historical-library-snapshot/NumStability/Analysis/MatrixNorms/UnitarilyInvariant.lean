-- Analysis/MatrixNorms/UnitarilyInvariant.lean
--
-- Unitarily invariant norms on finite complex matrices.

import NumStability.Analysis.SingularValues.Basic

/-!
# Unitarily invariant matrix norms

Defines unitarily invariant matrix-norm interfaces and proves their structural
properties through singular values and unitary actions.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Source-facing fixed rectangular matrix norm axioms plus left/right unitary
    invariance. This is the bare fixed-shape version of "unitarily invariant
    matrix norm" used in Higham Problem 6.5. -/
structure ComplexMatrixFixedUnitaryInvariantNorm (m n : ℕ) where
  norm : CMatrix m n → ℝ
  norm_nonneg : ∀ (A : CMatrix m n), 0 <= norm A
  eq_zero_iff : ∀ (A : CMatrix m n), norm A = 0 ↔ A = 0
  smul : ∀ (a : ℂ) (A : CMatrix m n),
    norm (((a • (A : Matrix (Fin m) (Fin n) ℂ)) : Matrix (Fin m) (Fin n) ℂ) :
      CMatrix m n) = ‖a‖ * norm A
  add_le : ∀ (A B : CMatrix m n),
    norm (((A : Matrix (Fin m) (Fin n) ℂ) + B : Matrix (Fin m) (Fin n) ℂ) :
      CMatrix m n) <= norm A + norm B
  left_unitary : ∀ (U : Matrix.unitaryGroup (Fin m) ℂ) (A : CMatrix m n),
    norm (complexMatrixMul ((U : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A) =
      norm A
  right_unitary : ∀ (A : CMatrix m n) (V : Matrix.unitaryGroup (Fin n) ℂ),
    norm (complexMatrixMul A ((V : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n)) =
      norm A

theorem ComplexMatrixFixedUnitaryInvariantNorm.left_contraction_le
    {m n : ℕ} (ξ : ComplexMatrixFixedUnitaryInvariantNorm m n)
    (hmid : ComplexSquareContractionMidpointProperty m)
    (L : CMatrix m m) (A : CMatrix m n)
    (hL : complexMatrixOp2 L <= 1) :
    ξ.norm (complexMatrixMul L A) <= ξ.norm A := by
  obtain ⟨U, V, hUV⟩ := hmid L hL
  have hmul :
      complexMatrixMul L A =
        (((1 / 2 : ℂ) •
          (((complexMatrixMul ((U : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A :
              Matrix (Fin m) (Fin n) ℂ) +
            complexMatrixMul ((V : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A)) :
          Matrix (Fin m) (Fin n) ℂ) : CMatrix m n) := by
    ext i j
    rw [hUV]
    simp [complexMatrixMul, Finset.mul_sum, Finset.sum_add_distrib,
      mul_add, mul_left_comm, mul_comm]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  calc
    ξ.norm (complexMatrixMul L A)
        = ξ.norm
          (((1 / 2 : ℂ) •
            (((complexMatrixMul ((U : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A :
                Matrix (Fin m) (Fin n) ℂ) +
              complexMatrixMul ((V : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A)) :
            Matrix (Fin m) (Fin n) ℂ) : CMatrix m n) := by rw [hmul]
    _ = ‖(1 / 2 : ℂ)‖ *
          ξ.norm
            ((((complexMatrixMul ((U : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A :
                Matrix (Fin m) (Fin n) ℂ) +
              complexMatrixMul ((V : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A) :
              Matrix (Fin m) (Fin n) ℂ) : CMatrix m n) :=
        ξ.smul (1 / 2 : ℂ) _
    _ <= (1 / 2 : ℝ) *
          (ξ.norm (complexMatrixMul ((U : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A) +
            ξ.norm (complexMatrixMul ((V : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A)) := by
        rw [hhalf]
        exact mul_le_mul_of_nonneg_left
          (ξ.add_le
            (complexMatrixMul ((U : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A)
            (complexMatrixMul ((V : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m) A))
          (by norm_num)
    _ = ξ.norm A := by
        rw [ξ.left_unitary U A, ξ.left_unitary V A]
        ring

theorem ComplexMatrixFixedUnitaryInvariantNorm.right_contraction_le
    {m n : ℕ} (ξ : ComplexMatrixFixedUnitaryInvariantNorm m n)
    (hmid : ComplexSquareContractionMidpointProperty n)
    (A : CMatrix m n) (R : CMatrix n n)
    (hR : complexMatrixOp2 R <= 1) :
    ξ.norm (complexMatrixMul A R) <= ξ.norm A := by
  obtain ⟨U, V, hUV⟩ := hmid R hR
  have hmul :
      complexMatrixMul A R =
        (((1 / 2 : ℂ) •
          (((complexMatrixMul A ((U : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n) :
              Matrix (Fin m) (Fin n) ℂ) +
            complexMatrixMul A ((V : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n))) :
          Matrix (Fin m) (Fin n) ℂ) : CMatrix m n) := by
    ext i j
    rw [hUV]
    simp [complexMatrixMul, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
      mul_left_comm]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  calc
    ξ.norm (complexMatrixMul A R)
        = ξ.norm
          (((1 / 2 : ℂ) •
            (((complexMatrixMul A ((U : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n) :
                Matrix (Fin m) (Fin n) ℂ) +
              complexMatrixMul A ((V : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n))) :
            Matrix (Fin m) (Fin n) ℂ) : CMatrix m n) := by rw [hmul]
    _ = ‖(1 / 2 : ℂ)‖ *
          ξ.norm
            ((((complexMatrixMul A ((U : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n) :
                Matrix (Fin m) (Fin n) ℂ) +
              complexMatrixMul A ((V : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n)) :
              Matrix (Fin m) (Fin n) ℂ) : CMatrix m n) :=
        ξ.smul (1 / 2 : ℂ) _
    _ <= (1 / 2 : ℝ) *
          (ξ.norm (complexMatrixMul A ((U : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n)) +
            ξ.norm (complexMatrixMul A ((V : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n))) := by
        rw [hhalf]
        exact mul_le_mul_of_nonneg_left
          (ξ.add_le
            (complexMatrixMul A ((U : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n))
            (complexMatrixMul A ((V : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n)))
          (by norm_num)
    _ = ξ.norm A := by
        rw [ξ.right_unitary A U, ξ.right_unitary A V]
        ring

theorem ComplexMatrixFixedUnitaryInvariantNorm.left_mul_le
    {m n : ℕ} (ξ : ComplexMatrixFixedUnitaryInvariantNorm m n)
    (hmid : ComplexSquareContractionMidpointProperty m)
    (L : CMatrix m m) (A : CMatrix m n) :
    ξ.norm (complexMatrixMul L A) <= complexMatrixOp2 L * ξ.norm A := by
  let α : ℝ := complexMatrixOp2 L
  by_cases hα : α = 0
  · have hLzero : L = 0 := complexMatrix_eq_zero_of_op2_eq_zero (A := L) hα
    have hmulzero : complexMatrixMul L A = 0 := by
      rw [hLzero]
      ext i j
      simp [complexMatrixMul]
    calc
      ξ.norm (complexMatrixMul L A) = 0 := by
        rw [hmulzero]
        exact (ξ.eq_zero_iff 0).2 rfl
      _ <= complexMatrixOp2 L * ξ.norm A := by
        rw [show complexMatrixOp2 L = 0 by exact hα]
        simp
  · have hα_nonneg : 0 <= α := complexMatrixOp2_nonneg L
    have hα_pos : 0 < α := lt_of_le_of_ne hα_nonneg (Ne.symm hα)
    let T : CMatrix m m := (((((α : ℂ)⁻¹) •
      (L : Matrix (Fin m) (Fin m) ℂ)) : Matrix (Fin m) (Fin m) ℂ) : CMatrix m m)
    have hnorm_inv : ‖((α : ℂ)⁻¹)‖ = α⁻¹ := by
      simpa [abs_of_nonneg (inv_nonneg.mpr hα_pos.le)]
    have hT_op : complexMatrixOp2 T <= 1 := by
      dsimp [T]
      rw [complexMatrixOp2_smul, hnorm_inv]
      have hmul : α⁻¹ * complexMatrixOp2 L = 1 := by
        dsimp [α]
        exact inv_mul_cancel₀ hα
      rw [hmul]
    have hcontr := ξ.left_contraction_le hmid T A hT_op
    have hscale : complexMatrixMul L A =
        (((α : ℂ) • (complexMatrixMul T A : Matrix (Fin m) (Fin n) ℂ)) :
          Matrix (Fin m) (Fin n) ℂ) := by
      ext i j
      dsimp [T, complexMatrixMul]
      change (∑ k : Fin m, L i k * A k j) =
        (α : ℂ) * ∑ k : Fin m, (((α : ℂ)⁻¹ * L i k) * A k j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      have hunit : (α : ℂ) * (α : ℂ)⁻¹ = 1 := by
        exact mul_inv_cancel₀ (by exact_mod_cast hα)
      symm
      rw [← mul_assoc, ← mul_assoc, hunit, one_mul]
    calc
      ξ.norm (complexMatrixMul L A)
          = ξ.norm ((((α : ℂ) • (complexMatrixMul T A :
              Matrix (Fin m) (Fin n) ℂ)) : Matrix (Fin m) (Fin n) ℂ) :
              CMatrix m n) := by rw [hscale]
      _ = ‖(α : ℂ)‖ * ξ.norm (complexMatrixMul T A) := ξ.smul (α : ℂ) _
      _ <= α * ξ.norm A := by
        have hnormα : ‖(α : ℂ)‖ = α := by
          simp [abs_of_nonneg hα_pos.le]
        rw [hnormα]
        exact mul_le_mul_of_nonneg_left hcontr hα_pos.le
      _ = complexMatrixOp2 L * ξ.norm A := rfl

theorem ComplexMatrixFixedUnitaryInvariantNorm.right_mul_le
    {m n : ℕ} (ξ : ComplexMatrixFixedUnitaryInvariantNorm m n)
    (hmid : ComplexSquareContractionMidpointProperty n)
    (A : CMatrix m n) (R : CMatrix n n) :
    ξ.norm (complexMatrixMul A R) <= ξ.norm A * complexMatrixOp2 R := by
  let α : ℝ := complexMatrixOp2 R
  by_cases hα : α = 0
  · have hRzero : R = 0 := complexMatrix_eq_zero_of_op2_eq_zero (A := R) hα
    have hmulzero : complexMatrixMul A R = 0 := by
      rw [hRzero]
      ext i j
      simp [complexMatrixMul]
    calc
      ξ.norm (complexMatrixMul A R) = 0 := by
        rw [hmulzero]
        exact (ξ.eq_zero_iff 0).2 rfl
      _ <= ξ.norm A * complexMatrixOp2 R := by
        rw [show complexMatrixOp2 R = 0 by exact hα]
        simp
  · have hα_nonneg : 0 <= α := complexMatrixOp2_nonneg R
    have hα_pos : 0 < α := lt_of_le_of_ne hα_nonneg (Ne.symm hα)
    let T : CMatrix n n := (((((α : ℂ)⁻¹) •
      (R : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) : CMatrix n n)
    have hnorm_inv : ‖((α : ℂ)⁻¹)‖ = α⁻¹ := by
      simpa [abs_of_nonneg (inv_nonneg.mpr hα_pos.le)]
    have hT_op : complexMatrixOp2 T <= 1 := by
      dsimp [T]
      rw [complexMatrixOp2_smul, hnorm_inv]
      have hmul : α⁻¹ * complexMatrixOp2 R = 1 := by
        dsimp [α]
        exact inv_mul_cancel₀ hα
      rw [hmul]
    have hcontr := ξ.right_contraction_le hmid A T hT_op
    have hscale : complexMatrixMul A R =
        (((α : ℂ) • (complexMatrixMul A T : Matrix (Fin m) (Fin n) ℂ)) :
          Matrix (Fin m) (Fin n) ℂ) := by
      ext i j
      dsimp [T, complexMatrixMul]
      change (∑ k : Fin n, A i k * R k j) =
        (α : ℂ) * ∑ k : Fin n, A i k * (((α : ℂ)⁻¹ * R k j))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      have hunit : (α : ℂ) * (α : ℂ)⁻¹ = 1 := by
        exact mul_inv_cancel₀ (by exact_mod_cast hα)
      symm
      calc
        (α : ℂ) * (A i k * ((α : ℂ)⁻¹ * R k j))
            = A i k * (((α : ℂ) * (α : ℂ)⁻¹) * R k j) := by ring
        _ = A i k * R k j := by rw [hunit, one_mul]
    calc
      ξ.norm (complexMatrixMul A R)
          = ξ.norm ((((α : ℂ) • (complexMatrixMul A T :
              Matrix (Fin m) (Fin n) ℂ)) : Matrix (Fin m) (Fin n) ℂ) :
              CMatrix m n) := by rw [hscale]
      _ = ‖(α : ℂ)‖ * ξ.norm (complexMatrixMul A T) := ξ.smul (α : ℂ) _
      _ <= α * ξ.norm A := by
        have hnormα : ‖(α : ℂ)‖ = α := by
          simp [abs_of_nonneg hα_pos.le]
        rw [hnormα]
        exact mul_le_mul_of_nonneg_left hcontr hα_pos.le
      _ = ξ.norm A * complexMatrixOp2 R := by
        dsimp [α]
        ring

/-- A fixed rectangular complex matrix norm with the two square-multiplier
    operator-ideal product inequalities needed for Higham Problem 6.5:
    `|||L A||| <= ||L||_2 |||A|||` and
    `|||A R||| <= |||A||| ||R||_2`.

    This is the exact fixed-shape surface of the source statement. Deriving
    these fields from bare unitary invariance is a separate foundation, most
    directly by proving that a square contraction is the midpoint of two
    unitaries and then using convexity plus unitary invariance. -/
structure ComplexMatrixFixedOperatorIdealNorm (m n : ℕ) where
  norm : CMatrix m n → ℝ
  norm_nonneg : ∀ (A : CMatrix m n), 0 <= norm A
  left_mul_le : ∀ (L : CMatrix m m) (A : CMatrix m n),
    norm (complexMatrixMul L A) <= complexMatrixOp2 L * norm A
  right_mul_le : ∀ (A : CMatrix m n) (R : CMatrix n n),
    norm (complexMatrixMul A R) <= norm A * complexMatrixOp2 R

/-- A bare fixed-shape unitarily invariant norm becomes a fixed-shape
    operator-ideal norm once the square-contraction midpoint property is
    available in the left and right square dimensions. -/
noncomputable def ComplexMatrixFixedUnitaryInvariantNorm.toOperatorIdealNorm
    {m n : ℕ} (ξ : ComplexMatrixFixedUnitaryInvariantNorm m n)
    (hmid_left : ComplexSquareContractionMidpointProperty m)
    (hmid_right : ComplexSquareContractionMidpointProperty n) :
    ComplexMatrixFixedOperatorIdealNorm m n where
  norm := ξ.norm
  norm_nonneg := ξ.norm_nonneg
  left_mul_le := ξ.left_mul_le hmid_left
  right_mul_le := ξ.right_mul_le hmid_right

/-- The complex Frobenius norm is a concrete fixed-shape operator-ideal norm. -/
noncomputable def complexFrobeniusFixedOperatorIdealNorm (m n : ℕ) :
    ComplexMatrixFixedOperatorIdealNorm m n where
  norm := fun A => complexMatrixFrobenius A
  norm_nonneg := by
    intro A
    exact complexMatrixFrobenius_nonneg A
  left_mul_le := by
    intro L A
    exact complexMatrixFrobenius_mul_le_op2_mul L A
  right_mul_le := by
    intro A R
    exact complexMatrixFrobenius_mul_le_mul_op2 A R

theorem complexFrobeniusFixedOperatorIdealNorm_norm {m n : ℕ}
    (A : CMatrix m n) :
    (complexFrobeniusFixedOperatorIdealNorm m n).norm A =
      complexMatrixFrobenius A :=
  rfl

/-- A dimension-uniform complex matrix norm family with the two operator-ideal
    product inequalities needed for shape-changing versions of Higham Problem
    6.5.

    This interface is intentionally stronger than bare fixed-shape unitary
    invariance: deriving it for a family across dimensions also requires a
    padding or isometric-embedding coherence theorem, which is not hidden in
    this structure. -/
structure ComplexMatrixOperatorIdealNormFamily where
  norm : {m n : ℕ} → CMatrix m n → ℝ
  norm_nonneg : ∀ {m n : ℕ} (A : CMatrix m n), 0 <= norm A
  left_mul_le : ∀ {m n p : ℕ} (L : CMatrix p m) (A : CMatrix m n),
    norm (complexMatrixMul L A) <= complexMatrixOp2 L * norm A
  right_mul_le : ∀ {m n p : ℕ} (A : CMatrix m n) (R : CMatrix n p),
    norm (complexMatrixMul A R) <= norm A * complexMatrixOp2 R

/-- The complex Frobenius norm is a concrete operator-ideal norm family. -/
noncomputable def complexFrobeniusOperatorIdealNormFamily :
    ComplexMatrixOperatorIdealNormFamily where
  norm := fun {m n} A => complexMatrixFrobenius (m := m) (n := n) A
  norm_nonneg := by
    intro m n A
    exact complexMatrixFrobenius_nonneg A
  left_mul_le := by
    intro m n p L A
    exact complexMatrixFrobenius_mul_le_op2_mul L A
  right_mul_le := by
    intro m n p A R
    exact complexMatrixFrobenius_mul_le_mul_op2 A R

theorem complexFrobeniusOperatorIdealNormFamily_norm {m n : ℕ}
    (A : CMatrix m n) :
    complexFrobeniusOperatorIdealNormFamily.norm A = complexMatrixFrobenius A :=
  rfl
end NumStability
