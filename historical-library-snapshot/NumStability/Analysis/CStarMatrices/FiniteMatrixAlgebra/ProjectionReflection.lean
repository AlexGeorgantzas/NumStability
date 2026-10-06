import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.ProjectionReflection

R07 canonical `reusable` leaf. Declaration-level review groups 7 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixProjectionReflection`, `NumStability.cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint`, `NumStability.cstarMatrixProjectionReflection_isUnit_of_idempotent`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- The reflection `2P - I` associated to a square C⋆-matrix `P`.  For an
idempotent self-adjoint `P`, this is the usual symmetry across the range of
`P`; it is the algebraic reflection used in block pinching arguments. -/
noncomputable def cstarMatrixProjectionReflection
    {ι : Type*} [DecidableEq ι] (P : CStarMatrix ι ι ℂ) :
    CStarMatrix ι ι ℂ :=
  (2 : ℂ) • P - 1

/-- If `P` is self-adjoint, then its reflection `2P - I` is self-adjoint. -/
theorem cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (cstarMatrixProjectionReflection P) := by
  rw [isSelfAdjoint_iff] at hP ⊢
  ext i j
  have hPij := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hP
  simp [cstarMatrixProjectionReflection, CStarMatrix.star_apply] at hPij ⊢
  rw [hPij]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

/-- If `P` is idempotent, then the reflection `2P - I` squares to the
identity. -/
theorem cstarMatrixProjectionReflection_mul_self_of_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hP : P * P = P) :
    cstarMatrixProjectionReflection P * cstarMatrixProjectionReflection P =
      (1 : CStarMatrix ι ι ℂ) := by
  ext i j
  have hPij := congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hP
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply] at hPij ⊢
  simp [mul_sub, sub_mul, Finset.sum_sub_distrib] at hPij ⊢
  have hdouble :
      (∑ x, 2 * P i x * (2 * P x j)) =
        4 * ∑ x, P i x * P x j := by
    calc
      (∑ x, 2 * P i x * (2 * P x j))
          = ∑ x, 4 * (P i x * P x j) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 4 * ∑ x, P i x * P x j := by
            rw [Finset.mul_sum]
  rw [hdouble, hPij]
  by_cases hij : i = j
  · subst hij
    ring
  · simp [hij]
    ring

/-- If `P` is idempotent, then the reflection `2P - I` is a unit with itself
as inverse. -/
theorem cstarMatrixProjectionReflection_isUnit_of_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hP : P * P = P) :
    IsUnit (cstarMatrixProjectionReflection P) := by
  have hsq := cstarMatrixProjectionReflection_mul_self_of_idempotent P hP
  refine isUnit_iff_exists.mpr
    ⟨cstarMatrixProjectionReflection P, ?_⟩
  exact ⟨hsq, hsq⟩

/-- If `P` is self-adjoint and idempotent, then the reflection `2P - I` is
unitary in the star-monoid sense. -/
theorem cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : CStarMatrix ι ι ℂ) (hself : IsSelfAdjoint P) (hid : P * P = P) :
    cstarMatrixProjectionReflection P ∈
      unitary (CStarMatrix ι ι ℂ) := by
  have hRself :
      IsSelfAdjoint (cstarMatrixProjectionReflection P) :=
    cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint P hself
  have hstar :
      star (cstarMatrixProjectionReflection P) =
        cstarMatrixProjectionReflection P := by
    simpa [isSelfAdjoint_iff] using hRself
  have hsq := cstarMatrixProjectionReflection_mul_self_of_idempotent P hid
  rw [Unitary.mem_iff]
  constructor
  · calc
      star (cstarMatrixProjectionReflection P) *
          cstarMatrixProjectionReflection P =
          cstarMatrixProjectionReflection P *
            cstarMatrixProjectionReflection P := by
            rw [hstar]
      _ = 1 := hsq
  · calc
      cstarMatrixProjectionReflection P *
          star (cstarMatrixProjectionReflection P) =
          cstarMatrixProjectionReflection P *
            cstarMatrixProjectionReflection P := by
            rw [hstar]
      _ = 1 := hsq

/-- If `P` fixes a rectangular matrix `V`, then the reflection `2P - I`
also fixes `V`. -/
theorem cstarMatrixProjectionReflection_mul_of_mul_eq_self
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (P : CStarMatrix α α ℂ) (V : CStarMatrix α β ℂ)
    (hPV : P * V = V) :
    cstarMatrixProjectionReflection P * V = V := by
  ext i j
  have hPVij := congrArg (fun M : CStarMatrix α β ℂ => M i j) hPV
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply, sub_mul, Finset.sum_sub_distrib] at hPVij ⊢
  have hdouble :
      (∑ x, 2 * P i x * V x j) =
        2 * ∑ x, P i x * V x j := by
    calc
      (∑ x, 2 * P i x * V x j)
          = ∑ x, 2 * (P i x * V x j) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 2 * ∑ x, P i x * V x j := by
            rw [Finset.mul_sum]
  rw [hdouble, hPVij]
  ring

/-- If a rectangular matrix `W` is fixed by right multiplication by `P`, then
it is also fixed by right multiplication by the reflection `2P - I`. -/
theorem cstarMatrix_mul_projectionReflection_of_mul_eq_self
    {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (W : CStarMatrix α β ℂ) (P : CStarMatrix β β ℂ)
    (hWP : W * P = W) :
    W * cstarMatrixProjectionReflection P = W := by
  ext i j
  have hWPij := congrArg (fun M : CStarMatrix α β ℂ => M i j) hWP
  simp [cstarMatrixProjectionReflection, CStarMatrix.mul_apply,
    CStarMatrix.one_apply, mul_sub, Finset.sum_sub_distrib] at hWPij ⊢
  have hdouble :
      (∑ x, W i x * (2 * P x j)) =
        2 * ∑ x, W i x * P x j := by
    calc
      (∑ x, W i x * (2 * P x j))
          = ∑ x, 2 * (W i x * P x j) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 2 * ∑ x, W i x * P x j := by
            rw [Finset.mul_sum]
  rw [hdouble, hWPij]
  ring

end NumStability
