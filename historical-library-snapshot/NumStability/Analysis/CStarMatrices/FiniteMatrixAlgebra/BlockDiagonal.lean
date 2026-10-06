import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.CStarMatrices.FiniteMatrixAlgebra.BlockDiagonal

R07 canonical `reusable` leaf. Declaration-level review groups 21 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.cstarMatrixBlockDiagonal`, `NumStability.cstarMatrixBlockDiagonalStarAlgHom`, `NumStability.cstarMatrixBlockDiagonalStarAlgHom_apply`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped ComplexOrder MatrixOrder

/-- Block diagonal C⋆-matrix over the sum index. -/
def cstarMatrixBlockDiagonal {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  CStarMatrix.ofMatrix
    (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm A) 0 0
      (CStarMatrix.ofMatrix.symm B))

@[simp]
theorem cstarMatrixBlockDiagonal_inl_inl {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inl i) (Sum.inl j) = A i j := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_inl_inr {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inl i) (Sum.inr j) = 0 := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_inr_inl {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inr i) (Sum.inl j) = 0 := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_inr_inr {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) (i j : ι) :
    cstarMatrixBlockDiagonal A B (Sum.inr i) (Sum.inr j) = B i j := by
  rfl

@[simp]
theorem cstarMatrixBlockDiagonal_zero_zero {ι : Type*} :
    cstarMatrixBlockDiagonal
        (0 : CStarMatrix ι ι ℂ) (0 : CStarMatrix ι ι ℂ) = 0 := by
  ext r c
  cases r <;> cases c <;> simp

@[simp]
theorem cstarMatrixBlockDiagonal_one_one {ι : Type*} [DecidableEq ι] :
    cstarMatrixBlockDiagonal
        (1 : CStarMatrix ι ι ℂ) (1 : CStarMatrix ι ι ℂ) = 1 := by
  ext r c
  cases r <;> cases c <;> simp [CStarMatrix.one_apply]

theorem cstarMatrixBlockDiagonal_add {ι : Type*}
    (A B C D : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal (A + C) (B + D) =
      cstarMatrixBlockDiagonal A B + cstarMatrixBlockDiagonal C D := by
  ext r c
  cases r <;> cases c <;> simp

theorem cstarMatrixBlockDiagonal_neg {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal (-A) (-B) =
      -cstarMatrixBlockDiagonal A B := by
  ext r c
  cases r <;> cases c <;> simp

theorem cstarMatrixBlockDiagonal_sub {ι : Type*}
    (A B C D : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal (A - C) (B - D) =
      cstarMatrixBlockDiagonal A B - cstarMatrixBlockDiagonal C D := by
  ext r c
  cases r <;> cases c <;> simp

theorem cstarMatrixBlockDiagonal_star {ι : Type*}
    (A B : CStarMatrix ι ι ℂ) :
    star (cstarMatrixBlockDiagonal A B) =
      cstarMatrixBlockDiagonal (star A) (star B) := by
  ext r c
  cases r <;> cases c <;> simp [CStarMatrix.star_apply]

theorem cstarMatrixBlockDiagonal_isSelfAdjoint {ι : Type*}
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (cstarMatrixBlockDiagonal A B) := by
  rw [isSelfAdjoint_iff] at hA hB ⊢
  rw [cstarMatrixBlockDiagonal_star, hA, hB]

theorem cstarMatrixBlockDiagonal_mul {ι : Type*} [Fintype ι]
    (A B C D : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonal A B * cstarMatrixBlockDiagonal C D =
      cstarMatrixBlockDiagonal (A * C) (B * D) := by
  ext r c
  cases r <;> cases c <;>
    simp [CStarMatrix.mul_apply, Fintype.sum_sum_type]

theorem cstarMatrixBlockDiagonal_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (cstarMatrixBlockDiagonal A B) := by
  rw [isUnit_iff_exists] at hA hB ⊢
  rcases hA with ⟨Ainv, hA1, hA2⟩
  rcases hB with ⟨Binv, hB1, hB2⟩
  refine ⟨cstarMatrixBlockDiagonal Ainv Binv, ?_, ?_⟩
  · calc
      cstarMatrixBlockDiagonal A B * cstarMatrixBlockDiagonal Ainv Binv =
          cstarMatrixBlockDiagonal (A * Ainv) (B * Binv) :=
        cstarMatrixBlockDiagonal_mul A B Ainv Binv
      _ = cstarMatrixBlockDiagonal 1 1 := by
        ext r c
        cases r with
        | inl i =>
            cases c with
            | inl j => simpa using congr_fun (congr_fun hA1 i) j
            | inr j => simp
        | inr i =>
            cases c with
            | inl j => simp
            | inr j => simpa using congr_fun (congr_fun hB1 i) j
      _ = 1 := cstarMatrixBlockDiagonal_one_one
  · calc
      cstarMatrixBlockDiagonal Ainv Binv * cstarMatrixBlockDiagonal A B =
          cstarMatrixBlockDiagonal (Ainv * A) (Binv * B) :=
        cstarMatrixBlockDiagonal_mul Ainv Binv A B
      _ = cstarMatrixBlockDiagonal 1 1 := by
        ext r c
        cases r with
        | inl i =>
            cases c with
            | inl j => simpa using congr_fun (congr_fun hA2 i) j
            | inr j => simp
        | inr i =>
            cases c with
            | inl j => simp
            | inr j => simpa using congr_fun (congr_fun hB2 i) j
      _ = 1 := cstarMatrixBlockDiagonal_one_one

theorem cstarMatrixBlockDiagonal_left_nonneg {ι : Type*} [Fintype ι]
    {A : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) :
    0 ≤ cstarMatrixBlockDiagonal A (0 : CStarMatrix ι ι ℂ) := by
  rw [StarOrderedRing.nonneg_iff] at hA ⊢
  refine AddSubmonoid.closure_induction
    (s := Set.range fun S : CStarMatrix ι ι ℂ => star S * S)
    (motive := fun X _ =>
      cstarMatrixBlockDiagonal X (0 : CStarMatrix ι ι ℂ) ∈
        AddSubmonoid.closure
          (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
    ?mem ?zero ?add hA
  · intro X hX
    rcases hX with ⟨S, rfl⟩
    apply AddSubmonoid.subset_closure
    refine ⟨cstarMatrixBlockDiagonal S (0 : CStarMatrix ι ι ℂ), ?_⟩
    simp [cstarMatrixBlockDiagonal_star, cstarMatrixBlockDiagonal_mul]
  · simp
  · intro X Y _ _ hX hY
    have hEq :
        cstarMatrixBlockDiagonal (X + Y) (0 : CStarMatrix ι ι ℂ) =
          cstarMatrixBlockDiagonal X (0 : CStarMatrix ι ι ℂ) +
            cstarMatrixBlockDiagonal Y (0 : CStarMatrix ι ι ℂ) := by
      simpa using
        (cstarMatrixBlockDiagonal_add X (0 : CStarMatrix ι ι ℂ) Y
          (0 : CStarMatrix ι ι ℂ))
    rw [hEq]
    exact AddSubmonoid.add_mem
      (AddSubmonoid.closure
        (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
      hX hY

theorem cstarMatrixBlockDiagonal_right_nonneg {ι : Type*} [Fintype ι]
    {B : CStarMatrix ι ι ℂ} (hB : 0 ≤ B) :
    0 ≤ cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) B := by
  rw [StarOrderedRing.nonneg_iff] at hB ⊢
  refine AddSubmonoid.closure_induction
    (s := Set.range fun S : CStarMatrix ι ι ℂ => star S * S)
    (motive := fun X _ =>
      cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) X ∈
        AddSubmonoid.closure
          (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
    ?mem ?zero ?add hB
  · intro X hX
    rcases hX with ⟨S, rfl⟩
    apply AddSubmonoid.subset_closure
    refine ⟨cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) S, ?_⟩
    simp [cstarMatrixBlockDiagonal_star, cstarMatrixBlockDiagonal_mul]
  · simp
  · intro X Y _ _ hX hY
    have hEq :
        cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) (X + Y) =
          cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) X +
            cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) Y := by
      simpa using
        (cstarMatrixBlockDiagonal_add (0 : CStarMatrix ι ι ℂ) X
          (0 : CStarMatrix ι ι ℂ) Y)
    rw [hEq]
    exact AddSubmonoid.add_mem
      (AddSubmonoid.closure
        (Set.range fun S : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ => star S * S))
      hX hY

theorem cstarMatrixBlockDiagonal_nonneg {ι : Type*} [Fintype ι]
    {A B : CStarMatrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ cstarMatrixBlockDiagonal A B := by
  have hsum :
      0 ≤ cstarMatrixBlockDiagonal A (0 : CStarMatrix ι ι ℂ) +
        cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) B :=
    add_nonneg (cstarMatrixBlockDiagonal_left_nonneg hA)
      (cstarMatrixBlockDiagonal_right_nonneg hB)
  have hEq :
      cstarMatrixBlockDiagonal A B =
        cstarMatrixBlockDiagonal A (0 : CStarMatrix ι ι ℂ) +
          cstarMatrixBlockDiagonal (0 : CStarMatrix ι ι ℂ) B := by
    simpa using
      (cstarMatrixBlockDiagonal_add A (0 : CStarMatrix ι ι ℂ)
        (0 : CStarMatrix ι ι ℂ) B)
  rwa [hEq]

theorem cstarMatrixBlockDiagonal_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CStarMatrix ι ι ℂ}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (cstarMatrixBlockDiagonal A B) :=
  (cstarMatrixBlockDiagonal_isUnit hA.isUnit hB.isUnit).isStrictlyPositive
    (cstarMatrixBlockDiagonal_nonneg hA.nonneg hB.nonneg)

/-- Block diagonal embedding as a real star-algebra homomorphism from a pair of
finite C⋆-matrices into the doubled-index finite C⋆-matrix algebra. -/
noncomputable def cstarMatrixBlockDiagonalStarAlgHom
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) →⋆ₐ[ℝ]
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun p := cstarMatrixBlockDiagonal p.1 p.2
  map_zero' := cstarMatrixBlockDiagonal_zero_zero
  map_one' := cstarMatrixBlockDiagonal_one_one
  map_add' p q := cstarMatrixBlockDiagonal_add p.1 p.2 q.1 q.2
  map_mul' p q := by
    simpa using (cstarMatrixBlockDiagonal_mul p.1 p.2 q.1 q.2).symm
  commutes' r := by
    ext row col
    cases row <;> cases col <;>
      simp [Algebra.algebraMap_eq_smul_one, CStarMatrix.one_apply]
  map_star' p := (cstarMatrixBlockDiagonal_star p.1 p.2).symm

@[simp]
theorem cstarMatrixBlockDiagonalStarAlgHom_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) :
    cstarMatrixBlockDiagonalStarAlgHom ι (A, B) =
      cstarMatrixBlockDiagonal A B := rfl

/-- The block diagonal star-algebra homomorphism is continuous. -/
theorem cstarMatrixBlockDiagonalStarAlgHom_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous
      (cstarMatrixBlockDiagonalStarAlgHom ι :
        CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ →
          CStarMatrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  have hmat :
      Continuous
        (fun p : CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ =>
          (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p.1) 0 0
            (CStarMatrix.ofMatrix.symm p.2) :
            Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)) := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro col
    cases row with
    | inl i =>
        cases col with
        | inl j =>
            simpa using
              ((continuous_apply j).comp
                ((continuous_apply i).comp continuous_fst))
        | inr j => exact continuous_const
    | inr i =>
        cases col with
        | inl j => exact continuous_const
        | inr j =>
            simpa using
              ((continuous_apply j).comp
                ((continuous_apply i).comp continuous_snd))
  simpa [cstarMatrixBlockDiagonalStarAlgHom, cstarMatrixBlockDiagonal] using
    ((CStarMatrix.ofMatrixL
      (m := ι ⊕ ι) (n := ι ⊕ ι) (A := ℂ)).continuous.comp hmat)

end NumStability
