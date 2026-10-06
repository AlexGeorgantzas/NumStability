import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# Projection

Canonical reusable module extracted without change from Higham20Lemma20_12.
-/

/-- Penrose equation `A Aplus A = A` identifies the range of the range
projection `A Aplus` with the range of `A`; its finite dimension is therefore
the matrix rank of `A`.

This is the rank bridge needed to apply the abstract equal-projection-rank
principal-angle theorem to arbitrary-rank rectangular matrices. -/
theorem higham20_lemma20_12_rangeProjection_finrank_eq_matrixRank
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (hPenrose1 : rectMatMul (rectMatMul A Aplus) A = A) :
    Module.finrank Real
        (LinearMap.range
          ((Matrix.of (rectMatMul A Aplus) :
            Matrix (Fin m) (Fin m) Real).mulVecLin)) =
      (Matrix.of A).rank := by
  let AM : Matrix (Fin m) (Fin n) Real := Matrix.of A
  let AplusM : Matrix (Fin n) (Fin m) Real := Matrix.of Aplus
  let PM : Matrix (Fin m) (Fin m) Real := Matrix.of (rectMatMul A Aplus)
  let TA : (Fin n -> Real) →ₗ[Real] (Fin m -> Real) := AM.mulVecLin
  let TAplus : (Fin m -> Real) →ₗ[Real] (Fin n -> Real) := AplusM.mulVecLin
  let TP : (Fin m -> Real) →ₗ[Real] (Fin m -> Real) := PM.mulVecLin
  have hTA_rect (x : Fin n -> Real) : TA x = rectMatMulVec A x := by
    ext i
    simp [TA, AM, Matrix.mulVec, dotProduct, rectMatMulVec]
  have hTAplus_rect (x : Fin m -> Real) :
      TAplus x = rectMatMulVec Aplus x := by
    ext i
    simp [TAplus, AplusM, Matrix.mulVec, dotProduct, rectMatMulVec]
  have hTP_rect (x : Fin m -> Real) :
      TP x = rectMatMulVec (rectMatMul A Aplus) x := by
    ext i
    simp [TP, PM, Matrix.mulVec, dotProduct, rectMatMulVec, rectMatMul]
  have hRange : LinearMap.range TP = LinearMap.range TA := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      refine ⟨TAplus x, ?_⟩
      calc
        TA (TAplus x) =
            rectMatMulVec A (rectMatMulVec Aplus x) := by
              rw [hTA_rect, hTAplus_rect]
        _ = rectMatMulVec (rectMatMul A Aplus) x := by
              exact (rectMatMulVec_rectMatMul A Aplus x).symm
        _ = TP x := (hTP_rect x).symm
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      refine ⟨TA z, ?_⟩
      calc
        TP (TA z) =
            rectMatMulVec (rectMatMul A Aplus) (rectMatMulVec A z) := by
              rw [hTP_rect, hTA_rect]
        _ = rectMatMulVec (rectMatMul (rectMatMul A Aplus) A) z := by
              exact
                (rectMatMulVec_rectMatMul (rectMatMul A Aplus) A z).symm
        _ = rectMatMulVec A z := by rw [hPenrose1]
        _ = TA z := (hTA_rect z).symm
  calc
    Module.finrank Real (LinearMap.range TP) =
        Module.finrank Real (LinearMap.range TA) := by rw [hRange]
    _ = AM.rank := by rfl
    _ = (Matrix.of A).rank := by rfl

end NumStability
