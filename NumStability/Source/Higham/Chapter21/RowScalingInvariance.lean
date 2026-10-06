import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve

/-!
# Higham Chapter 21: row-scaling invariance

Row-scaling invariance of the condition measure following equation (21.8) in
Higham's *Accuracy and Stability of Numerical Algorithms*, second edition.
-/

namespace NumStability

/-- Left row scaling by a diagonal with entries `d`. -/
def higham21RowScale {m n : Nat} (d : Fin m -> Real)
    (A : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun i j => d i * A i j

/-- Pseudoinverse transformation paired with `higham21RowScale` for a
    nonsingular diagonal row scaling. -/
noncomputable def higham21RowScaledAplus {m n : Nat} (d : Fin m -> Real)
    (Aplus : Fin n -> Fin m -> Real) : Fin n -> Fin m -> Real :=
  fun j i => Aplus j i / d i

/-- Diagonal row scaling and inverse column scaling leave the domain
    projection `Aplus * A` unchanged. -/
theorem higham21_rowScaled_domain_projection
    {m n : Nat} (d : Fin m -> Real)
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (hd : forall i, d i ≠ 0) :
    rectMatMul (higham21RowScaledAplus d Aplus) (higham21RowScale d A) =
      rectMatMul Aplus A := by
  ext j k
  unfold rectMatMul higham21RowScaledAplus higham21RowScale
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hd i]

/-- A right inverse remains a right inverse after a nonsingular diagonal row
    scaling and the corresponding inverse scaling of the pseudoinverse. -/
theorem higham21_rowScaled_right_inverse
    {m n : Nat} (d : Fin m -> Real)
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (hd : forall i, d i ≠ 0)
    (hRight : rectMatMul A Aplus = idMatrix m) :
    rectMatMul (higham21RowScale d A) (higham21RowScaledAplus d Aplus) =
      idMatrix m := by
  ext i r
  have hentry :
      (Finset.univ.sum fun j : Fin n => A i j * Aplus j r) =
        idMatrix m i r := by
    simpa only [rectMatMul] using congrFun (congrFun hRight i) r
  unfold rectMatMul higham21RowScale higham21RowScaledAplus
  calc
    (Finset.univ.sum fun j : Fin n =>
        d i * A i j * (Aplus j r / d r)) =
        (d i / d r) *
          Finset.univ.sum (fun j : Fin n => A i j * Aplus j r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          field_simp [hd r]
    _ = (d i / d r) * idMatrix m i r := by rw [hentry]
    _ = idMatrix m i r := by
      by_cases hir : i = r
      · subst r
        simp [idMatrix, hd i]
      · simp [idMatrix, hir]

/-- The transformed table is the Moore--Penrose pseudoinverse of the
    row-scaled matrix whenever the original full-row-rank table has the usual
    right-inverse and symmetric-domain-projection certificates. -/
theorem higham21_rowScaled_moorePenrose
    {m n : Nat} (d : Fin m -> Real)
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (hd : forall i, d i ≠ 0)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hDomain : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    RectMoorePenrosePseudoinverse m n
      (higham21RowScale d A) (higham21RowScaledAplus d Aplus) := by
  apply rectMoorePenrosePseudoinverse_of_right_inverse_and_domain_symmetric
  · exact higham21_rowScaled_right_inverse d A Aplus hd hRight
  · rw [higham21_rowScaled_domain_projection d A Aplus hd]
    exact hDomain

/-- Higham, 2nd ed., Chapter 21, equation (21.8), precise prose following the
    display: the row-scaled condition measure
    `cond2(A) = || |Aplus| |A| ||_2` is invariant under nonsingular diagonal
    row scaling, with the correspondingly transformed pseudoinverse. -/
theorem higham21Cond2With_row_scaling
    {m n : Nat} (d : Fin m -> Real)
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (hd : forall i, d i ≠ 0) :
    higham21Cond2With (higham21RowScale d A)
        (higham21RowScaledAplus d Aplus) =
      higham21Cond2With A Aplus := by
  unfold higham21Cond2With
  congr 1
  apply congrArg realRectToCMatrix
  ext j k
  unfold rectMatMul absMatrixRect higham21RowScale higham21RowScaledAplus
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_div, abs_mul]
  field_simp [abs_ne_zero.mpr (hd i)]

end NumStability
