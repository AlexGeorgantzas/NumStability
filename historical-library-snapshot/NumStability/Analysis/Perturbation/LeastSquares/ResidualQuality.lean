import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Basic

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# ResidualQuality

Canonical reusable module extracted without change from Higham20ResidualQuality.
-/

/-- The residual of a supplied vector for the original least-squares data. -/
noncomputable def higham20ConventionalResidual {m n : Nat}
    (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (xhat : Fin n → Real) : Fin m → Real :=
  fun i => b i - rectMatMulVec A xhat i
/-- The first-order absolute majorant in the post-Theorem-20.3 residual
estimate:

`|AA^+| (f + E|x|) + |A^+|^T E^T |r|`.
-/
noncomputable def higham20PostQRResidualFirstOrderMajorant {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (E : Fin m → Fin n → Real) (f r : Fin m → Real)
    (x : Fin n → Real) : Fin m → Real :=
  fun i =>
    rectMatMulVec (absMatrixRect (rectMatMul A Aplus))
        (lsComponentwiseDataMajorant E f x) i +
      ∑ j : Fin n, |Aplus j i| * lsComponentwiseTransposeMajorant E r j
/-- The first-order majorant embedded in the combined residual/solution
space.  The lower block is zero because the target is only the conventional
residual. -/
noncomputable def higham20PostQRResidualFirstOrderVector {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (E : Fin m → Fin n → Real) (f r : Fin m → Real)
    (x : Fin n → Real) : Fin (m + n) → Real :=
  Fin.append (higham20PostQRResidualFirstOrderMajorant A Aplus E f r x)
    (fun _ : Fin n => 0)
/-- The exact nonnegative matrix multiplying
`[|rhat-r|; |xhat-x|]` in the quadratic residual correction.

Its upper-left block is `|A^+|^T E^T`, its upper-right block is
`|AA^+| E`, and its lower block is zero. -/
noncomputable def higham20PostQRResidualCorrectionMatrix {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    (E : Fin m → Fin n → Real) :
    Fin (m + n) → Fin (m + n) → Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append
        (fun k : Fin m => ∑ j : Fin n, |Aplus j i| * E k j)
        (fun l : Fin n =>
          ∑ k : Fin m, |rectMatMul A Aplus i k| * E k l))
    (fun _ : Fin n => fun _ : Fin (m + n) => 0)
/-- The conventional residual error embedded in the combined space. -/
noncomputable def higham20PostQRConventionalResidualError {m n : Nat}
    (A : Fin m → Fin n → Real) (b r : Fin m → Real)
    (xhat : Fin n → Real) : Fin (m + n) → Real :=
  Fin.append (fun i => higham20ConventionalResidual A b xhat i - r i)
    (fun _ : Fin n => 0)
theorem higham20PostQRResidualCorrectionMatrix_nonneg {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    {E : Fin m → Fin n → Real} (hE : ∀ i j, 0 ≤ E i j) :
    ∀ i j, 0 ≤ higham20PostQRResidualCorrectionMatrix A Aplus E i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simp only [higham20PostQRResidualCorrectionMatrix, Fin.append_left]
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg (Aplus k ii)) (hE jj k))
    · simp only [higham20PostQRResidualCorrectionMatrix, Fin.append_left,
        Fin.append_right]
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg (rectMatMul A Aplus ii k)) (hE k jj))
  · intro ii j
    simp [higham20PostQRResidualCorrectionMatrix]
theorem higham20PostQRResidualFirstOrderVector_nonneg {m n : Nat}
    (A : Fin m → Fin n → Real) (Aplus : Fin n → Fin m → Real)
    {E : Fin m → Fin n → Real} {f r : Fin m → Real}
    (x : Fin n → Real) (hE : ∀ i j, 0 ≤ E i j)
    (hf : ∀ i, 0 ≤ f i) :
    ∀ k, 0 ≤ higham20PostQRResidualFirstOrderVector A Aplus E f r x k := by
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [higham20PostQRResidualFirstOrderVector, Fin.append_left,
      higham20PostQRResidualFirstOrderMajorant]
    apply add_nonneg
    · unfold rectMatMulVec absMatrixRect
      exact Finset.sum_nonneg (fun t _ => mul_nonneg
        (abs_nonneg (rectMatMul A Aplus i t)) (by
          unfold lsComponentwiseDataMajorant rectMatMulVec absVec
          exact add_nonneg (hf t) (Finset.sum_nonneg (fun j _ =>
            mul_nonneg (hE t j) (abs_nonneg (x j))))))
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg
        (abs_nonneg (Aplus j i)) (by
          unfold lsComponentwiseTransposeMajorant
          exact Finset.sum_nonneg (fun t _ =>
            mul_nonneg (hE t j) (abs_nonneg (r t)))))
  · intro j
    simp [higham20PostQRResidualFirstOrderVector]
/-- A row-repeated column-2-norm majorant for a QR matrix perturbation.  It
is pointwise no larger than the source's `e e^T |A|` majorant. -/
noncomputable def higham20QRColumnNormMajorant {m n : Nat}
    (A : Fin m → Fin n → Real) : Fin m → Fin n → Real :=
  fun _ j => vecNorm2 (fun i : Fin m => A i j)
/-- A row-repeated 2-norm majorant for the QR right-hand-side perturbation. -/
noncomputable def higham20QRRhsNormMajorant {m : Nat}
    (b : Fin m → Real) : Fin m → Real :=
  fun _ => vecNorm2 b
/-- Columnwise and RHS 2-norm bounds imply the componentwise perturbation
model needed by the finite residual-quality theorem. -/
theorem higham20_qr_norm_bounds_to_componentwise
    {m n : Nat} (A DeltaA : Fin m → Fin n → Real)
    (b Deltab : Fin m → Real) (eps : Real)
    (heps : 0 ≤ eps)
    (hA : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m => DeltaA i j) ≤
        eps * vecNorm2 (fun i : Fin m => A i j))
    (hb : vecNorm2 Deltab ≤ eps * vecNorm2 b) :
    LSComponentwisePerturbation DeltaA (higham20QRColumnNormMajorant A)
      Deltab (higham20QRRhsNormMajorant b) eps := by
  refine ⟨heps, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact vecNorm2_nonneg _
  · intro i
    exact vecNorm2_nonneg _
  · intro i j
    exact (abs_coord_le_vecNorm2 (fun k : Fin m => DeltaA k j) i).trans (hA j)
  · intro i
    exact (abs_coord_le_vecNorm2 Deltab i).trans hb

end NumStability
