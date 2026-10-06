import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.Underdetermined.Projectors.ComplementNorm.ProjectorNorm
import NumStability.Source.Higham.Chapter21.Equation08.ProjectorNorm
import NumStability.Source.Higham.Chapter21.Equation08.Results.Core
import NumStability.Source.Higham.Chapter21.Equation09.ProjectorNorm
import NumStability.Source.Higham.Chapter21.Equation09.Results.Core
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Conditioning

Canonical reusable module extracted without change from Higham20Prose.
-/

/-- Higham, 2nd ed., Chapter 20, printed page 383:

    `||I - A A⁺||₂ = min {1, m - n}`

for a full-column `m`-by-`n` matrix.  The left side is stated in the
repository's exact complexified Euclidean operator-norm API.  Full column rank
is exposed by the left-inverse identity `A⁺ A = I`; the supplied
Moore--Penrose certificate provides symmetry of the range projection `A A⁺`.

The proof applies the exact complementary-domain-projector theorem to the
transposed interface `(A⁺, A)`.  It therefore includes both source branches:
the norm is zero when `m = n`, and it is one when `n < m`. -/
theorem higham20_fullColumn_range_projector_complement_complexMatrixOp2_eq_min_one_sub
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hnm : n <= m)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) :
    complexMatrixOp2
        (realRectToCMatrix
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) =
      ((Nat.min 1 (m - n) : Nat) : Real) := by
  exact higham21_projector_complement_complexMatrixOp2_eq_min_one_sub
    Aplus A hnm hleft hMP.range_projection_symmetric

/-! ## The componentwise condition number `cond₂` -/
/-- A left-null vector whose pairing with the residual is nonzero makes the
Rayleigh quotient of the Theorem 20.5 eigenmatrix strictly negative whenever
`mu` and `||y||` are nonzero.  Consequently the printed least eigenvalue
`lambda_*` is negative. -/
theorem higham20_lambdaStar_neg_of_leftNull_residual_pairing {m n : Nat}
    (theta : Real) (A : Fin (m + 1) -> Fin n -> Real)
    (r z : Fin (m + 1) -> Real) (y : Fin n -> Real)
    (hmu : lsNormwiseBackwardErrorMu theta y ≠ 0)
    (hy : y ≠ 0)
    (hleftNull : forall j : Fin n, (∑ i : Fin (m + 1), A i j * z i) = 0)
    (hpair : (∑ i : Fin (m + 1), r i * z i) ≠ 0) :
    lsNormwiseBackwardErrorLambdaStar theta A r y < 0 := by
  let M := lsNormwiseBackwardErrorEigenMatrix theta A r y
  have hmu_pos : 0 < lsNormwiseBackwardErrorMu theta y :=
    lt_of_le_of_ne (lsNormwiseBackwardErrorMu_nonneg theta y) (Ne.symm hmu)
  have hysq_pos : 0 < vecNorm2Sq y := by
    rw [← vecNorm2_sq y]
    exact sq_pos_of_ne_zero (fun h => hy (funext ((vecNorm2_eq_zero_iff y).mp h)))
  have hgram :
      finiteQuadraticForm
          (fun i k : Fin (m + 1) => ∑ j : Fin n, A i j * A k j) z = 0 := by
    rw [finiteQuadraticForm_rowGram_transpose_eq_vecNorm2Sq_rectMatMulVec_finiteTranspose]
    have hz : rectMatMulVec (finiteTranspose A) z = 0 := by
      funext j
      simpa [rectMatMulVec, finiteTranspose, mul_comm] using hleftNull j
    rw [hz]
    simp [vecNorm2Sq]
  have houter :
      finiteQuadraticForm (fun i k : Fin (m + 1) => r i * r k) z =
        (∑ i : Fin (m + 1), r i * z i) ^ 2 := by
    unfold finiteQuadraticForm finiteMatVec
    calc
      (∑ i : Fin (m + 1), z i *
          (∑ j : Fin (m + 1), r i * r j * z j)) =
          ∑ i : Fin (m + 1),
            (z i * r i) * (∑ j : Fin (m + 1), r j * z j) := by
        apply Finset.sum_congr rfl
        intro i _
        have hin :
            (∑ j : Fin (m + 1), r i * r j * z j) =
              r i * (∑ j : Fin (m + 1), r j * z j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hin]
        ring
      _ = (∑ i : Fin (m + 1), z i * r i) *
          (∑ j : Fin (m + 1), r j * z j) := by
        rw [Finset.sum_mul]
      _ = (∑ i : Fin (m + 1), r i * z i) ^ 2 := by
        have hdot : (∑ i : Fin (m + 1), z i * r i) =
            ∑ i : Fin (m + 1), r i * z i := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hdot]
        ring
  have hpenalty :
      finiteQuadraticForm
          (fun i k : Fin (m + 1) =>
            lsNormwiseBackwardErrorMu theta y *
              (r i * r k / vecNorm2Sq y)) z =
        lsNormwiseBackwardErrorMu theta y *
          ((∑ i : Fin (m + 1), r i * z i) ^ 2 / vecNorm2Sq y) := by
    have hmatrix :
        (fun i k : Fin (m + 1) =>
          lsNormwiseBackwardErrorMu theta y *
            (r i * r k / vecNorm2Sq y)) =
          fun i k : Fin (m + 1) =>
            (lsNormwiseBackwardErrorMu theta y / vecNorm2Sq y) *
              (r i * r k) := by
      ext i k
      ring
    rw [hmatrix,
      finiteQuadraticForm_smul
        (lsNormwiseBackwardErrorMu theta y / vecNorm2Sq y)
        (fun i k : Fin (m + 1) => r i * r k) z,
      houter]
    ring
  have hquad :
      finiteQuadraticForm M z =
        -(lsNormwiseBackwardErrorMu theta y *
          ((∑ i : Fin (m + 1), r i * z i) ^ 2 / vecNorm2Sq y)) := by
    unfold M lsNormwiseBackwardErrorEigenMatrix
    rw [finiteQuadraticForm_sub, hgram, hpenalty]
    ring
  have hquad_neg : finiteQuadraticForm M z < 0 := by
    rw [hquad]
    have hsquare : 0 < (∑ i : Fin (m + 1), r i * z i) ^ 2 :=
      sq_pos_of_ne_zero hpair
    have hquot : 0 <
        (∑ i : Fin (m + 1), r i * z i) ^ 2 / vecNorm2Sq y :=
      div_pos hsquare hysq_pos
    nlinarith [mul_pos hmu_pos hquot]
  have hlower :=
    lsNormwiseBackwardErrorLambdaStar_mul_vecNorm2Sq_le_eigenMatrix_quadraticForm
      theta A r y z
  by_contra hnot
  have hlambda : 0 <= lsNormwiseBackwardErrorLambdaStar theta A r y :=
    le_of_not_gt hnot
  have hprod : 0 <=
      lsNormwiseBackwardErrorLambdaStar theta A r y * vecNorm2Sq z :=
    mul_nonneg hlambda (vecNorm2Sq_nonneg z)
  linarith

end NumStability
