-- Algorithms/Underdetermined/UnderdeterminedSolve.lean
--
-- Error analysis of solution methods for underdetermined systems
-- (Higham §21.3).
--
-- Q method (Theorem 21.4): the concrete rounded Householder-QR output is
-- row-wise backward stable under an explicit source-shaped gamma/cond2
-- smallness condition. A legacy coarse Gram predicate is retained below.
--
-- SNE method: solves RᵀRy = b by two rounded triangular solves. The
-- componentwise Gram-system envelope below is only an intermediate result;
-- the source-shaped equation (21.11) endpoint uses the signed factorwise
-- Demmel--Higham cancellation developed in the dedicated Higham21SNE modules.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.HighamChapter7
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.Cholesky.CholeskySolve
import NumStability.Algorithms.QR.Higham19
import NumStability.Algorithms.QR.GramSchmidt
import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  QR block algebra for the Q method and SNE setup
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.1):
    source-facing wrapper for multiplying by the tall QR block `[R; 0]`
    appearing in `Aᵀ = Q [R; 0]`. -/
theorem higham21_eq21_1_qr_transpose_block_mulVec {m k : ℕ}
    (R : Fin m → Fin m → ℝ) (x : Fin m → ℝ) :
    rectMatMulVec (lsQRTallBlock (k := k) R) x =
      Fin.append (rectMatMulVec R x) (0 : Fin k → ℝ) :=
  lsQRTallBlock_mulVec R x

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.2):
    source-facing wrapper for the block-transpose coordinate identity
    `[Rᵀ 0] [y₁; y₂] = Rᵀ y₁`.  This is the algebraic step behind reducing
    `b = A x` to the triangular equation for the first coordinate block after
    applying the orthogonal factor from (21.1). -/
theorem higham21_eq21_2_qr_block_transpose_coordinates {m k : ℕ}
    (R : Fin m → Fin m → ℝ) (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    (fun j : Fin m =>
      ∑ i : Fin (m + k), lsQRTallBlock (k := k) R i j *
        Fin.append y1 y2 i) =
      fun j : Fin m => ∑ i : Fin m, R i j * y1 i :=
  lsQRTallBlock_transpose_mulVec_append R y1 y2

/-- Orthogonal-coordinate transpose action for a rectangular panel.  If
    `M = Q B`, then `Mᵀ (Q y) = Bᵀ y`. -/
theorem higham21_matMulRectLeft_transpose_action_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) (hQ : IsOrthogonal m Q) :
    rectMatMulVec (finiteTranspose (matMulRectLeft Q B))
        (matMulVec m Q y) =
      fun j : Fin n => ∑ i : Fin m, B i j * y i := by
  ext j
  unfold rectMatMulVec finiteTranspose matMulRectLeft matMulVec
  calc
    ∑ i : Fin m, (∑ k : Fin m, Q i k * B k j) *
        (∑ l : Fin m, Q i l * y l)
        = ∑ i : Fin m, ∑ k : Fin m, ∑ l : Fin m,
            (Q i k * B k j) * (Q i l * y l) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin m, ∑ l : Fin m, ∑ i : Fin m,
          (Q i k * B k j) * (Q i l * y l) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (∑ i : Fin m, Q i k * Q i l) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (if k = l then 1 else 0) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [hQ.col_orthonormal k l]
    _ = ∑ k : Fin m, B k j * y k := by
            simp [Finset.mem_univ]

/-- Multiplying by an orthogonal matrix recovers a vector from its transposed
    coordinates. -/
theorem higham21_matMulVec_orthogonal_mul_transpose {n : ℕ}
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrthogonal n Q)
    (x : Fin n → ℝ) :
    matMulVec n Q (matMulVec n (matTranspose Q) x) = x := by
  ext i
  calc
    matMulVec n Q (matMulVec n (matTranspose Q) x) i
        = matMulVec n (matMul n Q (matTranspose Q)) x i := by
            exact (matMulVec_matMul n Q (matTranspose Q) x i).symm
    _ = matMulVec n (idMatrix n) x i := by
            have hmat : matMul n Q (matTranspose Q) = idMatrix n := by
              ext a b
              exact hQ.right_inv a b
            rw [hmat]
    _ = x i := by
            exact congrFun (matMulVec_id n x) i

/-- Reconstruct a vector over `Fin (p + q)` from its left and right
    `Fin.append` coordinate blocks. -/
theorem higham21_finAppend_left_right {p q : ℕ}
    (y : Fin (p + q) → ℝ) :
    Fin.append
        (fun i : Fin p => y (Fin.castAdd q i))
        (fun i : Fin q => y (Fin.natAdd p i)) =
      y := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (p + q) =>
      Fin.append
          (fun i : Fin p => y (Fin.castAdd q i))
          (fun i : Fin q => y (Fin.natAdd p i)) i = y i)
    ?left ?right i
  · intro i
    simp [Fin.append_left]
  · intro i
    simp [Fin.append_right]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equations (21.1)-(21.3):
    exact QR-coordinate handoff for the underdetermined system.  If
    `Aᵀ = Q [R;0]`, represented here by
    `A = (Q [R;0])ᵀ`, then applying `A` to `Q[y₁;y₂]` gives the
    triangular coordinate equation `Rᵀ y₁`. -/
theorem higham21_qr_transpose_system_eq {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    rectMatMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
        (matMulVec (m + k) Q (Fin.append y1 y2)) =
      fun j : Fin m => ∑ i : Fin m, R i j * y1 i := by
  have hcols :=
    higham21_matMulRectLeft_transpose_action_orthogonal
      Q (lsQRTallBlock (k := k) R) (Fin.append y1 y2) hQ
  ext j
  calc
    rectMatMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
        (matMulVec (m + k) Q (Fin.append y1 y2)) j
        = (fun j : Fin m =>
            ∑ i : Fin (m + k), lsQRTallBlock (k := k) R i j *
              Fin.append y1 y2 i) j := by
            exact congrFun hcols j
    _ = (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) j := by
            exact congrFun (lsQRTallBlock_transpose_mulVec_append R y1 y2) j

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equations (21.1) and (21.5):
    the Gram matrix of `(Q B)ᵀ` is the right Gram matrix of `B` when `Q` is
    orthogonal.  This is the algebraic cancellation behind deriving the SNE
    matrix from the QR representation `Aᵀ = Q B`. -/
theorem higham21_rectGram_finiteTranspose_matMulRectLeft_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q) :
    rectGram (finiteTranspose (matMulRectLeft Q B)) =
      fun i j : Fin n => ∑ r : Fin m, B r i * B r j := by
  ext i j
  unfold rectGram finiteTranspose matMulRectLeft
  calc
    ∑ row : Fin m, (∑ a : Fin m, Q row a * B a i) *
        (∑ b : Fin m, Q row b * B b j)
        = ∑ row : Fin m, ∑ a : Fin m, ∑ b : Fin m,
            (Q row a * B a i) * (Q row b * B b j) := by
            apply Finset.sum_congr rfl
            intro row _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ = ∑ a : Fin m, ∑ b : Fin m, ∑ row : Fin m,
          (Q row a * Q row b) * (B a i * B b j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro row _
            ring
    _ = ∑ a : Fin m, ∑ b : Fin m,
          (∑ row : Fin m, Q row a * Q row b) * (B a i * B b j) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
    _ = ∑ a : Fin m, ∑ b : Fin m,
          (if a = b then 1 else 0) * (B a i * B b j) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [hQ.col_orthonormal a b]
    _ = ∑ a : Fin m, B a i * B a j := by
            simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    the right Gram matrix of the tall block `[R;0]` is `RᵀR`. -/
theorem higham21_eq21_5_tall_block_right_gram {m k : ℕ}
    (R : Fin m → Fin m → ℝ) :
    (fun i j : Fin m =>
        ∑ row : Fin (m + k),
          lsQRTallBlock (k := k) R row i * lsQRTallBlock (k := k) R row j) =
      fun i j : Fin m => ∑ row : Fin m, R row i * R row j := by
  ext i j
  unfold lsQRTallBlock
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    if `Aᵀ = Q [R;0]` with `Q` orthogonal, then the SNE matrix
    `A Aᵀ` is `RᵀR`.  The theorem is stated for the exact rectangular matrix
    represented in this development as `A = (Q [R;0])ᵀ`. -/
theorem higham21_eq21_5_qr_sne_gram_eq {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ) :
    rectGram (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) =
      fun i j : Fin m => ∑ row : Fin m, R row i * R row j := by
  calc
    rectGram (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
        = (fun i j : Fin m =>
            ∑ row : Fin (m + k),
              lsQRTallBlock (k := k) R row i *
                lsQRTallBlock (k := k) R row j) := by
            exact
              higham21_rectGram_finiteTranspose_matMulRectLeft_orthogonal
                Q (lsQRTallBlock (k := k) R) hQ
    _ = fun i j : Fin m => ∑ row : Fin m, R row i * R row j :=
            higham21_eq21_5_tall_block_right_gram (k := k) R

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    QR-specialized SNE formation step.  Under `Aᵀ = Q[R;0]`, a vector `y`
    solving `RᵀR y = b`, followed by `x = Aᵀ y`, solves `A x = b`. -/
theorem higham21_eq21_5_sne_rect_transpose_solution_of_qr {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R SNE : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (x : Fin (m + k) → ℝ)
    (hSNE : ∀ i j : Fin m, SNE i j = ∑ row : Fin m, R row i * R row j)
    (hy : ∀ i : Fin m, matMulVec m SNE y i = b i)
    (hx :
      x = rectTransposeMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) y) :
    rectMatMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) x =
      b := by
  let A : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))
  have hgram := higham21_eq21_5_qr_sne_gram_eq Q hQ R
  have hSNEgram : ∀ i j : Fin m, SNE i j = rectGram A i j := by
    intro i j
    calc
      SNE i j = ∑ row : Fin m, R row i * R row j := hSNE i j
      _ = rectGram A i j := by
          exact (congrFun (congrFun hgram i) j).symm
  exact higham21_eq21_5_sne_rect_transpose_solution A SNE b y x hSNEgram hy hx

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    QR-specialized SNE minimum-norm handoff.  Under `Aᵀ = Q[R;0]`, solving
    `RᵀR y = b` and forming `x = Aᵀ y` gives the minimum 2-norm solution of
    the exact underdetermined system. -/
theorem higham21_eq21_5_sne_rect_transpose_min_norm_of_qr {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R SNE : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hSNE : ∀ i j : Fin m, SNE i j = ∑ row : Fin m, R row i * R row j)
    (hy : ∀ i : Fin m, matMulVec m SNE y i = b i) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (rectTransposeMulVec
        (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))) y) := by
  let A : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R))
  exact higham21_eq21_4_rect_transpose_min_norm_of_solves A b y
    (higham21_eq21_5_sne_rect_transpose_solution_of_qr
      Q hQ R SNE b y (rectTransposeMulVec A y) hSNE hy rfl)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    source-facing algebraic wrapper for the minimum-norm coordinate choice
    in the Q method.  Among coordinate vectors with the same first block,
    setting the free second block to zero gives no larger Euclidean norm.
    This is the norm-minimization step only; the full orthogonal `Q` handoff
    and triangular solve formula remain separate selected targets. -/
theorem higham21_eq21_3_free_coordinate_zero_min_norm {m k : ℕ}
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) ≤
      vecNorm2 (Fin.append y1 y2) := by
  have hzero :
      vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := by
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  calc
    vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := hzero
    _ ≤ vecNorm2 (Fin.append y1 y2) := lsVecNorm2_left_le_append y1 y2

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    source-facing lift of the free-coordinate norm-minimization step through
    the orthogonal factor `Q`.  Since orthogonal multiplication preserves the
    Euclidean norm, the vector `Q [y₁; 0]` has no larger norm than
    `Q [y₁; y₂]` for the same first coordinate block. -/
theorem higham21_eq21_3_q_factor_zero_free_block_min_norm {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    vecNorm2 (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) ≤
      vecNorm2 (matMulVec (m + k) Q (Fin.append y1 y2)) := by
  rw [vecNorm2_orthogonal Q (Fin.append y1 (0 : Fin k → ℝ)) hQ,
    vecNorm2_orthogonal Q (Fin.append y1 y2) hQ]
  exact higham21_eq21_3_free_coordinate_zero_min_norm y1 y2

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equations (21.1)-(21.3):
    exact Q-method minimum-norm handoff.  Under the supplied exact QR
    factorization `Aᵀ = Q [R;0]`, if `y₁` is the unique solution of the
    triangular coordinate equation `Rᵀ y₁ = b`, then the Q-method vector
    `Q [y₁;0]` is the minimum 2-norm solution of `A x = b`.

    This proves the QR-coordinate/minimum-norm algebra; the existence and
    triangular nonsingularity route for `R` remain separate selected targets. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_unique {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b)
    (huniq :
      ∀ z1 : Fin m → ℝ,
        (fun j : Fin m => ∑ i : Fin m, R i j * z1 i) = b → z1 = y1) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) := by
  constructor
  · rw [higham21_qr_transpose_system_eq Q hQ R y1 (0 : Fin k → ℝ), hy1]
  · intro z hz
    let y : Fin (m + k) → ℝ := matMulVec (m + k) (matTranspose Q) z
    let z1 : Fin m → ℝ := fun i => y (Fin.castAdd k i)
    let z2 : Fin k → ℝ := fun i => y (Fin.natAdd m i)
    have hy_append : Fin.append z1 z2 = y := by
      simpa [z1, z2] using higham21_finAppend_left_right (p := m) (q := k) y
    have hz_recover :
        matMulVec (m + k) Q (Fin.append z1 z2) = z := by
      rw [hy_append]
      exact higham21_matMulVec_orthogonal_mul_transpose hQ z
    have hz1_solve :
        (fun j : Fin m => ∑ i : Fin m, R i j * z1 i) = b := by
      have hAw :=
        higham21_qr_transpose_system_eq Q hQ R z1 z2
      rw [← hAw, hz_recover, hz]
    have hz1_eq : z1 = y1 := huniq z1 hz1_solve
    calc
      vecNorm2 (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)))
          = vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) := by
              exact vecNorm2_orthogonal Q (Fin.append y1 (0 : Fin k → ℝ)) hQ
      _ ≤ vecNorm2 (Fin.append z1 z2) := by
              simpa [hz1_eq] using
                higham21_eq21_3_free_coordinate_zero_min_norm y1 z2
      _ = vecNorm2 (matMulVec (m + k) Q (Fin.append z1 z2)) := by
              exact (vecNorm2_orthogonal Q (Fin.append z1 z2) hQ).symm
      _ = vecNorm2 z := by
              rw [hz_recover]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    uniqueness of the triangular coordinate equation `Rᵀ y₁ = b` from a
    supplied inverse of `Rᵀ`. -/
theorem higham21_eq21_3_transpose_triangular_solution_unique_of_inverse {m : ℕ}
    (R RTinv : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hInv : IsInverse m (matTranspose R) RTinv)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    ∀ z1 : Fin m → ℝ,
      (fun j : Fin m => ∑ i : Fin m, R i j * z1 i) = b → z1 = y1 := by
  intro z1 hz1
  have hy1_mv : rectMatMulVec (matTranspose R) y1 = b := by
    ext j
    exact congrFun hy1 j
  have hz1_mv : rectMatMulVec (matTranspose R) z1 = b := by
    ext j
    exact congrFun hz1 j
  calc
    z1 = rectMatMulVec RTinv (rectMatMulVec (matTranspose R) z1) := by
          exact (rectMatMulVec_left_inverse_of_IsLeftInverse hInv.1 z1).symm
    _ = rectMatMulVec RTinv b := by rw [hz1_mv]
    _ = rectMatMulVec RTinv (rectMatMulVec (matTranspose R) y1) := by rw [hy1_mv]
    _ = y1 := rectMatMulVec_left_inverse_of_IsLeftInverse hInv.1 y1

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    exact Q-method minimum-norm handoff with the triangular solve uniqueness
    instantiated from an inverse of `Rᵀ`. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_inverse {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R RTinv : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hInv : IsInverse m (matTranspose R) RTinv)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) :=
  higham21_eq21_3_q_method_min_norm_of_qr_unique Q hQ R b y1 hy1
    (higham21_eq21_3_transpose_triangular_solution_unique_of_inverse
      R RTinv b y1 hInv hy1)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    determinant-facing exact Q-method minimum-norm handoff, using the
    repository nonsingular inverse for `Rᵀ`. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_det_ne_zero {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hdetT : Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) :=
  higham21_eq21_3_q_method_min_norm_of_qr_inverse
    Q hQ R (nonsingInv m (matTranspose R)) b y1
    (isInverse_nonsingInv_of_det_ne_zero m (matTranspose R) hdetT)
    hy1

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    determinant-facing exact Q-method minimum-norm handoff from nonsingularity
    of the triangular factor `R` itself.  This is a thin source-facing bridge
    from the usual triangular-factor determinant condition to the transposed
    coordinate solve `Rᵀ y₁ = b`. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_R_det_ne_zero {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hdet : Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) := by
  have hdetT : Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    change Matrix.det (Matrix.transpose (R : Matrix (Fin m) (Fin m) ℝ)) ≠ 0
    simpa [Matrix.det_transpose] using hdet
  exact higham21_eq21_3_q_method_min_norm_of_qr_det_ne_zero Q hQ R b y1 hdetT hy1

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    exact Q-method minimum-norm handoff from the usual triangular-factor
    nonsingularity condition: `R` is upper triangular with nonzero diagonal. -/
theorem higham21_eq21_3_q_method_min_norm_of_qr_upper_diag_ne_zero {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hupper : IsUpperTrapezoidal m m R)
    (hdiag : ∀ i : Fin m, R i i ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    RectMinNormSolution m (m + k)
      (finiteTranspose (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
      b
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ))) := by
  have hdet : Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero m R hupper hdiag
  exact higham21_eq21_3_q_method_min_norm_of_qr_R_det_ne_zero Q hQ R b y1 hdet hy1

-- Equation (21.7): exact one-parameter first-order expansion.

noncomputable def higham21Eq21_7ScaledMatrix
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (t : ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => A i j + t * DeltaA i j

noncomputable def higham21Eq21_7ScaledRhs
    {m : ℕ} (b Deltab : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun i => b i + t * Deltab i

noncomputable def higham21Eq21_7GramLinear
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i r =>
    Finset.univ.sum (fun j : Fin n =>
      A i j * DeltaA r j + DeltaA i j * A r j)

noncomputable def higham21Eq21_7GramQuadratic
    {m n : ℕ} (DeltaA : Fin m → Fin n → ℝ) :
    Fin m → Fin m → ℝ :=
  rectGram DeltaA

noncomputable def higham21Eq21_7GramPerturbation
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (t : ℝ) :
    Fin m → Fin m → ℝ :=
  fun i r =>
    t * higham21Eq21_7GramLinear A DeltaA i r +
      t ^ 2 * higham21Eq21_7GramQuadratic DeltaA i r

theorem higham21Eq21_7_rectGram_scaledMatrix
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (t : ℝ) :
    rectGram (higham21Eq21_7ScaledMatrix A DeltaA t) =
      fun i r =>
        rectGram A i r +
          higham21Eq21_7GramPerturbation A DeltaA t i r := by
  ext i r
  simp only [higham21Eq21_7ScaledMatrix, rectGram,
    higham21Eq21_7GramPerturbation, higham21Eq21_7GramLinear,
    higham21Eq21_7GramQuadratic]
  calc
    Finset.univ.sum (fun j : Fin n =>
        (A i j + t * DeltaA i j) * (A r j + t * DeltaA r j)) =
      Finset.univ.sum (fun j : Fin n =>
        A i j * A r j +
          (t * (A i j * DeltaA r j + DeltaA i j * A r j) +
            t ^ 2 * (DeltaA i j * DeltaA r j))) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = Finset.univ.sum (fun j : Fin n => A i j * A r j) +
        (Finset.univ.sum (fun j : Fin n =>
            t * (A i j * DeltaA r j + DeltaA i j * A r j)) +
          Finset.univ.sum (fun j : Fin n =>
            t ^ 2 * (DeltaA i j * DeltaA r j))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = Finset.univ.sum (fun j : Fin n => A i j * A r j) +
        (t * Finset.univ.sum (fun j : Fin n =>
            A i j * DeltaA r j + DeltaA i j * A r j) +
          t ^ 2 * Finset.univ.sum (fun j : Fin n =>
            DeltaA i j * DeltaA r j)) := by
        rw [Finset.mul_sum, Finset.mul_sum]

noncomputable def higham21Eq21_7BaseSolution
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (G_inv : Fin m → Fin m → ℝ) : Fin n → ℝ :=
  rectMatMulVec (undetAplusOfGramInv A G_inv) b

noncomputable def higham21Eq21_7PerturbedSolution
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (b Deltab : Fin m → ℝ)
    (G_t_inv : Fin m → Fin m → ℝ) (t : ℝ) : Fin n → ℝ :=
  rectMatMulVec
    (undetAplusOfGramInv (higham21Eq21_7ScaledMatrix A DeltaA t) G_t_inv)
    (higham21Eq21_7ScaledRhs b Deltab t)

noncomputable def higham21Eq21_7FirstOrder
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (b Deltab : Fin m → ℝ)
    (G_inv : Fin m → Fin m → ℝ) : Fin n → ℝ :=
  let Aplus := undetAplusOfGramInv A G_inv
  let y := matMulVec m G_inv b
  let x := rectMatMulVec Aplus b
  fun j =>
    rectTransposeMulVec DeltaA y j -
        rectMatMulVec Aplus
          (rectMatMulVec A (rectTransposeMulVec DeltaA y)) j +
      rectMatMulVec Aplus
        (fun i => Deltab i - rectMatMulVec DeltaA x i) j

theorem higham21Eq21_7_gramLinear_action
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) :
    matMulVec m (higham21Eq21_7GramLinear A DeltaA) y =
      fun i =>
        rectMatMulVec A (rectTransposeMulVec DeltaA y) i +
          rectMatMulVec DeltaA (rectTransposeMulVec A y) i := by
  ext i
  simp only [matMulVec, higham21Eq21_7GramLinear,
    rectMatMulVec, rectTransposeMulVec]
  have hfirst :
      (∑ r : Fin m,
        (∑ j : Fin n, A i j * DeltaA r j) * y r) =
      ∑ j : Fin n,
        A i j * ∑ r : Fin m, DeltaA r j * y r := by
    calc
      (∑ r : Fin m,
          (∑ j : Fin n, A i j * DeltaA r j) * y r) =
        ∑ r : Fin m,
          ∑ j : Fin n, A i j * DeltaA r j * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
      _ = ∑ j : Fin n,
          ∑ r : Fin m, A i j * DeltaA r j * y r := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n,
          A i j * ∑ r : Fin m, DeltaA r j * y r := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            ring
  have hsecond :
      (∑ r : Fin m,
        (∑ j : Fin n, DeltaA i j * A r j) * y r) =
      ∑ j : Fin n,
        DeltaA i j * ∑ r : Fin m, A r j * y r := by
    calc
      (∑ r : Fin m,
          (∑ j : Fin n, DeltaA i j * A r j) * y r) =
        ∑ r : Fin m,
          ∑ j : Fin n, DeltaA i j * A r j * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
      _ = ∑ j : Fin n,
          ∑ r : Fin m, DeltaA i j * A r j * y r := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n,
          DeltaA i j * ∑ r : Fin m, A r j * y r := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            ring
  calc
    Finset.univ.sum (fun r : Fin m =>
        (Finset.univ.sum (fun j : Fin n =>
          A i j * DeltaA r j + DeltaA i j * A r j)) * y r) =
      Finset.univ.sum (fun r : Fin m =>
          (Finset.univ.sum (fun j : Fin n => A i j * DeltaA r j)) * y r) +
        Finset.univ.sum (fun r : Fin m =>
          (Finset.univ.sum (fun j : Fin n => DeltaA i j * A r j)) * y r) := by
            simp_rw [Finset.sum_add_distrib, add_mul]
            rw [Finset.sum_add_distrib]
    _ = Finset.univ.sum (fun j : Fin n =>
          A i j * Finset.univ.sum (fun r : Fin m => DeltaA r j * y r)) +
        Finset.univ.sum (fun j : Fin n =>
          DeltaA i j * Finset.univ.sum (fun r : Fin m => A r j * y r)) := by
            rw [hfirst, hsecond]

theorem higham21Eq21_7_matMulVec_sub_right
    {m : ℕ} (M : Fin m → Fin m → ℝ)
    (u v : Fin m → ℝ) :
    matMulVec m M (fun i => u i - v i) =
      fun i => matMulVec m M u i - matMulVec m M v i := by
  ext i
  unfold matMulVec
  simp [mul_sub, Finset.sum_sub_distrib]

theorem higham21Eq21_7_rectTransposeMulVec_add
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (u v : Fin m → ℝ) :
    rectTransposeMulVec A (fun i => u i + v i) =
      fun j => rectTransposeMulVec A u j + rectTransposeMulVec A v j := by
  ext j
  unfold rectTransposeMulVec
  simp [mul_add, Finset.sum_add_distrib]

theorem higham21Eq21_7_rectTransposeMulVec_sub
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (u v : Fin m → ℝ) :
    rectTransposeMulVec A (fun i => u i - v i) =
      fun j => rectTransposeMulVec A u j - rectTransposeMulVec A v j := by
  ext j
  unfold rectTransposeMulVec
  simp [mul_sub, Finset.sum_sub_distrib]

theorem higham21Eq21_7_rectTransposeMulVec_const_mul
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (t : ℝ) (u : Fin m → ℝ) :
    rectTransposeMulVec A (fun i => t * u i) =
      fun j => t * rectTransposeMulVec A u j := by
  ext j
  unfold rectTransposeMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem higham21Eq21_7_firstOrder_eq_gram_form
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (b Deltab : Fin m → ℝ)
    (G_inv : Fin m → Fin m → ℝ) :
    higham21Eq21_7FirstOrder A DeltaA b Deltab G_inv =
      fun j =>
        rectTransposeMulVec DeltaA (matMulVec m G_inv b) j -
          rectTransposeMulVec A
            (matMulVec m G_inv
              (matMulVec m (higham21Eq21_7GramLinear A DeltaA)
                (matMulVec m G_inv b))) j +
          rectTransposeMulVec A (matMulVec m G_inv Deltab) j := by
  let y : Fin m → ℝ := matMulVec m G_inv b
  let x : Fin n → ℝ := rectMatMulVec (undetAplusOfGramInv A G_inv) b
  have hx : x = rectTransposeMulVec A y := by
    simpa [x, y] using rectMatMulVec_undetAplusOfGramInv A G_inv b
  have hH :
      matMulVec m (higham21Eq21_7GramLinear A DeltaA) y =
        fun i =>
          rectMatMulVec A (rectTransposeMulVec DeltaA y) i +
            rectMatMulVec DeltaA x i := by
    rw [higham21Eq21_7_gramLinear_action]
    rw [hx]
  ext j
  simp only [higham21Eq21_7FirstOrder]
  rw [rectMatMulVec_undetAplusOfGramInv,
    rectMatMulVec_undetAplusOfGramInv]
  change
    rectTransposeMulVec DeltaA y j -
          rectTransposeMulVec A
            (matMulVec m G_inv
              (rectMatMulVec A (rectTransposeMulVec DeltaA y))) j +
        rectTransposeMulVec A
          (matMulVec m G_inv
            (fun i => Deltab i - rectMatMulVec DeltaA x i)) j =
      rectTransposeMulVec DeltaA y j -
          rectTransposeMulVec A
            (matMulVec m G_inv
              (matMulVec m (higham21Eq21_7GramLinear A DeltaA) y)) j +
        rectTransposeMulVec A (matMulVec m G_inv Deltab) j
  rw [hH]
  rw [matMulVec_add_right]
  rw [higham21Eq21_7_rectTransposeMulVec_add]
  rw [higham21Eq21_7_matMulVec_sub_right]
  rw [higham21Eq21_7_rectTransposeMulVec_sub]
  ring

noncomputable def higham21Eq21_7GramInverseDifferenceModel
    {m : ℕ} (G_inv E G_t_inv : Fin m → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i r =>
    -ch7InverseLinearizedEntry m G_inv E i r +
      ch7InverseQuadraticRemainderEntry m G_inv E G_t_inv i r

theorem higham21Eq21_7_gramInverse_difference
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (G_inv G_t_inv : Fin m → Fin m → ℝ) (t : ℝ)
    (hLeft : IsLeftInverse m (rectGram A) G_inv)
    (hRight :
      IsRightInverse m
        (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t)) G_t_inv) :
    ∀ i r,
      G_t_inv i r - G_inv i r =
        higham21Eq21_7GramInverseDifferenceModel G_inv
          (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv i r := by
  have hRightE :
      IsRightInverse m
        (fun i r =>
          rectGram A i r +
            higham21Eq21_7GramPerturbation A DeltaA t i r) G_t_inv := by
    have hGram :=
      higham21Eq21_7_rectGram_scaledMatrix A DeltaA t
    rw [hGram] at hRight
    exact hRight
  intro i r
  exact
    problem7_11_exact_inverse_firstOrder_remainder_identity
      m (rectGram A) G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv
        hLeft hRightE i r

noncomputable def higham21Eq21_7ExactRemainder
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (b Deltab : Fin m → ℝ)
    (G_inv G_t_inv : Fin m → Fin m → ℝ) (t : ℝ) :
    Fin n → ℝ :=
  let H := higham21Eq21_7GramLinear A DeltaA
  let E := higham21Eq21_7GramPerturbation A DeltaA t
  let dGinv :=
    higham21Eq21_7GramInverseDifferenceModel G_inv E G_t_inv
  let y := matMulVec m G_inv b
  fun j =>
    rectTransposeMulVec A (matMulVec m dGinv b) j +
      t * rectTransposeMulVec DeltaA (matMulVec m dGinv b) j +
      t * rectTransposeMulVec A (matMulVec m dGinv Deltab) j +
      t ^ 2 *
        rectTransposeMulVec DeltaA (matMulVec m G_t_inv Deltab) j +
      t * rectTransposeMulVec A
        (matMulVec m G_inv (matMulVec m H y)) j

theorem higham21Eq21_7_scaledMatrix_transpose_action
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (t : ℝ) (z : Fin m → ℝ) :
    rectTransposeMulVec (higham21Eq21_7ScaledMatrix A DeltaA t) z =
      fun j =>
        rectTransposeMulVec A z j +
          t * rectTransposeMulVec DeltaA z j := by
  ext j
  unfold rectTransposeMulVec higham21Eq21_7ScaledMatrix
  calc
    ∑ i : Fin m, (A i j + t * DeltaA i j) * z i =
      (∑ i : Fin m, A i j * z i) +
        ∑ i : Fin m, t * (DeltaA i j * z i) := by
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          apply congrArg (fun q : ℝ => _ + q)
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i : Fin m, A i j * z i) +
        t * ∑ i : Fin m, DeltaA i j * z i := by
          rw [Finset.mul_sum]

theorem higham21Eq21_7_scaledRhs_action
    {m : ℕ} (M : Fin m → Fin m → ℝ)
    (b Deltab : Fin m → ℝ) (t : ℝ) :
    matMulVec m M (higham21Eq21_7ScaledRhs b Deltab t) =
      fun i =>
        matMulVec m M b i + t * matMulVec m M Deltab i := by
  unfold higham21Eq21_7ScaledRhs
  rw [matMulVec_add_right]
  rw [matMulVec_const_mul_right]

theorem higham21Eq21_7_exact_expansion
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (b Deltab : Fin m → ℝ)
    (G_inv G_t_inv : Fin m → Fin m → ℝ) (t : ℝ)
    (hLeft : IsLeftInverse m (rectGram A) G_inv)
    (hRight :
      IsRightInverse m
        (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t)) G_t_inv) :
    (fun j =>
      higham21Eq21_7PerturbedSolution
          A DeltaA b Deltab G_t_inv t j -
        higham21Eq21_7BaseSolution A b G_inv j) =
      fun j =>
        t * higham21Eq21_7FirstOrder A DeltaA b Deltab G_inv j +
          higham21Eq21_7ExactRemainder
            A DeltaA b Deltab G_inv G_t_inv t j := by
  let At : Fin m → Fin n → ℝ :=
    higham21Eq21_7ScaledMatrix A DeltaA t
  let bt : Fin m → ℝ := higham21Eq21_7ScaledRhs b Deltab t
  let H : Fin m → Fin m → ℝ :=
    higham21Eq21_7GramLinear A DeltaA
  let E : Fin m → Fin m → ℝ :=
    higham21Eq21_7GramPerturbation A DeltaA t
  let dGinv : Fin m → Fin m → ℝ :=
    higham21Eq21_7GramInverseDifferenceModel G_inv E G_t_inv
  let y : Fin m → ℝ := matMulVec m G_inv b
  let q : Fin m → ℝ := matMulVec m G_inv Deltab
  let rb : Fin m → ℝ := matMulVec m dGinv b
  let rd : Fin m → ℝ := matMulVec m dGinv Deltab
  have hdiff : ∀ i r, G_t_inv i r - G_inv i r = dGinv i r := by
    intro i r
    simpa [dGinv, E] using
      higham21Eq21_7_gramInverse_difference
        A DeltaA G_inv G_t_inv t hLeft hRight i r
  have hmatrix :
      G_t_inv = fun i r => G_inv i r + dGinv i r := by
    ext i r
    have hir := hdiff i r
    linarith
  have hBb :
      matMulVec m G_t_inv b = fun i => y i + rb i := by
    rw [hmatrix, matMulVec_add_left]
  have hBd :
      matMulVec m G_t_inv Deltab = fun i => q i + rd i := by
    rw [hmatrix, matMulVec_add_left]
  have hBbt :
      matMulVec m G_t_inv bt =
        fun i => y i + rb i + t * (q i + rd i) := by
    rw [show bt = higham21Eq21_7ScaledRhs b Deltab t by rfl]
    rw [higham21Eq21_7_scaledRhs_action]
    rw [hBb, hBd]
  have hbase :
      higham21Eq21_7BaseSolution A b G_inv =
        rectTransposeMulVec A y := by
    simpa [higham21Eq21_7BaseSolution, y] using
      rectMatMulVec_undetAplusOfGramInv A G_inv b
  have hpert :
      higham21Eq21_7PerturbedSolution
          A DeltaA b Deltab G_t_inv t =
        rectTransposeMulVec At (matMulVec m G_t_inv bt) := by
    simpa [higham21Eq21_7PerturbedSolution, At, bt] using
      rectMatMulVec_undetAplusOfGramInv At G_t_inv bt
  have hfirst :
      higham21Eq21_7FirstOrder A DeltaA b Deltab G_inv =
        fun j =>
          rectTransposeMulVec DeltaA y j -
            rectTransposeMulVec A
              (matMulVec m G_inv (matMulVec m H y)) j +
            rectTransposeMulVec A q j := by
    simpa [y, q, H] using
      higham21Eq21_7_firstOrder_eq_gram_form
        A DeltaA b Deltab G_inv
  ext j
  rw [hpert, hbase, hBbt]
  rw [show At = higham21Eq21_7ScaledMatrix A DeltaA t by rfl]
  rw [higham21Eq21_7_scaledMatrix_transpose_action]
  simp only [higham21Eq21_7_rectTransposeMulVec_add,
    higham21Eq21_7_rectTransposeMulVec_const_mul]
  rw [hfirst]
  unfold higham21Eq21_7ExactRemainder
  change
    ((rectTransposeMulVec A y j + rectTransposeMulVec A rb j) +
          t * (rectTransposeMulVec A q j + rectTransposeMulVec A rd j) +
        t *
          ((rectTransposeMulVec DeltaA y j +
              rectTransposeMulVec DeltaA rb j) +
            t * (rectTransposeMulVec DeltaA q j +
              rectTransposeMulVec DeltaA rd j))) -
      rectTransposeMulVec A y j =
    t *
        (rectTransposeMulVec DeltaA y j -
          rectTransposeMulVec A
              (matMulVec m G_inv (matMulVec m H y)) j +
          rectTransposeMulVec A q j) +
      (rectTransposeMulVec A rb j +
        t * rectTransposeMulVec DeltaA rb j +
        t * rectTransposeMulVec A rd j +
        t ^ 2 * rectTransposeMulVec DeltaA
          (matMulVec m G_t_inv Deltab) j +
        t * rectTransposeMulVec A
          (matMulVec m G_inv (matMulVec m H y)) j)
  rw [hBd]
  rw [higham21Eq21_7_rectTransposeMulVec_add]
  ring

theorem higham21Eq21_7_exact_expansion_of_gram_det_ne_zero
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ)
    (b Deltab : Fin m → ℝ) (t : ℝ)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hdet_t :
      Matrix.det
        (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    (fun j =>
      higham21Eq21_7PerturbedSolution A DeltaA b Deltab
          (undetGramNonsingInv
            (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
        higham21Eq21_7BaseSolution A b (undetGramNonsingInv A) j) =
      fun j =>
        t * higham21Eq21_7FirstOrder A DeltaA b Deltab
              (undetGramNonsingInv A) j +
          higham21Eq21_7ExactRemainder A DeltaA b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A DeltaA t)) t j := by
  apply higham21Eq21_7_exact_expansion
  exact
    (isInverse_nonsingInv_of_det_ne_zero
      m (rectGram A) hdet).1
  exact
    (isInverse_nonsingInv_of_det_ne_zero m
      (rectGram (higham21Eq21_7ScaledMatrix A DeltaA t)) hdet_t).2

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.7):
    the null-space and pseudoinverse-range vectors in the first-order change
    are orthogonal. -/
theorem higham21Eq21_7_source_vectors_orthogonal
    {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ)
    (b Deltab : Fin m → ℝ)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    let Aplus := undetAplusOfGramNonsingInv A
    let x := rectMatMulVec Aplus b
    let z := rectTransposeMulVec Aplus x
    let w := rectTransposeMulVec DeltaA z
    let q := fun i => Deltab i - rectMatMulVec DeltaA x i
    (∑ j : Fin n,
      (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) *
        rectMatMulVec Aplus q j) = 0 := by
  dsimp only
  let Aplus : Fin n → Fin m → ℝ :=
    undetAplusOfGramNonsingInv A
  let x : Fin n → ℝ := rectMatMulVec Aplus b
  let z : Fin m → ℝ := rectTransposeMulVec Aplus x
  let w : Fin n → ℝ := rectTransposeMulVec DeltaA z
  let q : Fin m → ℝ :=
    fun i => Deltab i - rectMatMulVec DeltaA x i
  change
    (∑ j : Fin n,
      (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) *
        rectMatMulVec Aplus q j) = 0
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hSym :
      IsSymmetricFiniteMatrix (rectMatMul Aplus A) := by
    simpa [Aplus] using
      undetAplusOfGramNonsingInv_domain_projection_symmetric A
  simpa only [rectMatMulVec_rectMatMul] using
    (rectMatMulVec_domainProjection_residual_orthogonal_range_of_symmetric_right_inverse
      A Aplus hRight hSym w q)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.6):
    direct componentwise majorant for the first-order change in (21.7).
    The first term is
    `|(I - Aplus*A) DeltaA^T Aplus^T x|`; the second is
    `|Aplus| (f + E|x|)`. -/
theorem higham21Eq21_7_firstOrder_componentwise_abs_majorant
    {m n : ℕ}
    (A DeltaA E : Fin m → Fin n → ℝ)
    (b Deltab f : Fin m → ℝ)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hDeltaA : ∀ i j, |DeltaA i j| ≤ E i j)
    (hDeltab : ∀ i, |Deltab i| ≤ f i) :
    let Aplus := undetAplusOfGramNonsingInv A
    let x := rectMatMulVec Aplus b
    let z := rectTransposeMulVec Aplus x
    let w := rectTransposeMulVec DeltaA z
    ∀ j : Fin n,
      |higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A) j| ≤
        |w j - rectMatMulVec Aplus (rectMatMulVec A w) j| +
          rectMatMulVec (absMatrixRect Aplus)
            (fun i => f i + rectMatMulVec E (fun k => |x k|) i) j := by
  dsimp only
  intro j
  let G_inv : Fin m → Fin m → ℝ := undetGramNonsingInv A
  let Aplus : Fin n → Fin m → ℝ :=
    undetAplusOfGramNonsingInv A
  let x : Fin n → ℝ := rectMatMulVec Aplus b
  let y : Fin m → ℝ := matMulVec m G_inv b
  let z : Fin m → ℝ := rectTransposeMulVec Aplus x
  let w : Fin n → ℝ := rectTransposeMulVec DeltaA z
  let q : Fin m → ℝ :=
    fun i => Deltab i - rectMatMulVec DeltaA x i
  let budget : Fin m → ℝ :=
    fun i => f i + rectMatMulVec E (fun k => |x k|) i
  change
    |higham21Eq21_7FirstOrder A DeltaA b Deltab G_inv j| ≤
      |w j - rectMatMulVec Aplus (rectMatMulVec A w) j| +
        rectMatMulVec (absMatrixRect Aplus) budget j
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hRightEntry : ∀ r i : Fin m,
      (∑ k : Fin n, A r k * Aplus k i) =
        if r = i then 1 else 0 := by
    intro r i
    have hri := congrFun (congrFun hRight r) i
    simpa [rectMatMul, idMatrix] using hri
  have hx : x = rectTransposeMulVec A y := by
    simpa [x, Aplus, y, G_inv, undetAplusOfGramNonsingInv] using
      (rectMatMulVec_undetAplusOfGramInv A G_inv b)
  have hyz : y = z := by
    ext i
    symm
    rw [show z = rectTransposeMulVec Aplus x by rfl, hx]
    unfold rectTransposeMulVec
    calc
      ∑ j : Fin n, Aplus j i * (∑ r : Fin m, A r j * y r) =
          ∑ j : Fin n, ∑ r : Fin m,
            Aplus j i * (A r j * y r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ r : Fin m, ∑ j : Fin n,
            Aplus j i * (A r j * y r) := by
            rw [Finset.sum_comm]
      _ = ∑ r : Fin m,
            (∑ j : Fin n, A r j * Aplus j i) * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ r : Fin m, (if r = i then 1 else 0) * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [hRightEntry r i]
      _ = y i := by
            simp
  have hsource :
      higham21Eq21_7FirstOrder A DeltaA b Deltab G_inv j =
        (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) +
          rectMatMulVec Aplus q j := by
    simp only [higham21Eq21_7FirstOrder]
    change
      rectTransposeMulVec DeltaA y j -
            rectMatMulVec Aplus
              (rectMatMulVec A (rectTransposeMulVec DeltaA y)) j +
          rectMatMulVec Aplus q j =
        (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) +
          rectMatMulVec Aplus q j
    rw [hyz]
  have hDeltaAction : ∀ i : Fin m,
      |rectMatMulVec DeltaA x i| ≤
        rectMatMulVec E (fun k => |x k|) i :=
    rectMatMulVec_abs_entry_le hDeltaA x
  have hq : ∀ i : Fin m, |q i| ≤ budget i := by
    intro i
    change
      |Deltab i - rectMatMulVec DeltaA x i| ≤
        f i + rectMatMulVec E (fun k => |x k|) i
    exact
      le_trans (abs_sub _ _)
        (add_le_add (hDeltab i) (hDeltaAction i))
  have hv :
      |rectMatMulVec Aplus q j| ≤
        rectMatMulVec (absMatrixRect Aplus) budget j := by
    calc
      |rectMatMulVec Aplus q j| ≤
          ∑ i : Fin m, |Aplus j i| * |q i| :=
        abs_rectMatMulVec_le Aplus q j
      _ ≤ ∑ i : Fin m, |Aplus j i| * budget i := by
        apply Finset.sum_le_sum
        intro i _
        exact
          mul_le_mul_of_nonneg_left (hq i) (abs_nonneg (Aplus j i))
      _ = rectMatMulVec (absMatrixRect Aplus) budget j := by
        rfl
  calc
    |higham21Eq21_7FirstOrder A DeltaA b Deltab G_inv j| =
        |(w j - rectMatMulVec Aplus (rectMatMulVec A w) j) +
          rectMatMulVec Aplus q j| :=
      congrArg (fun r : ℝ => |r|) hsource
    _ ≤ |w j - rectMatMulVec Aplus (rectMatMulVec A w) j| +
          |rectMatMulVec Aplus q j| :=
      abs_add_le _ _
    _ ≤ |w j - rectMatMulVec Aplus (rectMatMulVec A w) j| +
          rectMatMulVec (absMatrixRect Aplus) budget j :=
      add_le_add le_rfl hv

-- Equation (21.7): explicit fixed-radius quadratic remainder bounds.
section Higham21Eq21_7QuadraticRemainder

open Filter
open Asymptotics
noncomputable def higham21Eq21_7GramAbsEnvelope
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real) (rho : Real) :
    Fin m -> Fin m -> Real :=
  let H := higham21Eq21_7GramLinear A DeltaA
  let K := higham21Eq21_7GramQuadratic DeltaA
  fun i j => |H i j| + rho * |K i j|

noncomputable def higham21Eq21_7LinearizedMatrix
    {m : Nat} (G_inv D : Fin m -> Fin m -> Real) :
    Fin m -> Fin m -> Real :=
  fun i j => ch7InverseLinearizedEntry m G_inv D i j

noncomputable def higham21Eq21_7InverseQuadraticCoefficient
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv : Fin m -> Fin m -> Real) (rho beta : Real) : Real :=
  let Ebar := higham21Eq21_7GramAbsEnvelope A DeltaA rho
  let P := ch7InverseFirstProductSensitivity m G_inv Ebar
  frobNorm P ^ 2 * beta

noncomputable def higham21Eq21_7InverseDifferenceCoefficient
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv : Fin m -> Fin m -> Real) (rho beta : Real) : Real :=
  let H := higham21Eq21_7GramLinear A DeltaA
  let K := higham21Eq21_7GramQuadratic DeltaA
  let LH := higham21Eq21_7LinearizedMatrix G_inv H
  let LK := higham21Eq21_7LinearizedMatrix G_inv K
  frobNorm LH + rho * frobNorm LK +
    rho * higham21Eq21_7InverseQuadraticCoefficient
      A DeltaA G_inv rho beta

noncomputable def higham21Eq21_7CancellationCoefficient
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv : Fin m -> Fin m -> Real) (rho beta : Real) : Real :=
  let K := higham21Eq21_7GramQuadratic DeltaA
  let LK := higham21Eq21_7LinearizedMatrix G_inv K
  frobNorm LK +
    higham21Eq21_7InverseQuadraticCoefficient A DeltaA G_inv rho beta

noncomputable def higham21Eq21_7InverseDifferenceMatrix
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real) (t : Real) :
    Fin m -> Fin m -> Real :=
  higham21Eq21_7GramInverseDifferenceModel G_inv
    (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv

noncomputable def higham21Eq21_7CancellationMatrix
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real) (t : Real) :
    Fin m -> Fin m -> Real :=
  let dG := higham21Eq21_7InverseDifferenceMatrix
    A DeltaA G_inv G_t_inv t
  let H := higham21Eq21_7GramLinear A DeltaA
  let LH := higham21Eq21_7LinearizedMatrix G_inv H
  fun i j => dG i j + t * LH i j

/-- A fixed-neighborhood coefficient for the exact remainder in Higham,
    Chapter 21, equation (21.7).  It depends on uniform bounds for the
    perturbed Gram inverse, but not on the perturbation parameter `t`. -/
noncomputable def higham21Eq21_7FixedRadiusCoefficient
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (G_inv : Fin m -> Fin m -> Real)
    (rho beta : Real) : Real :=
  let dC := higham21Eq21_7InverseDifferenceCoefficient
    A DeltaA G_inv rho beta
  let qC := higham21Eq21_7CancellationCoefficient
    A DeltaA G_inv rho beta
  frobNormRect A * qC * vecNorm2 b +
    frobNormRect DeltaA * dC * vecNorm2 b +
    frobNormRect A * dC * vecNorm2 Deltab +
    frobNormRect DeltaA * beta * vecNorm2 Deltab

theorem higham21Eq21_7_gramPerturbation_abs_le_fixed_radius
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (rho t : Real) (hrho : 0 <= rho) (ht : |t| <= rho) :
    forall i j,
      |higham21Eq21_7GramPerturbation A DeltaA t i j| <=
        |t| * higham21Eq21_7GramAbsEnvelope A DeltaA rho i j := by
  intro i j
  let H := higham21Eq21_7GramLinear A DeltaA
  let K := higham21Eq21_7GramQuadratic DeltaA
  have ht0 : 0 <= |t| := abs_nonneg t
  have hK0 : 0 <= |K i j| := abs_nonneg _
  calc
    |higham21Eq21_7GramPerturbation A DeltaA t i j|
        = |t * H i j + t ^ 2 * K i j| := by
            rfl
    _ <= |t * H i j| + |t ^ 2 * K i j| := abs_add_le _ _
    _ = |t| * |H i j| + |t| ^ 2 * |K i j| := by
          rw [abs_mul, abs_mul, abs_pow]
    _ <= |t| * |H i j| + (|t| * rho) * |K i j| := by
          have hsq : |t| ^ 2 <= |t| * rho := by
            calc
              |t| ^ 2 = |t| * |t| := by ring
              _ <= |t| * rho := mul_le_mul_of_nonneg_left ht ht0
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hsq hK0)
    _ = |t| * higham21Eq21_7GramAbsEnvelope A DeltaA rho i j := by
          simp only [higham21Eq21_7GramAbsEnvelope]
          change |t| * |H i j| + (|t| * rho) * |K i j| =
            |t| * (|H i j| + rho * |K i j|)
          ring

theorem higham21Eq21_7_linearized_gramPerturbation
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv : Fin m -> Fin m -> Real) (t : Real) :
    higham21Eq21_7LinearizedMatrix G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) =
      fun i j =>
        t * higham21Eq21_7LinearizedMatrix G_inv
              (higham21Eq21_7GramLinear A DeltaA) i j +
          t ^ 2 * higham21Eq21_7LinearizedMatrix G_inv
              (higham21Eq21_7GramQuadratic DeltaA) i j := by
  ext i j
  simp only [higham21Eq21_7LinearizedMatrix,
    ch7InverseLinearizedEntry, higham21Eq21_7GramPerturbation]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  apply congrArg₂ (fun x y : Real => x + y)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring

theorem higham21Eq21_7_inverseDifference_decomposition
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real) (t : Real) :
    higham21Eq21_7GramInverseDifferenceModel G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv =
      fun i j =>
        -(t * higham21Eq21_7LinearizedMatrix G_inv
              (higham21Eq21_7GramLinear A DeltaA) i j +
            t ^ 2 * higham21Eq21_7LinearizedMatrix G_inv
              (higham21Eq21_7GramQuadratic DeltaA) i j) +
          ch7InverseQuadraticRemainderEntry m G_inv
            (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv i j := by
  have hlin :=
    higham21Eq21_7_linearized_gramPerturbation A DeltaA G_inv t
  ext i j
  have hlinij := congrFun (congrFun hlin i) j
  simp only [higham21Eq21_7GramInverseDifferenceModel]
  rw [show ch7InverseLinearizedEntry m G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) i j =
      higham21Eq21_7LinearizedMatrix G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) i j by rfl]
  rw [hlinij]

set_option maxHeartbeats 800000 in
theorem higham21Eq21_7_inverseQuadraticRemainder_frobNorm_le_fixed_radius
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real)
    (rho beta t : Real) (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (ht : |t| <= rho) (hG_t_inv : frobNorm G_t_inv <= beta) :
    frobNorm
        (fun i j =>
          ch7InverseQuadraticRemainderEntry m G_inv
            (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv i j) <=
      |t| ^ 2 *
        (frobNorm
            (ch7InverseFirstProductSensitivity m G_inv
              (higham21Eq21_7GramAbsEnvelope A DeltaA rho)) ^ 2 * beta) := by
  let E := higham21Eq21_7GramPerturbation A DeltaA t
  let Ebar := higham21Eq21_7GramAbsEnvelope A DeltaA rho
  let P := ch7InverseFirstProductSensitivity m G_inv Ebar
  let R : Fin m -> Fin m -> Real :=
    fun i j => ch7InverseQuadraticRemainderEntry m G_inv E G_t_inv i j
  let S : Fin m -> Fin m -> Real :=
    fun i j =>
      ch7InverseQuadraticRemainderSensitivityEntry m G_inv Ebar G_t_inv i j
  have hEbar : forall i j, 0 <= Ebar i j := by
    intro i j
    dsimp [Ebar, higham21Eq21_7GramAbsEnvelope]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg hrho (abs_nonneg _))
  have hE : forall i j, |E i j| <= |t| * Ebar i j := by
    intro i j
    exact higham21Eq21_7_gramPerturbation_abs_le_fixed_radius
      A DeltaA rho t hrho ht i j
  have hRentry : forall i j, |R i j| <= |t| ^ 2 * S i j := by
    intro i j
    exact ch7InverseQuadraticRemainderEntry_abs_le m G_inv E Ebar G_t_inv
      |t| (abs_nonneg t) hEbar hE i j
  have hSnonneg : forall i j, 0 <= S i j := by
    intro i j
    exact ch7InverseQuadraticRemainderSensitivityEntry_nonneg
      m G_inv Ebar G_t_inv hEbar i j
  have hRnorm : frobNorm R <= |t| ^ 2 * frobNorm S := by
    apply frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      R S (sq_nonneg |t|)
    intro i j
    simpa [abs_of_nonneg (hSnonneg i j)] using hRentry i j
  have hAbsG : frobNorm (absMatrix m G_t_inv) = frobNorm G_t_inv := by
    rw [← frobNormRect_eq_frobNormFn, ← frobNormRect_eq_frobNormFn]
    simpa [absMatrix] using (frobNormRect_abs G_t_inv)
  have hinner :
      frobNorm (matMul m P (absMatrix m G_t_inv)) <=
        frobNorm P * frobNorm G_t_inv := by
    calc
      frobNorm (matMul m P (absMatrix m G_t_inv)) <=
          frobNorm P * frobNorm (absMatrix m G_t_inv) :=
        frobNorm_matMul_le P (absMatrix m G_t_inv)
      _ = frobNorm P * frobNorm G_t_inv := by rw [hAbsG]
  have hSnorm : frobNorm S <= frobNorm P ^ 2 * beta := by
    calc
      frobNorm S =
          frobNorm (matMul m P (matMul m P (absMatrix m G_t_inv))) := by
            rfl
      _ <= frobNorm P *
            frobNorm (matMul m P (absMatrix m G_t_inv)) :=
          frobNorm_matMul_le P (matMul m P (absMatrix m G_t_inv))
      _ <= frobNorm P * (frobNorm P * frobNorm G_t_inv) :=
          mul_le_mul_of_nonneg_left hinner (frobNorm_nonneg P)
      _ <= frobNorm P * (frobNorm P * beta) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hG_t_inv (frobNorm_nonneg P))
            (frobNorm_nonneg P)
      _ = frobNorm P ^ 2 * beta := by ring
  change frobNorm R <= |t| ^ 2 * (frobNorm P ^ 2 * beta)
  exact le_trans hRnorm
    (mul_le_mul_of_nonneg_left hSnorm (sq_nonneg |t|))

set_option maxHeartbeats 800000 in
theorem higham21Eq21_7_inverseDifference_frobNorm_le_fixed_radius
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real)
    (rho beta t : Real) (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (ht : |t| <= rho) (hG_t_inv : frobNorm G_t_inv <= beta) :
    frobNorm
        (higham21Eq21_7GramInverseDifferenceModel G_inv
          (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv) <=
      |t| * higham21Eq21_7InverseDifferenceCoefficient
        A DeltaA G_inv rho beta := by
  let H := higham21Eq21_7GramLinear A DeltaA
  let K := higham21Eq21_7GramQuadratic DeltaA
  let LH := higham21Eq21_7LinearizedMatrix G_inv H
  let LK := higham21Eq21_7LinearizedMatrix G_inv K
  let R : Fin m -> Fin m -> Real :=
    fun i j =>
      ch7InverseQuadraticRemainderEntry m G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv i j
  let rC := higham21Eq21_7InverseQuadraticCoefficient
    A DeltaA G_inv rho beta
  have hrC : 0 <= rC := by
    dsimp [rC, higham21Eq21_7InverseQuadraticCoefficient]
    exact mul_nonneg (sq_nonneg _) hbeta
  have hsmul : forall (a : Real) (M : Fin m -> Fin m -> Real),
      frobNorm (fun i j => a * M i j) = |a| * frobNorm M := by
    intro a M
    rw [← frobNormRect_eq_frobNormFn, ← frobNormRect_eq_frobNormFn]
    exact frobNormRect_smul a M
  have hlinNorm :
      frobNorm (fun i j => t * LH i j + t ^ 2 * LK i j) <=
        |t| * (frobNorm LH + rho * frobNorm LK) := by
    calc
      frobNorm (fun i j => t * LH i j + t ^ 2 * LK i j) <=
          frobNorm (fun i j => t * LH i j) +
            frobNorm (fun i j => t ^ 2 * LK i j) :=
        frobNorm_add_le _ _
      _ = |t| * frobNorm LH + |t| ^ 2 * frobNorm LK := by
        rw [hsmul t LH, hsmul (t ^ 2) LK, abs_pow]
      _ <= |t| * frobNorm LH + (|t| * rho) * frobNorm LK := by
        have hsq : |t| ^ 2 <= |t| * rho := by
          calc
            |t| ^ 2 = |t| * |t| := by ring
            _ <= |t| * rho :=
              mul_le_mul_of_nonneg_left ht (abs_nonneg t)
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_right hsq (frobNorm_nonneg LK))
      _ = |t| * (frobNorm LH + rho * frobNorm LK) := by ring
  have hR : frobNorm R <= |t| ^ 2 * rC := by
    exact higham21Eq21_7_inverseQuadraticRemainder_frobNorm_le_fixed_radius
      A DeltaA G_inv G_t_inv rho beta t hrho hbeta ht hG_t_inv
  have hdecomp :=
    higham21Eq21_7_inverseDifference_decomposition
      A DeltaA G_inv G_t_inv t
  change frobNorm
      (higham21Eq21_7GramInverseDifferenceModel G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv) <= _
  rw [hdecomp]
  calc
    frobNorm
        (fun i j =>
          -(t * LH i j + t ^ 2 * LK i j) + R i j) <=
      frobNorm (fun i j => -(t * LH i j + t ^ 2 * LK i j)) +
        frobNorm R := frobNorm_add_le _ _
    _ = frobNorm (fun i j => t * LH i j + t ^ 2 * LK i j) +
        frobNorm R := by rw [frobNorm_neg]
    _ <= |t| * (frobNorm LH + rho * frobNorm LK) +
        |t| ^ 2 * rC := add_le_add hlinNorm hR
    _ <= |t| * (frobNorm LH + rho * frobNorm LK) +
        (|t| * rho) * rC := by
      have hsq : |t| ^ 2 <= |t| * rho := by
        calc
          |t| ^ 2 = |t| * |t| := by ring
          _ <= |t| * rho := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hsq hrC)
    _ = |t| * higham21Eq21_7InverseDifferenceCoefficient
          A DeltaA G_inv rho beta := by
      simp only [higham21Eq21_7InverseDifferenceCoefficient]
      change |t| * (frobNorm LH + rho * frobNorm LK) +
          (|t| * rho) * rC =
        |t| * (frobNorm LH + rho * frobNorm LK + rho * rC)
      ring

set_option maxHeartbeats 800000 in
theorem higham21Eq21_7_inverseDifference_cancellation_frobNorm_le_fixed_radius
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real)
    (rho beta t : Real) (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (ht : |t| <= rho) (hG_t_inv : frobNorm G_t_inv <= beta) :
    frobNorm
        (fun i j =>
          higham21Eq21_7GramInverseDifferenceModel G_inv
              (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv i j +
            t * higham21Eq21_7LinearizedMatrix G_inv
              (higham21Eq21_7GramLinear A DeltaA) i j) <=
      |t| ^ 2 * higham21Eq21_7CancellationCoefficient
        A DeltaA G_inv rho beta := by
  let H := higham21Eq21_7GramLinear A DeltaA
  let K := higham21Eq21_7GramQuadratic DeltaA
  let LH := higham21Eq21_7LinearizedMatrix G_inv H
  let LK := higham21Eq21_7LinearizedMatrix G_inv K
  let R : Fin m -> Fin m -> Real :=
    fun i j =>
      ch7InverseQuadraticRemainderEntry m G_inv
        (higham21Eq21_7GramPerturbation A DeltaA t) G_t_inv i j
  let rC := higham21Eq21_7InverseQuadraticCoefficient
    A DeltaA G_inv rho beta
  have hsmul : forall (a : Real) (M : Fin m -> Fin m -> Real),
      frobNorm (fun i j => a * M i j) = |a| * frobNorm M := by
    intro a M
    rw [← frobNormRect_eq_frobNormFn, ← frobNormRect_eq_frobNormFn]
    exact frobNormRect_smul a M
  have hR : frobNorm R <= |t| ^ 2 * rC := by
    exact higham21Eq21_7_inverseQuadraticRemainder_frobNorm_le_fixed_radius
      A DeltaA G_inv G_t_inv rho beta t hrho hbeta ht hG_t_inv
  have hdecomp :=
    higham21Eq21_7_inverseDifference_decomposition
      A DeltaA G_inv G_t_inv t
  rw [hdecomp]
  change frobNorm
      (fun i j =>
        (-(t * LH i j + t ^ 2 * LK i j) + R i j) + t * LH i j) <= _
  have hcancel :
      (fun i j =>
        (-(t * LH i j + t ^ 2 * LK i j) + R i j) + t * LH i j) =
        fun i j => -(t ^ 2 * LK i j) + R i j := by
    ext i j
    ring
  rw [hcancel]
  calc
    frobNorm (fun i j => -(t ^ 2 * LK i j) + R i j) <=
        frobNorm (fun i j => -(t ^ 2 * LK i j)) + frobNorm R :=
      frobNorm_add_le _ _
    _ = |t| ^ 2 * frobNorm LK + frobNorm R := by
      rw [frobNorm_neg, hsmul (t ^ 2) LK, abs_pow]
    _ <= |t| ^ 2 * frobNorm LK + |t| ^ 2 * rC :=
      add_le_add (le_refl _) hR
    _ = |t| ^ 2 * higham21Eq21_7CancellationCoefficient
          A DeltaA G_inv rho beta := by
      simp only [higham21Eq21_7CancellationCoefficient]
      change |t| ^ 2 * frobNorm LK + |t| ^ 2 * rC =
        |t| ^ 2 * (frobNorm LK + rC)
      ring

theorem higham21Eq21_7_matMulVec_matrix_const_mul
    {m : Nat} (M : Fin m -> Fin m -> Real)
    (t : Real) (x : Fin m -> Real) :
    matMulVec m (fun i j => t * M i j) x =
      fun i => t * matMulVec m M x i := by
  ext i
  unfold matMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

set_option maxHeartbeats 800000 in
theorem higham21Eq21_7_exactRemainder_four_term_decomposition
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real) (t : Real) :
    higham21Eq21_7ExactRemainder
        A DeltaA b Deltab G_inv G_t_inv t =
      fun j =>
        (((rectTransposeMulVec A
              (matMulVec m
                (higham21Eq21_7CancellationMatrix
                  A DeltaA G_inv G_t_inv t) b) j +
            t * rectTransposeMulVec DeltaA
              (matMulVec m
                (higham21Eq21_7InverseDifferenceMatrix
                  A DeltaA G_inv G_t_inv t) b) j) +
          t * rectTransposeMulVec A
            (matMulVec m
              (higham21Eq21_7InverseDifferenceMatrix
                A DeltaA G_inv G_t_inv t) Deltab) j) +
        t ^ 2 * rectTransposeMulVec DeltaA
          (matMulVec m G_t_inv Deltab) j) := by
  let H := higham21Eq21_7GramLinear A DeltaA
  let dG := higham21Eq21_7InverseDifferenceMatrix
    A DeltaA G_inv G_t_inv t
  let LH := higham21Eq21_7LinearizedMatrix G_inv H
  let qMat := higham21Eq21_7CancellationMatrix
    A DeltaA G_inv G_t_inv t
  have hLHmat : LH = matMul m (matMul m G_inv H) G_inv := by
    ext i j
    exact ch7InverseLinearizedEntry_eq_matMul m G_inv H i j
  have hLHb :
      matMulVec m LH b =
        matMulVec m G_inv (matMulVec m H (matMulVec m G_inv b)) := by
    rw [hLHmat]
    ext i
    rw [matMulVec_matMul m (matMul m G_inv H) G_inv b i]
    rw [matMulVec_matMul m G_inv H (matMulVec m G_inv b) i]
  have hqAction :
      matMulVec m qMat b =
        fun i => matMulVec m dG b i + t * matMulVec m LH b i := by
    change matMulVec m (fun i j => dG i j + t * LH i j) b = _
    rw [matMulVec_add_left]
    rw [higham21Eq21_7_matMulVec_matrix_const_mul]
  have hcombine :
      rectTransposeMulVec A (matMulVec m qMat b) =
        fun j =>
          rectTransposeMulVec A (matMulVec m dG b) j +
            t * rectTransposeMulVec A
              (matMulVec m G_inv
                (matMulVec m H (matMulVec m G_inv b))) j := by
    rw [hqAction]
    rw [higham21Eq21_7_rectTransposeMulVec_add]
    rw [higham21Eq21_7_rectTransposeMulVec_const_mul]
    rw [hLHb]
  ext j
  have hj := congrFun hcombine j
  change
    rectTransposeMulVec A (matMulVec m dG b) j +
        t * rectTransposeMulVec DeltaA (matMulVec m dG b) j +
        t * rectTransposeMulVec A (matMulVec m dG Deltab) j +
        t ^ 2 * rectTransposeMulVec DeltaA
          (matMulVec m G_t_inv Deltab) j +
        t * rectTransposeMulVec A
          (matMulVec m G_inv
            (matMulVec m H (matMulVec m G_inv b))) j =
      (((rectTransposeMulVec A (matMulVec m qMat b) j +
            t * rectTransposeMulVec DeltaA (matMulVec m dG b) j) +
          t * rectTransposeMulVec A (matMulVec m dG Deltab) j) +
        t ^ 2 * rectTransposeMulVec DeltaA
          (matMulVec m G_t_inv Deltab) j)
  calc
    rectTransposeMulVec A (matMulVec m dG b) j +
          t * rectTransposeMulVec DeltaA (matMulVec m dG b) j +
          t * rectTransposeMulVec A (matMulVec m dG Deltab) j +
          t ^ 2 * rectTransposeMulVec DeltaA
            (matMulVec m G_t_inv Deltab) j +
          t * rectTransposeMulVec A
            (matMulVec m G_inv
              (matMulVec m H (matMulVec m G_inv b))) j =
        (((rectTransposeMulVec A (matMulVec m dG b) j +
              t * rectTransposeMulVec A
                (matMulVec m G_inv
                  (matMulVec m H (matMulVec m G_inv b))) j) +
            t * rectTransposeMulVec DeltaA (matMulVec m dG b) j) +
          t * rectTransposeMulVec A (matMulVec m dG Deltab) j) +
        t ^ 2 * rectTransposeMulVec DeltaA
          (matMulVec m G_t_inv Deltab) j := by ring
    _ = (((rectTransposeMulVec A (matMulVec m qMat b) j +
            t * rectTransposeMulVec DeltaA (matMulVec m dG b) j) +
          t * rectTransposeMulVec A (matMulVec m dG Deltab) j) +
        t ^ 2 * rectTransposeMulVec DeltaA
          (matMulVec m G_t_inv Deltab) j) := by rw [hj]

set_option maxHeartbeats 5000000
/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.7): the exact
    finite remainder is bounded by `|t|^2` times an explicit fixed-radius
    coefficient whenever the perturbed Gram inverses are uniformly bounded. -/
theorem higham21Eq21_7_exactRemainder_vecNorm2_le_fixed_radius
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (G_inv G_t_inv : Fin m -> Fin m -> Real)
    (rho beta t : Real) (hrho : 0 <= rho) (hbeta : 0 <= beta)
    (ht : |t| <= rho) (hG_t_inv : frobNorm G_t_inv <= beta) :
    vecNorm2
        (higham21Eq21_7ExactRemainder
          A DeltaA b Deltab G_inv G_t_inv t) <=
      |t| ^ 2 * higham21Eq21_7FixedRadiusCoefficient
        A DeltaA b Deltab G_inv rho beta := by
  let dG := higham21Eq21_7InverseDifferenceMatrix
    A DeltaA G_inv G_t_inv t
  let qMat := higham21Eq21_7CancellationMatrix
    A DeltaA G_inv G_t_inv t
  let dC := higham21Eq21_7InverseDifferenceCoefficient
    A DeltaA G_inv rho beta
  let qC := higham21Eq21_7CancellationCoefficient
    A DeltaA G_inv rho beta
  have hDnorm : frobNorm dG <= |t| * dC := by
    simpa [dG, higham21Eq21_7InverseDifferenceMatrix] using
      (higham21Eq21_7_inverseDifference_frobNorm_le_fixed_radius
        A DeltaA G_inv G_t_inv rho beta t hrho hbeta ht hG_t_inv)
  have hQnorm : frobNorm qMat <= |t| ^ 2 * qC := by
    simpa [qMat, higham21Eq21_7CancellationMatrix,
      higham21Eq21_7InverseDifferenceMatrix] using
      higham21Eq21_7_inverseDifference_cancellation_frobNorm_le_fixed_radius
        A DeltaA G_inv G_t_inv rho beta t hrho hbeta ht hG_t_inv
  let v0 : Fin n -> Real :=
    rectTransposeMulVec A (matMulVec m qMat b)
  let v1 : Fin n -> Real :=
    fun j => t * rectTransposeMulVec DeltaA (matMulVec m dG b) j
  let v2 : Fin n -> Real :=
    fun j => t * rectTransposeMulVec A (matMulVec m dG Deltab) j
  let v3 : Fin n -> Real :=
    fun j => t ^ 2 *
      rectTransposeMulVec DeltaA (matMulVec m G_t_inv Deltab) j
  have hrem :
      higham21Eq21_7ExactRemainder
          A DeltaA b Deltab G_inv G_t_inv t =
        fun j => ((v0 j + v1 j) + v2 j) + v3 j := by
    simpa [v0, v1, v2, v3, dG, qMat] using
      (higham21Eq21_7_exactRemainder_four_term_decomposition
        A DeltaA b Deltab G_inv G_t_inv t)
  have hv0 : vecNorm2 v0 <=
      |t| ^ 2 * (frobNormRect A * qC * vecNorm2 b) := by
    calc
      vecNorm2 v0 <=
          frobNormRect A * vecNorm2 (matMulVec m qMat b) := by
        exact vecNorm2_rectMatMulVec_finiteTranspose_le_frobNormRect_mul
          A (matMulVec m qMat b)
      _ <= frobNormRect A * (frobNorm qMat * vecNorm2 b) :=
        mul_le_mul_of_nonneg_left
          (vecNorm2_matMulVec_le_frobNorm_mul qMat b)
          (frobNormRect_nonneg A)
      _ <= frobNormRect A * ((|t| ^ 2 * qC) * vecNorm2 b) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hQnorm (vecNorm2_nonneg b))
          (frobNormRect_nonneg A)
      _ = |t| ^ 2 * (frobNormRect A * qC * vecNorm2 b) := by ring
  have hv1 : vecNorm2 v1 <=
      |t| ^ 2 * (frobNormRect DeltaA * dC * vecNorm2 b) := by
    calc
      vecNorm2 v1 = |t| *
          vecNorm2 (rectTransposeMulVec DeltaA (matMulVec m dG b)) := by
        exact vecNorm2_smul t _
      _ <= |t| * (frobNormRect DeltaA * vecNorm2 (matMulVec m dG b)) :=
        mul_le_mul_of_nonneg_left
          (vecNorm2_rectMatMulVec_finiteTranspose_le_frobNormRect_mul
            DeltaA (matMulVec m dG b)) (abs_nonneg t)
      _ <= |t| *
          (frobNormRect DeltaA * (frobNorm dG * vecNorm2 b)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (vecNorm2_matMulVec_le_frobNorm_mul dG b)
            (frobNormRect_nonneg DeltaA)) (abs_nonneg t)
      _ <= |t| *
          (frobNormRect DeltaA * ((|t| * dC) * vecNorm2 b)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hDnorm (vecNorm2_nonneg b))
            (frobNormRect_nonneg DeltaA)) (abs_nonneg t)
      _ = |t| ^ 2 * (frobNormRect DeltaA * dC * vecNorm2 b) := by ring
  have hv2 : vecNorm2 v2 <=
      |t| ^ 2 * (frobNormRect A * dC * vecNorm2 Deltab) := by
    calc
      vecNorm2 v2 = |t| *
          vecNorm2 (rectTransposeMulVec A (matMulVec m dG Deltab)) := by
        exact vecNorm2_smul t _
      _ <= |t| * (frobNormRect A * vecNorm2 (matMulVec m dG Deltab)) :=
        mul_le_mul_of_nonneg_left
          (vecNorm2_rectMatMulVec_finiteTranspose_le_frobNormRect_mul
            A (matMulVec m dG Deltab)) (abs_nonneg t)
      _ <= |t| *
          (frobNormRect A * (frobNorm dG * vecNorm2 Deltab)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (vecNorm2_matMulVec_le_frobNorm_mul dG Deltab)
            (frobNormRect_nonneg A)) (abs_nonneg t)
      _ <= |t| *
          (frobNormRect A * ((|t| * dC) * vecNorm2 Deltab)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hDnorm (vecNorm2_nonneg Deltab))
            (frobNormRect_nonneg A)) (abs_nonneg t)
      _ = |t| ^ 2 * (frobNormRect A * dC * vecNorm2 Deltab) := by ring
  have hv3 : vecNorm2 v3 <=
      |t| ^ 2 * (frobNormRect DeltaA * beta * vecNorm2 Deltab) := by
    calc
      vecNorm2 v3 = |t ^ 2| *
          vecNorm2 (rectTransposeMulVec DeltaA
            (matMulVec m G_t_inv Deltab)) := by
        exact vecNorm2_smul (t ^ 2) _
      _ = |t| ^ 2 *
          vecNorm2 (rectTransposeMulVec DeltaA
            (matMulVec m G_t_inv Deltab)) := by rw [abs_pow]
      _ <= |t| ^ 2 *
          (frobNormRect DeltaA * vecNorm2 (matMulVec m G_t_inv Deltab)) :=
        mul_le_mul_of_nonneg_left
          (vecNorm2_rectMatMulVec_finiteTranspose_le_frobNormRect_mul
            DeltaA (matMulVec m G_t_inv Deltab)) (sq_nonneg |t|)
      _ <= |t| ^ 2 *
          (frobNormRect DeltaA * (frobNorm G_t_inv * vecNorm2 Deltab)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (vecNorm2_matMulVec_le_frobNorm_mul G_t_inv Deltab)
            (frobNormRect_nonneg DeltaA)) (sq_nonneg |t|)
      _ <= |t| ^ 2 *
          (frobNormRect DeltaA * (beta * vecNorm2 Deltab)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hG_t_inv (vecNorm2_nonneg Deltab))
            (frobNormRect_nonneg DeltaA)) (sq_nonneg |t|)
      _ = |t| ^ 2 *
          (frobNormRect DeltaA * beta * vecNorm2 Deltab) := by ring
  rw [hrem]
  calc
    vecNorm2 (fun j => ((v0 j + v1 j) + v2 j) + v3 j) <=
        vecNorm2 (fun j => (v0 j + v1 j) + v2 j) + vecNorm2 v3 :=
      vecNorm2_add_le _ _
    _ <= (vecNorm2 (fun j => v0 j + v1 j) + vecNorm2 v2) +
        vecNorm2 v3 :=
      by
        have h012 := vecNorm2_add_le (fun j => v0 j + v1 j) v2
        nlinarith
    _ <= ((vecNorm2 v0 + vecNorm2 v1) + vecNorm2 v2) +
        vecNorm2 v3 :=
      by
        have h01 := vecNorm2_add_le v0 v1
        nlinarith
    _ <=
        ((|t| ^ 2 * (frobNormRect A * qC * vecNorm2 b) +
            |t| ^ 2 * (frobNormRect DeltaA * dC * vecNorm2 b)) +
          |t| ^ 2 * (frobNormRect A * dC * vecNorm2 Deltab)) +
        |t| ^ 2 * (frobNormRect DeltaA * beta * vecNorm2 Deltab) :=
      add_le_add (add_le_add (add_le_add hv0 hv1) hv2) hv3
    _ = |t| ^ 2 * higham21Eq21_7FixedRadiusCoefficient
          A DeltaA b Deltab G_inv rho beta := by
      simp only [higham21Eq21_7FixedRadiusCoefficient]
      change
        ((|t| ^ 2 * (frobNormRect A * qC * vecNorm2 b) +
              |t| ^ 2 * (frobNormRect DeltaA * dC * vecNorm2 b)) +
            |t| ^ 2 * (frobNormRect A * dC * vecNorm2 Deltab)) +
          |t| ^ 2 * (frobNormRect DeltaA * beta * vecNorm2 Deltab) =
        |t| ^ 2 *
          (frobNormRect A * qC * vecNorm2 b +
            frobNormRect DeltaA * dC * vecNorm2 b +
            frobNormRect A * dC * vecNorm2 Deltab +
            frobNormRect DeltaA * beta * vecNorm2 Deltab)
      ring

/-- Higham, 2nd ed., Chapter 21, Theorem 21.1, equation (21.7): the exact
    remainder is `O(t^2)` for any locally uniformly bounded family of
    perturbed Gram inverses. -/
theorem higham21Eq21_7_exactRemainder_vecNorm2_isBigO
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (G_inv : Fin m -> Fin m -> Real)
    (G_t_inv : Real -> Fin m -> Fin m -> Real)
    (rho beta : Real) (hrho : 0 < rho) (hbeta : 0 <= beta)
    (hG_t_inv : forall t, |t| <= rho -> frobNorm (G_t_inv t) <= beta) :
    (fun t =>
      vecNorm2
        (higham21Eq21_7ExactRemainder
          A DeltaA b Deltab G_inv (G_t_inv t) t)) =O[nhds 0]
      (fun t : Real => t ^ 2) := by
  let C := higham21Eq21_7FixedRadiusCoefficient
    A DeltaA b Deltab G_inv rho beta
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (0 : Real) hrho] with t ht
  have htlt : |t| < rho := by
    simpa [Real.dist_eq] using ht
  have hquad :=
    higham21Eq21_7_exactRemainder_vecNorm2_le_fixed_radius
      A DeltaA b Deltab G_inv (G_t_inv t) rho beta t hrho.le hbeta
        htlt.le (hG_t_inv t htlt.le)
  calc
    norm
        (vecNorm2
          (higham21Eq21_7ExactRemainder
            A DeltaA b Deltab G_inv (G_t_inv t) t)) =
        vecNorm2
          (higham21Eq21_7ExactRemainder
            A DeltaA b Deltab G_inv (G_t_inv t) t) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (vecNorm2_nonneg _)]
    _ <= |t| ^ 2 * C := by simpa [C] using hquad
    _ = C * norm (t ^ 2) := by
      rw [Real.norm_eq_abs, abs_pow]
      ring



end Higham21Eq21_7QuadraticRemainder


-- ============================================================
-- §21.2  Lemma 21.2 projector/norm bridge
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-facing right-projector mixture for the Kielbasinski--Schwetlick
    construction.  The projector acts on the solution vector `x`, as in the
    printed formula `DeltaA = DeltaA1 P + DeltaA2 (I - P)`.  This is the
    constructed perturbation block, not the full minimum-norm symmetrization
    theorem. -/
noncomputable abbrev undetLemma21_2SymmetrizedPerturbation {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  finiteTranspose
    (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))

/-- Nonzero vectors have nonzero squared Euclidean norm.  This local helper lets
    the Chapter 21 Lemma 21.2 wrapper branch on the source proof's `x = 0`
    case while feeding the existing nonzero beta/projector route. -/
theorem higham21_vecNorm2Sq_ne_zero_of_ne_zero {n : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    vecNorm2Sq x ≠ 0 := by
  intro hsq
  apply hx
  ext i
  have hall :
      ∀ j : Fin n, j ∈ (Finset.univ : Finset (Fin n)) →
        x j ^ 2 = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => x j ^ 2)
        (by intro j _; exact sq_nonneg (x j))).mp
        (by simpa [vecNorm2Sq] using hsq)
  have hxi2 : x i ^ 2 = 0 := hall i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hxi2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-case perturbation.  The proof takes `DeltaA = DeltaA2` when the
    candidate solution `x` is zero; otherwise it uses the right-projector
    mixture already represented by `undetLemma21_2SymmetrizedPerturbation`. -/
noncomputable def undetLemma21_2SinglePerturbation {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  if x = 0 then DeltaA2 else undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the transposed Chapter 20 construction is exactly the right-projector
    mixture `DeltaA1 P + DeltaA2 (I - P)` used in the proof. -/
theorem higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
      matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
  have hmix :=
    lsLemma20_6Perturbation_eq_projector_mixture
      x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1) j i
  have hrightQ :
      matMulRectLeft (lsLemma20_6ProjectorComplement x) (finiteTranspose DeltaA2) j i =
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
    unfold matMulRectLeft matMulRectRight finiteTranspose
    apply Finset.sum_congr rfl
    intro k _
    rw [lsLemma20_6ProjectorComplement_symmetric x j k]
    ring
  have hrightP :
      matMulRectLeft (lsLemma20_6Projector x) (finiteTranspose DeltaA1) j i =
        matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j := by
    unfold matMulRectLeft matMulRectRight finiteTranspose
    apply Finset.sum_congr rfl
    intro k _
    rw [lsLemma20_6Projector_symmetric x j k]
    ring
  calc
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
        lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1) j i := rfl
    _ = matMulRectLeft (lsLemma20_6ProjectorComplement x) (finiteTranspose DeltaA2) j i +
          matMulRectLeft (lsLemma20_6Projector x) (finiteTranspose DeltaA1) j i := hmix
    _ = matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j +
          matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j := by
          rw [hrightQ, hrightP]
    _ = matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
          matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the two source perturbation slots are the same matrix, then the
    source-case single perturbation collapses back to that matrix. -/
theorem higham21_lemma21_2_single_perturbation_same {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ) :
    undetLemma21_2SinglePerturbation x DeltaA DeltaA = DeltaA := by
  by_cases hx : x = 0
  · simp [undetLemma21_2SinglePerturbation, hx]
  · ext i j
    calc
      undetLemma21_2SinglePerturbation x DeltaA DeltaA i j =
          undetLemma21_2SymmetrizedPerturbation x DeltaA DeltaA i j := by
            simp [undetLemma21_2SinglePerturbation, hx]
      _ =
          matMulRectRight DeltaA (lsLemma20_6Projector x) i j +
            matMulRectRight DeltaA (lsLemma20_6ProjectorComplement x) i j :=
            higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
              x DeltaA DeltaA i j
      _ =
          matMulRectRight DeltaA
            (fun a b => lsLemma20_6Projector x a b +
              lsLemma20_6ProjectorComplement x a b) i j := by
            unfold matMulRectRight
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = matMulRectRight DeltaA (idMatrix n) i j := by
            unfold matMulRectRight
            apply Finset.sum_congr rfl
            intro k _
            simpa using
              congrArg (fun t : ℝ => DeltaA i k * t)
                (lsLemma20_6Projector_add_complement x k j)
      _ = DeltaA i j := by
            have h := congrFun (congrFun (rectMatMul_id_right DeltaA) i) j
            simpa [rectMatMul, matMulRectRight] using h

private theorem higham21_rectMatMulVec_matMulRectRight {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (matMulRectRight A V) x =
      rectMatMulVec A (matMulVec n V x) := by
  simpa [matMulRectRight, rectMatMul, rectMatMulVec, matMulVec] using
    (rectMatMulVec_rectMatMul A V x)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    for the source-oriented construction
    `DeltaA = DeltaA1 P + DeltaA2 (I-P)`, multiplying by the projector source
    vector `x` recovers the first perturbation action `DeltaA1 x`.  This is the
    algebraic step behind `(A + DeltaA)x = (A + DeltaA1)x = b`. -/
theorem higham21_lemma21_2_symmetrized_perturbation_mulVec_self_eq {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    rectMatMulVec (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) x =
      rectMatMulVec DeltaA1 x := by
  let P : Fin n → Fin n → ℝ := lsLemma20_6Projector x
  let Q : Fin n → Fin n → ℝ := lsLemma20_6ProjectorComplement x
  have hP : matMulVec n P x = x := by
    ext j
    simpa [P, matMulVec] using lsLemma20_6Projector_apply_self x hsq j
  have hQ : matMulVec n Q x = 0 := by
    simpa [Q] using lsLemma20_6ProjectorComplement_mulVec_self x hsq
  ext i
  calc
    rectMatMulVec (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) x i =
        rectMatMulVec
          (fun i j => matMulRectRight DeltaA1 P i j + matMulRectRight DeltaA2 Q i j) x i := by
          unfold rectMatMulVec
          apply Finset.sum_congr rfl
          intro j _
          rw [higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture]
    _ = rectMatMulVec (matMulRectRight DeltaA1 P) x i +
          rectMatMulVec (matMulRectRight DeltaA2 Q) x i := by
          unfold rectMatMulVec
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = rectMatMulVec DeltaA1 (matMulVec n P x) i +
          rectMatMulVec DeltaA2 (matMulVec n Q x) i := by
          rw [congrFun (higham21_rectMatMulVec_matMulRectRight DeltaA1 P x) i,
            congrFun (higham21_rectMatMulVec_matMulRectRight DeltaA2 Q x) i]
    _ = rectMatMulVec DeltaA1 x i := by
          rw [hP, hQ]
          simp [rectMatMulVec]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    system-action form of the previous identity.  The constructed perturbation
    has the same action on `x` as `DeltaA1`, so replacing `DeltaA1` by the
    symmetrized perturbation preserves the equation tested at `x`. -/
theorem higham21_lemma21_2_symmetrized_system_mulVec_self_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    rectMatMulVec
        (fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) x =
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x := by
  have hDelta :=
    higham21_lemma21_2_symmetrized_perturbation_mulVec_self_eq
      x hsq DeltaA1 DeltaA2
  ext i
  have hDelta_i := congrFun hDelta i
  unfold rectMatMulVec at hDelta_i ⊢
  calc
    (∑ j : Fin n,
        (A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) * x j)
        = (∑ j : Fin n, A i j * x j) +
            (∑ j : Fin n, undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j * x j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ j : Fin n, A i j * x j) + (∑ j : Fin n, DeltaA1 i j * x j) := by
          rw [hDelta_i]
    _ = ∑ j : Fin n, (A i j + DeltaA1 i j) * x j := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the first perturbed system `(A + DeltaA1)x = b` holds, then the
    source-oriented symmetrized perturbation also satisfies `(A + DeltaA)x = b`
    at the same vector `x`. -/
theorem higham21_lemma21_2_symmetrized_system_mulVec_self_of_deltaA1 {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b) :
    rectMatMulVec
        (fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) x =
      b := by
  rw [higham21_lemma21_2_symmetrized_system_mulVec_self_eq A x hsq DeltaA1 DeltaA2]
  exact hDeltaA1

/-- A zero right-hand side has the zero vector as a minimum 2-norm solution of
    any rectangular system. -/
theorem rectMinNormSolution_zero_of_rhs_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hb : b = 0) :
    RectMinNormSolution m n A b (0 : Fin n → ℝ) := by
  constructor
  · rw [hb]
    ext i
    simp [rectMatMulVec]
  · intro z _hz
    have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
      simpa using (vecNorm2_zero (n := n))
    rw [hzero]
    exact vecNorm2_nonneg z

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    zero-vector branch of the Kielbasinski--Schwetlick proof.  If the printed
    candidate `x` is zero, the source proof takes the single perturbation to be
    `DeltaA2`; the first perturbed equation then forces `b = 0`, so the zero
    vector is the minimum 2-norm solution for the `A + DeltaA2` system.

    This is only the `x = 0` branch.  The nonzero branch uses the projector
    mixture and beta argument below. -/
theorem higham21_lemma21_2_zero_branch_min_norm_of_deltaA2 {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hx : x = 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b) :
    RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x := by
  subst x
  have hb : b = 0 := by
    rw [← hDeltaA1]
    ext i
    simp [rectMatMulVec]
  exact rectMinNormSolution_zero_of_rhs_zero
    (fun i j => A i j + DeltaA2 i j) b hb

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the scalar `beta = 1 + x^T H^T y / x^T x`, where
    `H = DeltaA1 - DeltaA2`, used to rescale the dual vector in the proof. -/
noncomputable def undetLemma21_2Beta {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) : ℝ :=
  1 + (∑ j : Fin n,
    x j * rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y j) /
      vecNorm2Sq x

private theorem higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector
    {m n : ℕ}
    (x : Fin n → ℝ) (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j =
      DeltaA2 i j +
        matMulRectRight (fun i j => DeltaA1 i j - DeltaA2 i j)
          (lsLemma20_6Projector x) i j := by
  have hmix :=
    higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
      x DeltaA1 DeltaA2 i j
  have hid :
      (∑ k : Fin n, DeltaA2 i k * idMatrix n k j) = DeltaA2 i j := by
    have h := congrFun (congrFun (rectMatMul_id_right DeltaA2) i) j
    simpa [rectMatMul] using h
  rw [hmix]
  unfold matMulRectRight lsLemma20_6ProjectorComplement
  calc
    (∑ k : Fin n, DeltaA1 i k * lsLemma20_6Projector x k j) +
        ∑ k : Fin n, DeltaA2 i k * (idMatrix n k j - lsLemma20_6Projector x k j)
        = ∑ k : Fin n,
            (DeltaA2 i k * idMatrix n k j +
              (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k : Fin n, DeltaA2 i k * idMatrix n k j) +
            ∑ k : Fin n,
              (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j := by
          rw [Finset.sum_add_distrib]
    _ = DeltaA2 i j +
          ∑ k : Fin n,
            (DeltaA1 i k - DeltaA2 i k) * lsLemma20_6Projector x k j := by
          rw [hid]

private theorem higham21_matMulRectRight_projector_transpose_mulVec {m n : ℕ}
    (x : Fin n → ℝ) (H : Fin m → Fin n → ℝ) (y : Fin m → ℝ)
    (j : Fin n) :
    rectMatMulVec (finiteTranspose (matMulRectRight H (lsLemma20_6Projector x))) y j =
      ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
          vecNorm2Sq x) * x j := by
  unfold rectMatMulVec finiteTranspose matMulRectRight lsLemma20_6Projector
  calc
    (∑ i : Fin m, (∑ k : Fin n, H i k * (x k * x j / vecNorm2Sq x)) * y i)
        = ∑ i : Fin m, ∑ k : Fin n,
            (H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ k : Fin n, ∑ i : Fin m,
            (H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n,
          (∑ i : Fin m, H i k * y i) * (x k * x j / vecNorm2Sq x) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin n,
          (x k * (∑ i : Fin m, H i k * y i) / vecNorm2Sq x) * x j := by
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ((∑ k : Fin n, x k * (∑ i : Fin m, H i k * y i)) /
          vecNorm2Sq x) * x j := by
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.sum_div]
    _ = ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
          vecNorm2Sq x) * x j := by
          rfl

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    transposed-system action of the source-oriented projector construction.
    If `x = (A + DeltaA2)^T y`, then
    `(A + DeltaA)^T y = beta x`, where
    `DeltaA = DeltaA1 P + DeltaA2 (I-P)` and
    `beta = 1 + x^T (DeltaA1 - DeltaA2)^T y / x^T x`.

    This is the algebraic step before the source proof shows `beta ≠ 0` and
    sets the new dual vector to `beta^{-1} y`; it does not prove positivity of
    `beta` or the final minimum-norm symmetrization theorem. -/
theorem higham21_lemma21_2_symmetrized_transpose_mulVec_eq_beta_smul {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x) :
    rectMatMulVec
        (finiteTranspose
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)) y =
      fun j : Fin n => undetLemma21_2Beta x DeltaA1 DeltaA2 y * x j := by
  let H : Fin m → Fin n → ℝ := fun i j => DeltaA1 i j - DeltaA2 i j
  ext j
  have hDeltaA2_j := congrFun hDeltaA2 j
  have hcorr :=
    higham21_matMulRectRight_projector_transpose_mulVec x H y j
  unfold rectMatMulVec finiteTranspose at hDeltaA2_j ⊢
  calc
    (∑ i : Fin m,
        (A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) * y i)
        = (∑ i : Fin m, (A i j + DeltaA2 i j) * y i) +
            ∑ i : Fin m, matMulRectRight H (lsLemma20_6Projector x) i j * y i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector]
          ring
    _ = x j +
          ((∑ k : Fin n, x k * rectMatMulVec (finiteTranspose H) y k) /
            vecNorm2Sq x) * x j := by
          rw [hDeltaA2_j]
          rw [← hcorr]
          rfl
    _ = undetLemma21_2Beta x DeltaA1 DeltaA2 y * x j := by
          unfold undetLemma21_2Beta H
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conditional rescaling step after the source proof's beta algebra.
    If the source-oriented perturbation preserves the first perturbed system,
    `(A + DeltaA2)^T y = x`, and the beta scalar is nonzero, then the same
    constructed perturbation makes `x` a minimum 2-norm solution of the single
    perturbed rectangular system.

    This is intentionally conditional on `beta ≠ 0`; the source proof's
    perturbation-smallness argument that ensures this condition remains a
    separate open dependency. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_beta_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hbeta : undetLemma21_2Beta x DeltaA1 DeltaA2 y ≠ 0) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let M : Fin m → Fin n → ℝ :=
    fun i j => A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j
  let beta : ℝ := undetLemma21_2Beta x DeltaA1 DeltaA2 y
  let ytilde : Fin m → ℝ := fun i => beta⁻¹ * y i
  have hfirst : rectMatMulVec M x = b := by
    simpa [M] using
      higham21_lemma21_2_symmetrized_system_mulVec_self_of_deltaA1
        A x hsq DeltaA1 DeltaA2 b hDeltaA1
  have haction :
      rectMatMulVec (finiteTranspose M) y = fun j : Fin n => beta * x j := by
    simpa [M, beta] using
      higham21_lemma21_2_symmetrized_transpose_mulVec_eq_beta_smul
        A x DeltaA1 DeltaA2 y hDeltaA2
  have hytilde_eq : rectTransposeMulVec M ytilde = x := by
    ext j
    have hsmul_j :=
      congrFun (rectMatMulVec_smul (finiteTranspose M) beta⁻¹ y) j
    have haction_j := congrFun haction j
    calc
      rectTransposeMulVec M ytilde j =
          rectMatMulVec (finiteTranspose M) ytilde j := by
            rfl
      _ = beta⁻¹ * rectMatMulVec (finiteTranspose M) y j := by
            change rectMatMulVec (finiteTranspose M) (fun i : Fin m => beta⁻¹ * y i) j =
              beta⁻¹ * rectMatMulVec (finiteTranspose M) y j
            exact hsmul_j
      _ = beta⁻¹ * (beta * x j) := by rw [haction_j]
      _ = x j := by
            rw [← mul_assoc, inv_mul_cancel₀ hbeta, one_mul]
  have hsolve : rectMatMulVec M (rectTransposeMulVec M ytilde) = b := by
    rw [hytilde_eq]
    exact hfirst
  have hmin :=
    higham21_eq21_4_rect_transpose_min_norm_of_solves M b ytilde hsolve
  rwa [hytilde_eq] at hmin

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar smallness adapter for a common bound.  If both perturbation
    products are bounded by `rho`, then `3 * rho < 1` implies the printed
    `3 * max ... < 1` hypothesis. -/
theorem higham21_lemma21_2_three_max_lt_one_of_common_bound
    (a b rho : ℝ)
    (ha : a ≤ rho)
    (hb : b ≤ rho)
    (hrho : 3 * rho < 1) :
    3 * max a b < 1 := by
  have hmax_le : max a b ≤ rho := max_le ha hb
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar endpoint of the source proof's beta-positivity estimate.
    Once the matrix perturbation argument has produced the displayed lower
    bound `beta >= 1 - (a + b)/(1 - b)`, the source smallness condition
    `3 * max a b < 1` implies `beta > 0`.

    This is only the final real-arithmetic step; it does not prove the
    pseudoinverse perturbation lower bound that supplies `hbound`. -/
theorem higham21_lemma21_2_scalar_beta_pos_of_bound
    (a b beta : ℝ)
    (hsmall : 3 * max a b < 1)
    (hbound : 1 - (a + b) / (1 - b) ≤ beta) :
    0 < beta := by
  have ha_le : a ≤ max a b := le_max_left a b
  have hb_le : b ≤ max a b := le_max_right a b
  have hden_pos : 0 < 1 - b := by
    nlinarith [hb_le, hsmall]
  have hnum_lt_den : a + b < 1 - b := by
    nlinarith [ha_le, hb_le, hsmall]
  have hfrac_lt_one : (a + b) / (1 - b) < 1 := by
    rw [div_lt_iff₀ hden_pos]
    simpa using hnum_lt_den
  linarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonzero form of the scalar beta-positivity endpoint. -/
theorem higham21_lemma21_2_scalar_beta_ne_zero_of_bound
    (a b beta : ℝ)
    (hsmall : 3 * max a b < 1)
    (hbound : 1 - (a + b) / (1 - b) ≤ beta) :
    beta ≠ 0 :=
  ne_of_gt (higham21_lemma21_2_scalar_beta_pos_of_bound a b beta hsmall hbound)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    inner-product route to the source proof's displayed beta lower bound.
    If the numerator `x^T (DeltaA1 - DeltaA2)^T y` is bounded in absolute
    value by `gamma * x^T x`, then
    `beta >= 1 - gamma`.

    This is an algebraic handoff for the still-open pseudoinverse perturbation
    estimate, which must provide the absolute inner-product bound. -/
theorem higham21_lemma21_2_beta_lower_bound_of_abs_inner_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hinner :
      |∑ j : Fin n,
        x j *
          rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
            y j| ≤
        gamma * vecNorm2Sq x) :
    1 - gamma ≤ undetLemma21_2Beta x DeltaA1 DeltaA2 y := by
  let numer : ℝ :=
    ∑ j : Fin n,
      x j *
        rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          y j
  let denom : ℝ := vecNorm2Sq x
  have hden_pos : 0 < denom := by
    exact lt_of_le_of_ne (by simpa [denom] using vecNorm2Sq_nonneg x)
      (by simpa [denom] using hsq.symm)
  have hden_ne : denom ≠ 0 := ne_of_gt hden_pos
  have hinner' : |numer| ≤ gamma * denom := by
    simpa [numer, denom] using hinner
  have hnum_lower : -(gamma * denom) ≤ numer := (abs_le.mp hinner').1
  have hdiv_lower :
      (-(gamma * denom)) / denom ≤ numer / denom :=
    div_le_div_of_nonneg_right hnum_lower (le_of_lt hden_pos)
  have hleft : (-(gamma * denom)) / denom = -gamma := by
    field_simp [hden_ne]
  have hratio_lower : -gamma ≤ numer / denom := by
    simpa [hleft] using hdiv_lower
  have hfinal : 1 - gamma ≤ 1 + numer / denom := by
    linarith
  simpa [undetLemma21_2Beta, numer, denom] using hfinal

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from the source proof's scalar beta lower bound.
    If the matrix perturbation argument supplies
    `1 - (rho1 + rho2)/(1 - rho2) <= beta`, then the source smallness condition
    `3 * max rho1 rho2 < 1` gives `beta ≠ 0`, so the conditional rescaling
    theorem applies.

    This isolates the remaining matrix work to proving the displayed lower
    bound from pseudoinverse perturbation estimates. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_beta_lower_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hbound :
      1 - (rho1 + rho2) / (1 - rho2) ≤
        undetLemma21_2Beta x DeltaA1 DeltaA2 y) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_beta_ne_zero
    A x DeltaA1 DeltaA2 b y hsq hDeltaA1 hDeltaA2
    (higham21_lemma21_2_scalar_beta_ne_zero_of_bound
      rho1 rho2 (undetLemma21_2Beta x DeltaA1 DeltaA2 y) hsmall hbound)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from the beta numerator bound.  This replaces the
    previous displayed beta lower-bound hypothesis by the equivalent local
    obligation that the absolute beta numerator is bounded by
    `((rho1 + rho2)/(1 - rho2)) * x^T x`.

    The pseudoinverse perturbation estimate needed to prove this absolute
    numerator bound remains open. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_abs_inner_fraction_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hinner :
      |∑ j : Fin n,
        x j *
          rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
            y j| ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2Sq x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_beta_lower_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_beta_lower_bound_of_abs_inner_bound
      x DeltaA1 DeltaA2 y ((rho1 + rho2) / (1 - rho2)) hsq hinner)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    vector-action route to the beta numerator bound.  If
    `(DeltaA1 - DeltaA2)^T y` has Euclidean norm at most `gamma * ||x||_2`,
    then Cauchy--Schwarz gives
    `|x^T (DeltaA1 - DeltaA2)^T y| <= gamma * x^T x`.

    The remaining source perturbation work is to supply this vector-action
    bound from pseudoinverse estimates. -/
theorem higham21_lemma21_2_beta_abs_inner_bound_of_transpose_action_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    (gamma : ℝ)
    (haction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        gamma * vecNorm2 x) :
    |∑ j : Fin n,
      x j *
        rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          y j| ≤
      gamma * vecNorm2Sq x := by
  let z : Fin n → ℝ :=
    rectMatMulVec (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y
  calc
    |∑ j : Fin n, x j * z j|
        ≤ vecNorm2 x * vecNorm2 z :=
            abs_vecInnerProduct_le_vecNorm2_mul x z
    _ ≤ vecNorm2 x * (gamma * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left (by simpa [z] using haction)
              (vecNorm2_nonneg x)
    _ = gamma * vecNorm2Sq x := by
            rw [← vecNorm2_sq x]
            ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from a vector-action perturbation bound on the beta
    numerator.  This is one step closer to the source pseudoinverse proof than
    the raw scalar lower-bound hypothesis, but it is still conditional on the
    vector-action estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (haction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_abs_inner_fraction_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_beta_abs_inner_bound_of_transpose_action_bound
      x DeltaA1 DeltaA2 y ((rho1 + rho2) / (1 - rho2)) haction)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator/vector route to the beta vector-action bound.  An operator-2
    bound for `(DeltaA1 - DeltaA2)^T`, together with a bound on the auxiliary
    dual vector `y` in terms of `x`, gives the vector-action estimate needed by
    the beta handoff.

    The source pseudoinverse perturbation argument is still responsible for
    proving the operator and dual-vector bounds used here. -/
theorem higham21_lemma21_2_transpose_action_bound_of_op_bound_and_dual_norm
    {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ)
    {alpha eta gamma : ℝ}
    (halpha : 0 ≤ alpha)
    (hprod : alpha * eta ≤ gamma)
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) alpha)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
      gamma * vecNorm2 x := by
  calc
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y)
        ≤ alpha * vecNorm2 y := hOp y
    _ ≤ alpha * (eta * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hy halpha
    _ = (alpha * eta) * vecNorm2 x := by ring
    _ ≤ gamma * vecNorm2 x :=
        mul_le_mul_of_nonneg_right hprod (vecNorm2_nonneg x)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from operator and dual-vector norm bounds for the beta
    vector-action estimate.  This isolates the remaining source-specific work
    to proving those bounds from pseudoinverse perturbation theory. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_op_bound_and_dual_norm {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hprod : alpha * eta ≤ (rho1 + rho2) / (1 - rho2))
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) alpha)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
    A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall
    (higham21_lemma21_2_transpose_action_bound_of_op_bound_and_dual_norm
      x DeltaA1 DeltaA2 y halpha hprod hOp hy)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 triangle step for the remaining beta obligation.  Separate
    operator bounds on `DeltaA1` and `DeltaA2` give an operator bound for
    `(DeltaA1 - DeltaA2)^T`. -/
theorem higham21_lemma21_2_transpose_sub_op_bound_of_separate_op_bounds {m n : ℕ}
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ}
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le
      (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
      (alpha + beta) :=
  rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
    (fun i j => DeltaA1 i j - DeltaA2 i j)
    (add_nonneg halpha hbeta)
    (rectOpNorm2Le_sub DeltaA1 DeltaA2 hDeltaA1 hDeltaA2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from separate perturbation operator bounds and a
    dual-vector norm bound.  This leaves the source-specific pseudoinverse
    perturbation work to prove the dual-vector estimate and the final product
    budget. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_norm
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (hprod : (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_op_bound_and_dual_norm
    A x DeltaA1 DeltaA2 b y rho1 rho2 (alpha + beta) eta hsq hDeltaA1
    hDeltaA2 hsmall (add_nonneg halpha hbeta) hprod
    (higham21_lemma21_2_transpose_sub_op_bound_of_separate_op_bounds
      DeltaA1 DeltaA2 halpha hbeta hDeltaA1Op hDeltaA2Op)
    hy

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar product-budget bridge for the operator/dual-vector route.  If the
    two perturbation operator bounds are no larger than `rho1` and `rho2`, and
    the dual-vector factor is bounded by `(1 - rho2)^{-1}`, then the product
    budget required by the beta handoff follows. -/
theorem higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
    (rho1 rho2 alpha beta eta : ℝ)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹) :
    (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2) := by
  have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
  have hden_pos : 0 < 1 - rho2 := by
    nlinarith [hrho2_le, hsmall]
  have hsum_le : alpha + beta ≤ rho1 + rho2 :=
    add_le_add halpha_le hbeta_le
  have hsum_rhs_nonneg : 0 ≤ rho1 + rho2 :=
    le_trans (add_nonneg halpha hbeta) hsum_le
  have hprod :
      (alpha + beta) * eta ≤ (rho1 + rho2) * (1 - rho2)⁻¹ :=
    mul_le_mul hsum_le heta_le heta hsum_rhs_nonneg
  simpa [div_eq_mul_inv] using hprod

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from separate perturbation operator bounds and a
    source-shaped dual-vector factor estimate.  The remaining source-specific
    work is to prove `||y||₂ <= eta ||x||₂` with
    `eta <= (1 - rho2)^{-1}` from the pseudoinverse perturbation argument. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_factor
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hy : vecNorm2 y ≤ eta * vecNorm2 x) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_norm
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1 hDeltaA2
    hsmall halpha hbeta
    (higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le hbeta_le
      heta_le)
    hDeltaA1Op hDeltaA2Op hy

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    algebraic action of the perturbed pseudoinverse transpose used in the
    source proof.  Applying `Bᵀ` to `Bplusᵀ x` is the transposed action of the
    domain projection `Bplus B` on `x`. -/
theorem higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
    {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (finiteTranspose B) (rectMatMulVec (finiteTranspose Bplus) x) =
      rectMatMulVec (finiteTranspose (rectMatMul Bplus B)) x := by
  ext j
  unfold rectMatMulVec finiteTranspose rectMatMul
  calc
    ∑ i : Fin m, B i j * (∑ k : Fin n, Bplus k i * x k)
        = ∑ i : Fin m, ∑ k : Fin n, B i j * (Bplus k i * x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ i : Fin m, B i j * (Bplus k i * x k) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, (∑ i : Fin m, Bplus k i * B i j) * x k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the perturbed pseudoinverse domain projection is symmetric and fixes
    `x`, then the source proof's choice `y = Bplusᵀ x` solves
    `Bᵀ y = x`. -/
theorem higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
    {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    (x : Fin n → ℝ)
    (hDomainSym : IsSymmetricFiniteMatrix (rectMatMul Bplus B))
    (hDomainX : rectMatMulVec (rectMatMul Bplus B) x = x) :
    rectMatMulVec (finiteTranspose B) (rectMatMulVec (finiteTranspose Bplus) x) =
      x := by
  rw [higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection]
  have htranspose :
      finiteTranspose (rectMatMul Bplus B) = rectMatMul Bplus B := by
    ext i j
    exact hDomainSym j i
  rw [htranspose, hDomainX]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a perturbation-pseudoinverse operator bound gives the dual-vector estimate
    for the source proof's choice `y = Bplusᵀ x`. -/
theorem higham21_lemma21_2_dual_vector_bound_of_perturbed_pseudoinverse_op_bound
    {m n : ℕ}
    (Bplus : Fin n → Fin m → ℝ) (x : Fin n → ℝ)
    {eta : ℝ}
    (heta : 0 ≤ eta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    vecNorm2 (rectMatMulVec (finiteTranspose Bplus) x) ≤ eta * vecNorm2 x :=
  (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Bplus heta hBplusOp) x

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped product-bound bridge.  A direct operator bound for
    `Bplus * (DeltaA1 - DeltaA2)` gives the vector-action estimate for
    `(DeltaA1 - DeltaA2)ᵀ (Bplusᵀ x)` used in the beta numerator. -/
theorem higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
    {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    vecNorm2
        (rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rectMatMulVec (finiteTranspose Bplus) x)) ≤
      gamma * vecNorm2 x := by
  have haction :
      rectMatMulVec
          (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rectMatMulVec (finiteTranspose Bplus) x) =
        rectMatMulVec
          (finiteTranspose
            (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j)))
          x :=
    higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
      (fun i j => DeltaA1 i j - DeltaA2 i j) Bplus x
  rw [haction]
  exact
    (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
      hgamma hProduct) x

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete operator-product estimate used in the beta lower-bound route.
    Separate operator-2 bounds for `DeltaA1`, `DeltaA2`, and the perturbed
    pseudoinverse candidate `Bplus` imply an operator bound for the source
    product `Bplus * (DeltaA1 - DeltaA2)`.

    This is the product-bound estimate only; the source perturbation theorem
    must still supply the perturbed-pseudoinverse operator bound. -/
theorem higham21_lemma21_2_pseudoinverse_product_bound_of_separate_op_bounds
    {m n : ℕ}
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    {alpha beta eta : ℝ}
    (heta : 0 ≤ eta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    rectOpNorm2Le
      (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
      (eta * (alpha + beta)) :=
  rectOpNorm2Le_rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j)
    heta hBplusOp (rectOpNorm2Le_sub DeltaA1 DeltaA2 hDeltaA1 hDeltaA2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    minimum-norm handoff from a source-shaped product bound on
    `Bplus * (DeltaA1 - DeltaA2)`.  The remaining perturbation proof is to
    instantiate this product bound for `Bplus = (A + DeltaA2)^+` from the
    source smallness hypotheses. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_pseudoinverse_product_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDomainSym :
      IsSymmetricFiniteMatrix
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)))
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hgamma : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (rho1 + rho2) / (1 - rho2))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let y : Fin m → ℝ := rectMatMulVec (finiteTranspose Bplus) x
  have hDeltaA2 :
      rectMatMulVec (finiteTranspose B) y = x := by
    simpa [B, y] using
      higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
        B Bplus x (by simpa [B] using hDomainSym) (by simpa [B] using hDomainX)
  have hActionGamma :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        gamma * vecNorm2 x := by
    simpa [y] using
      higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
        x DeltaA1 DeltaA2 Bplus hgamma hProduct
  have hAction :
      vecNorm2
          (rectMatMulVec
            (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
        ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x :=
    le_trans hActionGamma
      (mul_le_mul_of_nonneg_right hgamma_le (vecNorm2_nonneg x))
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
      A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hDeltaA1 hDeltaA2 hsmall hAction

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse specialization of the source-shaped product
    handoff.  Under Gram nonsingularity for `B = A + DeltaA2`, the printed
    hypothesis `x = Bᵀ y` supplies the domain-projection condition, so the
    remaining source perturbation work is reduced to the product bound
    on `B⁺ (DeltaA1 - DeltaA2)`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 gamma : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hgamma : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (rho1 + rho2) / (1 - rho2))
    (hProduct :
      rectOpNorm2Le
        (rectMatMul
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          (fun i j => DeltaA1 i j - DeltaA2 i j))
        gamma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let Bplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv B
  have hdetB : Matrix.det (rectGram B : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    simpa [B] using hdet
  have hMP : RectMoorePenrosePseudoinverse m n B Bplus :=
    higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero B hdetB
  have hxRange :
      x = rectMatMulVec Bplus (matMulVec m (rectGram B) y) := by
    calc
      x = rectTransposeMulVec B y := by
        simpa [B] using hxTranspose
      _ = rectMatMulVec Bplus (matMulVec m (rectGram B) y) := by
        simpa [Bplus] using
          higham21_lemma21_2_gram_pseudoinverse_range_of_transpose B hdetB y
  have hDomainX : rectMatMulVec (rectMatMul Bplus B) x = x := by
    rw [hxRange]
    simpa [Bplus] using
      higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
        B hdetB (matMulVec m (rectGram B) y)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_pseudoinverse_product_bound
      A x DeltaA1 DeltaA2 b Bplus rho1 rho2 gamma hsq hDeltaA1
      (by simpa [B, Bplus] using hMP.domain_projection_symmetric)
      (by simpa [B, Bplus] using hDomainX) hsmall hgamma hgamma_le
      (by simpa [B, Bplus] using hProduct)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-facing product-bound specialization of the symmetrized minimum-norm
    handoff.  If the perturbed Gram pseudoinverse exists, the printed transpose
    representation `x = (A + DeltaA2)^T y` holds, and the separate operator
    bounds plus the perturbed-pseudoinverse operator bound imply the source
    product budget, then the constructed single perturbation makes `x` the
    minimum 2-norm solution.

    This removes the raw product-bound hypothesis from the concrete Gram route;
    it remains conditional on the perturbed-Gram nonsingularity and
    perturbed-pseudoinverse operator estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hbudget : eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let Bplus : Fin n → Fin m → ℝ :=
    undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j)
  have hgamma : 0 ≤ eta * (alpha + beta) :=
    mul_nonneg heta (add_nonneg halpha hbeta)
  have hProduct :
      rectOpNorm2Le
        (rectMatMul Bplus (fun i j => DeltaA1 i j - DeltaA2 i j))
        (eta * (alpha + beta)) := by
    exact
      higham21_lemma21_2_pseudoinverse_product_bound_of_separate_op_bounds
        DeltaA1 DeltaA2 Bplus heta hDeltaA1Op hDeltaA2Op
        (by simpa [Bplus] using hBplusOp)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_bound
      A x DeltaA1 DeltaA2 b y rho1 rho2 (eta * (alpha + beta))
      hsq hDeltaA1 hdet hxTranspose hsmall hgamma hbudget
      (by simpa [Bplus] using hProduct)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-factor budget for the concrete perturbed-pseudoinverse route.
    The printed estimates `alpha <= rho1`, `beta <= rho2`, and
    `eta <= (1 - rho2)^{-1}` imply the product budget in the orientation used
    by the concrete Gram-pseudoinverse handoff. -/
theorem higham21_lemma21_2_product_budget_of_source_factor_bounds
    (rho1 rho2 alpha beta eta : ℝ)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹) :
    eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2) := by
  have hbudget :
      (alpha + beta) * eta ≤ (rho1 + rho2) / (1 - rho2) :=
    higham21_lemma21_2_product_budget_of_separate_bounds_and_dual_factor
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le
      hbeta_le heta_le
  simpa [mul_comm] using hbudget

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Gram perturbation
    `(A + DeltaA2)(A + DeltaA2)^T - A A^T` used to reduce perturbed
    Gram nonsingularity to the Chapter 7 `I + A^{-1} DeltaA` route. -/
noncomputable def undetGramPerturbation {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ) : Fin m → Fin m → ℝ :=
  fun i j =>
    rectGram (fun i j => A i j + DeltaA2 i j) i j - rectGram A i j

/-- Componentwise budget for the Chapter 21 Gram perturbation induced by a
    rectangular data perturbation bound `|DeltaA2| <= eps * E`. -/
noncomputable def undetGramPerturbationComponentBudget {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (eps : ℝ) : Fin m → Fin m → ℝ :=
  fun i j => ∑ k : Fin n,
    (|A i k| * E j k + E i k * |A j k| + eps * E i k * E j k)

/-- Row-norm source budget for the Chapter 21 Gram perturbation induced by a
    rectangular componentwise data-perturbation budget.  This replaces each
    entry of `A` and `E` in the componentwise Gram budget by its row 2-norm. -/
noncomputable def undetGramPerturbationRowNormBudget {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (eps : ℝ) : Fin m → Fin m → ℝ :=
  fun i j =>
    (n : ℝ) *
      (rectRowNorm2 A i * rectRowNorm2 E j +
        rectRowNorm2 E i * rectRowNorm2 A j +
        eps * rectRowNorm2 E i * rectRowNorm2 E j)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a row 2-norm is bounded by an operator-2 certificate for the transpose. -/
theorem higham21_rectRowNorm2_le_of_transpose_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) {c : ℝ}
    (hAt : rectOpNorm2Le (finiteTranspose A) c) :
    rectRowNorm2 A i ≤ c := by
  have htest := hAt (finiteBasisVec i)
  have hrow :
      rectMatMulVec (finiteTranspose A) (finiteBasisVec i) =
        fun j : Fin n => A i j := by
    ext j
    simp [rectMatMulVec, finiteTranspose, finiteBasisVec]
  simpa [rectRowNorm2, hrow, vecNorm2_finiteBasisVec] using htest

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a uniform operator-2 bound on a rectangular matrix bounds every row
    2-norm, by applying the transpose operator certificate to a coordinate
    vector. -/
theorem higham21_rectRowNorm2_le_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) {c : ℝ}
    (hc : 0 ≤ c) (hA : rectOpNorm2Le A c) :
    rectRowNorm2 A i ≤ c :=
  higham21_rectRowNorm2_le_of_transpose_rectOpNorm2Le A i
    (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le A hc hA)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scaling a rectangular data majorant by a nonnegative perturbation size
    scales its operator-2 certificate. -/
theorem higham21_rectOpNorm2Le_const_mul_of_nonneg {m n : ℕ}
    (E : Fin m → Fin n → ℝ) {eps e : ℝ}
    (heps : 0 ≤ eps) (hE : rectOpNorm2Le E e) :
    rectOpNorm2Le (fun i j => eps * E i j) (eps * e) := by
  intro x
  have hscale :
      rectMatMulVec (fun i j => eps * E i j) x =
        fun i => eps * rectMatMulVec E x i := by
    ext i
    unfold rectMatMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    vecNorm2 (rectMatMulVec (fun i j => eps * E i j) x)
        = eps * vecNorm2 (rectMatMulVec E x) := by
          rw [hscale, vecNorm2_smul, abs_of_nonneg heps]
    _ ≤ eps * (e * vecNorm2 x) :=
          mul_le_mul_of_nonneg_left (hE x) heps
    _ = eps * e * vecNorm2 x := by ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a componentwise data perturbation bound `|DeltaA| <= eps * E` gives an
    operator-2 certificate for `DeltaA` from an operator-2 certificate for
    `E`. -/
theorem higham21_rectOpNorm2Le_of_componentwise_data_bound {m n : ℕ}
    (DeltaA E : Fin m → Fin n → ℝ) {eps e : ℝ}
    (heps : 0 ≤ eps)
    (hDeltaComponent : ∀ i k, |DeltaA i k| ≤ eps * E i k)
    (hE : rectOpNorm2Le E e) :
    rectOpNorm2Le DeltaA (eps * e) :=
  rectOpNorm2Le_of_abs_entry_le
    (A := DeltaA) (B := fun i j => eps * E i j)
    hDeltaComponent
    (higham21_rectOpNorm2Le_const_mul_of_nonneg E heps hE)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the dimension factor in the conservative source scalar bound has the
    expected quadratic form. -/
theorem higham21_sqrt_nat_cast_mul_self (m : ℕ) :
    Real.sqrt ((m : ℝ) * (m : ℝ)) = (m : ℝ) := by
  rw [← sq]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by exact_mod_cast Nat.zero_le m)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    quadratic source-size scalar bound for the conservative Chapter 7 factor. -/
theorem higham21_lemma21_2_source_factor_le_of_quadratic_bound
    (m : ℕ) (rho2 tau omega : ℝ)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹) :
    tau *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega)) ≤
      (1 - rho2)⁻¹ := by
  calc
    tau *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega))
        = 2 * (m : ℝ) ^ 2 * tau * omega := by
          rw [higham21_sqrt_nat_cast_mul_self m]
          ring
    _ ≤ (1 - rho2)⁻¹ := hSourceFactor_le

/-- Expansion of the Chapter 21 Gram perturbation
    `(A + DeltaA2)(A + DeltaA2)^T - AA^T`. -/
theorem undetGramPerturbation_eq_sum {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ) (i j : Fin m) :
    undetGramPerturbation A DeltaA2 i j =
      ∑ k : Fin n,
        (A i k * DeltaA2 j k + DeltaA2 i k * A j k +
          DeltaA2 i k * DeltaA2 j k) := by
  unfold undetGramPerturbation rectGram
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The componentwise Gram budget is nonnegative when the rectangular
    perturbation majorant is nonnegative. -/
theorem undetGramPerturbationComponentBudget_nonneg {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hE : ∀ i k, 0 ≤ E i k) :
    ∀ i j : Fin m, 0 ≤ undetGramPerturbationComponentBudget A E eps i j := by
  intro i j
  unfold undetGramPerturbationComponentBudget
  apply Finset.sum_nonneg
  intro k _
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (abs_nonneg _) (hE j k))
      (mul_nonneg (hE i k) (abs_nonneg _)))
    (mul_nonneg (mul_nonneg heps (hE i k)) (hE j k))

/-- The row-norm source Gram budget is nonnegative when the rectangular
    perturbation majorant and scalar perturbation size are nonnegative. -/
theorem undetGramPerturbationRowNormBudget_nonneg {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) :
    ∀ i j : Fin m, 0 ≤ undetGramPerturbationRowNormBudget A E eps i j := by
  intro i j
  unfold undetGramPerturbationRowNormBudget
  exact mul_nonneg (by exact_mod_cast Nat.zero_le n)
    (add_nonneg
      (add_nonneg
        (mul_nonneg (rectRowNorm2_nonneg A i) (rectRowNorm2_nonneg E j))
        (mul_nonneg (rectRowNorm2_nonneg E i) (rectRowNorm2_nonneg A j)))
      (mul_nonneg
        (mul_nonneg heps (rectRowNorm2_nonneg E i))
        (rectRowNorm2_nonneg E j)))

/-- The induced componentwise Gram perturbation budget is bounded by the
    row-norm source Gram budget. -/
theorem undetGramPerturbationComponentBudget_le_rowNormBudget {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hE : ∀ i k, 0 ≤ E i k) :
    ∀ i j : Fin m,
      undetGramPerturbationComponentBudget A E eps i j ≤
        undetGramPerturbationRowNormBudget A E eps i j := by
  intro i j
  let C : ℝ :=
    rectRowNorm2 A i * rectRowNorm2 E j +
      rectRowNorm2 E i * rectRowNorm2 A j +
      eps * rectRowNorm2 E i * rectRowNorm2 E j
  have hsum :
      (∑ k : Fin n,
        (|A i k| * E j k + E i k * |A j k| + eps * E i k * E j k)) ≤
        ∑ _k : Fin n, C := by
    apply Finset.sum_le_sum
    intro k _
    have hAi : |A i k| ≤ rectRowNorm2 A i := by
      simpa [rectRowNorm2] using abs_coord_le_vecNorm2 (fun q : Fin n => A i q) k
    have hAj : |A j k| ≤ rectRowNorm2 A j := by
      simpa [rectRowNorm2] using abs_coord_le_vecNorm2 (fun q : Fin n => A j q) k
    have hEi : E i k ≤ rectRowNorm2 E i := by
      simpa [rectRowNorm2, abs_of_nonneg (hE i k)] using
        abs_coord_le_vecNorm2 (fun q : Fin n => E i q) k
    have hEj : E j k ≤ rectRowNorm2 E j := by
      simpa [rectRowNorm2, abs_of_nonneg (hE j k)] using
        abs_coord_le_vecNorm2 (fun q : Fin n => E j q) k
    have hterm1 :
        |A i k| * E j k ≤ rectRowNorm2 A i * rectRowNorm2 E j :=
      mul_le_mul hAi hEj (hE j k) (rectRowNorm2_nonneg A i)
    have hterm2 :
        E i k * |A j k| ≤ rectRowNorm2 E i * rectRowNorm2 A j :=
      mul_le_mul hEi hAj (abs_nonneg _) (rectRowNorm2_nonneg E i)
    have hterm3_raw :
        E i k * E j k ≤ rectRowNorm2 E i * rectRowNorm2 E j :=
      mul_le_mul hEi hEj (hE j k) (rectRowNorm2_nonneg E i)
    have hterm3 :
        eps * E i k * E j k ≤
          eps * rectRowNorm2 E i * rectRowNorm2 E j := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hterm3_raw heps
    simpa [C, add_assoc] using add_le_add (add_le_add hterm1 hterm2) hterm3
  calc
    undetGramPerturbationComponentBudget A E eps i j
        = ∑ k : Fin n,
            (|A i k| * E j k + E i k * |A j k| + eps * E i k * E j k) := by
          rfl
    _ ≤ ∑ _k : Fin n, C := hsum
    _ = undetGramPerturbationRowNormBudget A E eps i j := by
          simp [undetGramPerturbationRowNormBudget, C]
          ring

/-- A componentwise rectangular perturbation bound induces a componentwise
    bound on the Chapter 21 Gram perturbation. -/
theorem undetGramPerturbation_abs_le_componentBudget {m n : ℕ}
    (A DeltaA2 E : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps)
    (hE : ∀ i k, 0 ≤ E i k)
    (hDeltaA2 : ∀ i k, |DeltaA2 i k| ≤ eps * E i k) :
    ∀ i j : Fin m,
      |undetGramPerturbation A DeltaA2 i j| ≤
        eps * undetGramPerturbationComponentBudget A E eps i j := by
  intro i j
  rw [undetGramPerturbation_eq_sum]
  unfold undetGramPerturbationComponentBudget
  calc
    |∑ k : Fin n,
        (A i k * DeltaA2 j k + DeltaA2 i k * A j k +
          DeltaA2 i k * DeltaA2 j k)|
        ≤ ∑ k : Fin n,
            |A i k * DeltaA2 j k + DeltaA2 i k * A j k +
              DeltaA2 i k * DeltaA2 j k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n,
          eps * (|A i k| * E j k + E i k * |A j k| +
            eps * E i k * E j k) := by
        apply Finset.sum_le_sum
        intro k _
        have hterm1 :
            |A i k * DeltaA2 j k| ≤ eps * (|A i k| * E j k) := by
          calc
            |A i k * DeltaA2 j k| = |A i k| * |DeltaA2 j k| := by
              rw [abs_mul]
            _ ≤ |A i k| * (eps * E j k) :=
              mul_le_mul_of_nonneg_left (hDeltaA2 j k) (abs_nonneg _)
            _ = eps * (|A i k| * E j k) := by ring
        have hterm2 :
            |DeltaA2 i k * A j k| ≤ eps * (E i k * |A j k|) := by
          calc
            |DeltaA2 i k * A j k| = |DeltaA2 i k| * |A j k| := by
              rw [abs_mul]
            _ ≤ (eps * E i k) * |A j k| :=
              mul_le_mul_of_nonneg_right (hDeltaA2 i k) (abs_nonneg _)
            _ = eps * (E i k * |A j k|) := by ring
        have hterm3 :
            |DeltaA2 i k * DeltaA2 j k| ≤
              eps * (eps * E i k * E j k) := by
          have hleft_nonneg : 0 ≤ eps * E i k := mul_nonneg heps (hE i k)
          calc
            |DeltaA2 i k * DeltaA2 j k| =
                |DeltaA2 i k| * |DeltaA2 j k| := by
              rw [abs_mul]
            _ ≤ (eps * E i k) * (eps * E j k) :=
              mul_le_mul (hDeltaA2 i k) (hDeltaA2 j k)
                (abs_nonneg _) hleft_nonneg
            _ = eps * (eps * E i k * E j k) := by ring
        calc
          |A i k * DeltaA2 j k + DeltaA2 i k * A j k +
              DeltaA2 i k * DeltaA2 j k|
              ≤ |A i k * DeltaA2 j k| +
                  |DeltaA2 i k * A j k| +
                  |DeltaA2 i k * DeltaA2 j k| := by
                exact abs_add_three _ _ _
          _ ≤ eps * (|A i k| * E j k) +
                eps * (E i k * |A j k|) +
                eps * (eps * E i k * E j k) := by
              nlinarith [hterm1, hterm2, hterm3]
          _ = eps * (|A i k| * E j k + E i k * |A j k| +
                eps * E i k * E j k) := by ring
    _ = eps * (∑ k : Fin n,
          (|A i k| * E j k + E i k * |A j k| +
            eps * E i k * E j k)) := by
        rw [Finset.mul_sum]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Chapter 7 inverse-perturbation handoff for the remaining perturbed Gram
    nonsingularity obligation.  If `AA^T` has a left inverse and the relative
    Gram perturbation `AAT_inv * ((A + DeltaA2)(A + DeltaA2)^T - AA^T)` is a
    strict absolute infinity-norm contraction, then the perturbed Gram matrix
    is nonsingular.

    This is not the full source smallness proof; it replaces the raw
    determinant certificate by the repository's existing Neumann-style
    perturbation condition. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let G : Fin m → Fin m → ℝ := rectGram A
  let DeltaG : Fin m → Fin m → ℝ := undetGramPerturbation A DeltaA2
  let GpertInv : Fin m → Fin m → ℝ :=
    ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG
  have hRight :
      IsRightInverse m (fun i j => G i j + DeltaG i j) GpertInv :=
    problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
      m hm G AAT_inv DeltaG c hc_nn hc_lt
      (by simpa [G] using hLeft)
      (by simpa [DeltaG] using hbound)
  have hdetAdd :
      Matrix.det
          ((fun i j => G i j + DeltaG i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    exact
      Matrix.det_ne_zero_of_right_inverse
        (A := ((fun i j => G i j + DeltaG i j) :
          Matrix (Fin m) (Fin m) ℝ))
        (B := (GpertInv : Matrix (Fin m) (Fin m) ℝ))
        (by
          ext i j
          rw [Matrix.mul_apply, Matrix.one_apply]
          exact hRight i j)
  have hmatrix :
      ((fun i j => G i j + DeltaG i j) :
        Matrix (Fin m) (Fin m) ℝ) =
        (rectGram B : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp [G, DeltaG, undetGramPerturbation, B]
  rw [hmatrix] at hdetAdd
  simpa [B] using hdetAdd

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Chapter 7 inverse perturbation candidate is a certified right inverse
    for the perturbed Gram matrix under the same absolute left-product
    contraction used for nonsingularity above. -/
theorem higham21_lemma21_2_perturbed_gram_ch7_candidate_right_inverse_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    IsRightInverse m
      (rectGram (fun i j => A i j + DeltaA2 i j))
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2)) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  let G : Fin m → Fin m → ℝ := rectGram A
  let DeltaG : Fin m → Fin m → ℝ := undetGramPerturbation A DeltaA2
  have hRight :
      IsRightInverse m (fun i j => G i j + DeltaG i j)
        (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) :=
    problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
      m hm G AAT_inv DeltaG c hc_nn hc_lt
      (by simpa [G] using hLeft)
      (by simpa [DeltaG] using hbound)
  intro i j
  simpa [G, DeltaG, undetGramPerturbation, B] using hRight i j

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    under the Chapter 7 contraction certificate, the repository
    `nonsingInv` chosen for `(A + DeltaA2)(A + DeltaA2)^T` agrees with the
    explicit inverse-perturbation candidate. -/
theorem higham21_lemma21_2_perturbed_gram_nonsingInv_eq_ch7_candidate_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    undetGramNonsingInv (fun i j => A i j + DeltaA2 i j) =
      ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hRight :
      IsRightInverse m (rectGram B)
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)) := by
    simpa [B] using
      higham21_lemma21_2_perturbed_gram_ch7_candidate_right_inverse_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c hc_nn hc_lt hLeft hbound
  unfold undetGramNonsingInv
  simpa [B] using
    nonsingInv_eq_of_isRightInverse (rectGram B)
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2))
      hRight

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a concrete operator-2 certificate for the perturbed Gram inverse follows
    from the explicit Chapter 7 candidate and the Frobenius operator bound. -/
theorem higham21_lemma21_2_gram_nonsingInv_rectOpNorm2Le_frob_candidate_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c) :
    rectOpNorm2Le
      (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
      (frobNorm
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2))) := by
  rw [
    higham21_lemma21_2_perturbed_gram_nonsingInv_eq_ch7_candidate_of_abs_left_product_bound
      hm A DeltaA2 AAT_inv c hc_nn hc_lt hLeft hbound]
  exact
    rectOpNorm2Le_of_opNorm2Le_square
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2))
      (opNorm2Le_of_frobNorm_self
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    square-matrix norm bridge used to convert the Chapter 7 infinity-norm
    estimate for the explicit perturbed inverse candidate into a conservative
    Frobenius/operator-2 certificate. -/
theorem higham21_frobNorm_le_sqrt_card_sq_mul_infNorm {n : ℕ}
    (M : Fin n → Fin n → ℝ) :
    frobNorm M ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) * infNorm M := by
  rw [← frobNormRect_eq_frobNorm M]
  exact
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le M (infNorm_nonneg M)
      (fun i j => ch7_abs_entry_le_infNorm M i j)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conservative Frobenius bound for the explicit Chapter 7 perturbed inverse
    candidate, obtained by composing the local Frobenius/infinity bridge with
    the Chapter 7 inverse-candidate infinity-norm estimate. -/
theorem higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
    {m : ℕ}
    (hm : 0 < m)
    (AAT_inv DeltaG : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_lt : c < 1)
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv DeltaG))
        c) :
    frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
        (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) := by
  let Gcand : Fin m → Fin m → ℝ :=
    ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG
  have hInf :
      infNorm Gcand ≤ ((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv := by
    simpa [Gcand] using
      problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound
        m hm AAT_inv DeltaG c hc_nn hc_lt hbound
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  calc
    frobNorm Gcand
        ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) * infNorm Gcand :=
          higham21_frobNorm_le_sqrt_card_sq_mul_infNorm Gcand
    _ ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
          mul_le_mul_of_nonneg_left hInf hsqrt_nonneg

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar half-radius adapter for the conservative Chapter 7 inverse-candidate
    factor. -/
theorem higham21_one_div_one_sub_le_two_of_nonneg_le_half
    {c : ℝ}
    (_hc_nn : 0 ≤ c)
    (hc_half : c ≤ (1 / 2 : ℝ)) :
    1 / (1 - c) ≤ 2 := by
  have hden_pos : 0 < 1 - c := by nlinarith
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    conservative Frobenius bound for the explicit Chapter 7 perturbed inverse
    candidate under the sufficient half-radius first-product condition. -/
theorem higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_half_radius
    {m : ℕ}
    (hm : 0 < m)
    (AAT_inv DeltaG : Fin m → Fin m → ℝ)
    (c : ℝ)
    (hc_nn : 0 ≤ c)
    (hc_half : c ≤ (1 / 2 : ℝ))
    (hbound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv DeltaG))
        c) :
    frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
        (((m : ℝ) * 2) * infNorm AAT_inv) := by
  have hc_lt : c < 1 := by nlinarith
  have hbase :
      frobNorm (ch7Problem711PerturbedInverseCandidate m AAT_inv DeltaG) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
      hm AAT_inv DeltaG c hc_nn hc_lt hbound
  have hfactor :
      1 / (1 - c) ≤ 2 :=
    higham21_one_div_one_sub_le_two_of_nonneg_le_half hc_nn hc_half
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hinner :
      (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
        (((m : ℝ) * 2) * infNorm AAT_inv) := by
    exact
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor hm_nonneg)
        (infNorm_nonneg AAT_inv)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  exact hbase.trans (mul_le_mul_of_nonneg_left hinner hsqrt_nonneg)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a componentwise Gram-perturbation estimate implies the Chapter 7 absolute
    left-product contraction certificate used for perturbed Gram
    nonsingularity. -/
theorem higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
    {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hE : ∀ i j, 0 ≤ E i j)
    (hDeltaG :
      ∀ i j,
        |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j) :
    infNormBound m
      (absMatrix m
        (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
      (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E)) := by
  simpa [infNormBound] using
    ch7_abs_left_product_infNorm_le_of_componentwise_bound
      m AAT_inv (undetGramPerturbation A DeltaA2) E eps heps hE hDeltaG

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise source-shaped route to perturbed Gram nonsingularity.  If the
    relative Gram perturbation is small in the Chapter 7 first-product
    sensitivity bound, then `(A + DeltaA2)(A + DeltaA2)^T` is nonsingular. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hsmall :
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hE : ∀ i j, 0 ≤ E i j)
    (hDeltaG :
      ∀ i j,
        |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
  higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
    hm A DeltaA2 AAT_inv
    (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E))
    (mul_nonneg heps
      (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv E)))
    hsmall hLeft
    (higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
      A DeltaA2 AAT_inv E eps heps hE hDeltaG)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise rectangular-perturbation route to perturbed Gram
    nonsingularity.  A bound `|DeltaA2| <= eps * E` induces a componentwise
    Gram perturbation budget, which is then passed to the Chapter 7
    first-product smallness condition. -/
theorem higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A DeltaA2 : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps : ℝ)
    (heps : 0 ≤ eps)
    (hsmall :
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hLeft : IsLeftInverse m (rectGram A) AAT_inv)
    (hE : ∀ i k, 0 ≤ E i k)
    (hDeltaA2 : ∀ i k, |DeltaA2 i k| ≤ eps * E i k) :
    Matrix.det
        (rectGram (fun i j => A i j + DeltaA2 i j) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
  higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
    hm A DeltaA2 AAT_inv (undetGramPerturbationComponentBudget A E eps)
    eps heps hsmall hLeft
    (undetGramPerturbationComponentBudget_nonneg A E heps hE)
    (undetGramPerturbation_abs_le_componentBudget A DeltaA2 E heps hE hDeltaA2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    monotonicity of the Chapter 7 first-product infinity-norm sensitivity in
    the nonnegative componentwise perturbation budget. -/
theorem higham21_ch7_first_product_infNorm_le_of_componentwise_le
    {m : ℕ}
    (A_inv E F : Fin m → Fin m → ℝ)
    (hE_nonneg : ∀ i j, 0 ≤ E i j)
    (hEF : ∀ i j, E i j ≤ F i j) :
    infNorm (ch7InverseFirstProductSensitivity m A_inv E) ≤
      infNorm (ch7InverseFirstProductSensitivity m A_inv F) := by
  let PE : Fin m → Fin m → ℝ := ch7InverseFirstProductSensitivity m A_inv E
  let PF : Fin m → Fin m → ℝ := ch7InverseFirstProductSensitivity m A_inv F
  have hF_nonneg : ∀ i j, 0 ≤ F i j := by
    intro i j
    exact (hE_nonneg i j).trans (hEF i j)
  have hPE_nonneg : ∀ i j, 0 ≤ PE i j := by
    intro i j
    exact ch7InverseFirstProductSensitivity_nonneg m A_inv E hE_nonneg i j
  have hPF_nonneg : ∀ i j, 0 ≤ PF i j := by
    intro i j
    exact ch7InverseFirstProductSensitivity_nonneg m A_inv F hF_nonneg i j
  have hPE_le_PF : ∀ i j, PE i j ≤ PF i j := by
    intro i j
    simpa [PE, PF, ch7InverseFirstProductSensitivity] using
      ch7_matMul_le_of_nonneg_left m (absMatrix m A_inv) E F
        (fun i j => abs_nonneg (A_inv i j)) hEF i j
  refine infNorm_le_of_row_sum_le PE ?_ (infNorm_nonneg PF)
  intro i
  calc
    ∑ j : Fin m, |PE i j| = ∑ j : Fin m, PE i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact abs_of_nonneg (hPE_nonneg i j)
    _ ≤ ∑ j : Fin m, PF i j := by
      exact Finset.sum_le_sum fun j _ => hPE_le_PF i j
    _ = ∑ j : Fin m, |PF i j| := by
      apply Finset.sum_congr rfl
      intro j _
      exact (abs_of_nonneg (hPF_nonneg i j)).symm
    _ ≤ infNorm PF :=
      row_sum_le_infNorm PF i

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-budget handoff for the Chapter 7 first-product radius condition.
    If the induced Gram perturbation budget is componentwise bounded by a
    nonnegative source Gram budget, then a radius condition for the source
    budget implies the radius condition for the induced budget. -/
theorem higham21_lemma21_2_gram_first_product_radius_of_componentwise_budget_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (EGram : Fin m → Fin m → ℝ)
    (eps rhoG : ℝ)
    (heps : 0 ≤ eps)
    (hrhoG : 0 ≤ rhoG)
    (hE : ∀ i k, 0 ≤ E i k)
    (hBudget_le :
      ∀ i j, undetGramPerturbationComponentBudget A E eps i j ≤ EGram i j)
    (hSourceRadius :
      rhoG * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  have hBudget_nonneg :
      ∀ i j, 0 ≤ undetGramPerturbationComponentBudget A E eps i j :=
    undetGramPerturbationComponentBudget_nonneg A E heps hE
  have hsens_le :
      infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) ≤
        infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) :=
    higham21_ch7_first_product_infNorm_le_of_componentwise_le
      AAT_inv (undetGramPerturbationComponentBudget A E eps) EGram
      hBudget_nonneg hBudget_le
  exact (mul_le_mul_of_nonneg_left hsens_le hrhoG).trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    perturbed Gram-pseudoinverse operator-bound reduction.  Bounds for `A`,
    the second perturbation `DeltaA2`, and the inverse candidate for
    `(A + DeltaA2)(A + DeltaA2)^T` imply the operator bound for the concrete
    table `(A + DeltaA2)^T ((A + DeltaA2)(A + DeltaA2)^T)^{-1}`.

    This does not prove the source perturbation estimate for the Gram inverse;
    it exposes that estimate as the remaining matrix-analysis obligation. -/
theorem higham21_lemma21_2_perturbed_pseudoinverse_op_bound_of_matrix_and_gram_inverse_bounds
    {m n : ℕ}
    (A DeltaA2 : Fin m → Fin n → ℝ)
    {sigma beta eta : ℝ}
    (hsigma : 0 ≤ sigma)
    (hbeta : 0 ≤ beta)
    (hA : rectOpNorm2Le A sigma)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta)
    (hGramInv :
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    rectOpNorm2Le
      (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
      ((sigma + beta) * eta) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hB : rectOpNorm2Le B (sigma + beta) := by
    simpa [B] using rectOpNorm2Le_add A DeltaA2 hA hDeltaA2
  exact
    rectOpNorm2Le_undetAplusOfGramNonsingInv_of_bounds
      B (add_nonneg hsigma hbeta) hB (by simpa [B] using hGramInv)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse handoff with the scalar product budget derived
    from source-shaped perturbation and pseudoinverse-factor bounds.  The
    remaining matrix perturbation work is still the perturbed Gram
    nonsingularity and the perturbed-pseudoinverse operator estimate. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
    hdet hxTranspose hsmall halpha hbeta heta
    (higham21_lemma21_2_product_budget_of_source_factor_bounds
      rho1 rho2 alpha beta eta hsmall halpha hbeta heta halpha_le
      hbeta_le heta_le)
    hDeltaA1Op hDeltaA2Op hBplusOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    case-split minimum-norm handoff for the source proof.  If `x = 0`, the
    single perturbation is `DeltaA2`; otherwise the existing projector/beta
    argument applies to the symmetrized perturbation.  The nonzero branch is
    still conditional on the perturbed-Gram nonsingularity and pseudoinverse
    operator estimate that remain the active source-facing gap. -/
theorem higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_product_budget
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hbudget : eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hnonzero :
        RectMinNormSolution m n
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_product_budget
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
        hdet hxTranspose hsmall halpha hbeta heta hbudget hDeltaA1Op
        hDeltaA2Op hBplusOp
    simpa [undetLemma21_2SinglePerturbation, hx] using hnonzero

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    case-split handoff using source-shaped factor bounds instead of an explicit
    scalar product-budget certificate.  The theorem still exposes the genuine
    nonzero-branch matrix perturbation obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hnonzero :
        RectMinNormSolution m n
          (fun i j => A i j +
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_source_factors
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1
        hdet hxTranspose hsmall halpha hbeta heta halpha_le hbeta_le
        heta_le hDeltaA1Op hDeltaA2Op hBplusOp
    simpa [undetLemma21_2SinglePerturbation, hx] using hnonzero

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped case split whose nonzero-branch certificates are only
    required when `x != 0`.  This records that the `x = 0` branch needs only the
    first perturbed equation, while the projector/beta branch still needs the
    perturbed-Gram and pseudoinverse product-budget certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_certificates
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (heta : x ≠ 0 → 0 ≤ eta)
    (hbudget : x ≠ 0 →
      eta * (alpha + beta) ≤ (rho1 + rho2) / (1 - rho2))
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : x ≠ 0 →
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_product_budget
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hDeltaA1
        (hdet hx) (hxTranspose hx) (hsmall hx) (halpha hx) (hbeta hx)
        (heta hx) (hbudget hx) (hDeltaA1Op hx) (hDeltaA2Op hx)
        (hBplusOp hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor case split.  The zero branch has no perturbation
    certificates; the nonzero branch derives the scalar product budget from
    source-shaped factor bounds and still exposes only the genuine matrix
    perturbation obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_source_factors
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (heta_le : x ≠ 0 → eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : x ≠ 0 →
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_gram_pseudoinverse_source_factors
        A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hDeltaA1
        (hdet hx) (hxTranspose hx) (hsmall hx) (halpha hx) (hbeta hx)
        (heta hx) (halpha_le hx) (hbeta_le hx) (heta_le hx)
        (hDeltaA1Op hx) (hDeltaA2Op hx) (hBplusOp hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with the concrete perturbed-pseudoinverse
    operator certificate derived from a perturbed-matrix bound and a Gram-inverse
    bound.  The zero branch still needs only the first perturbed equation; the
    nonzero branch now exposes perturbed Gram nonsingularity and the concrete
    Gram-inverse operator estimate as the remaining matrix-analysis obligations. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet : x ≠ 0 →
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_source_factors
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta ((sigma + beta) * eta)
    hDeltaA1 hdet hxTranspose hsmall halpha hbeta
    (fun hx => mul_nonneg (add_nonneg (hsigma hx) (hbeta hx)) (heta hx))
    halpha_le hbeta_le hGramFactor_le hDeltaA1Op hDeltaA2Op
    (fun hx =>
      higham21_lemma21_2_perturbed_pseudoinverse_op_bound_of_matrix_and_gram_inverse_bounds
        A DeltaA2 (hsigma hx) (hbeta hx) (hAOp hx) (hDeltaA2Op hx)
        (hGramInvOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonzero-branch handoff with perturbed Gram nonsingularity discharged by
    the Chapter 7 absolute infinity-norm contraction condition on the relative
    Gram perturbation.  The remaining explicit matrix-analysis obligation is
    the operator-2 bound for the concrete perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta c : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramSmallNonneg : x ≠ 0 → 0 ≤ c)
    (hGramSmallLt : x ≠ 0 → c < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramPerturbBound : x ≠ 0 →
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with both perturbed Gram nonsingularity and
    the concrete Gram-inverse operator certificate derived from the Chapter 7
    absolute left-product contraction.  The remaining source-side obligation is
    the scalar factor bound for the explicit Chapter 7 inverse candidate. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_abs_left_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma c : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramSmallNonneg : x ≠ 0 → 0 ≤ c)
    (hGramSmallLt : x ≠ 0 → c < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramPerturbBound : x ≠ 0 →
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma
    (frobNorm
      (ch7Problem711PerturbedInverseCandidate m AAT_inv
        (undetGramPerturbation A DeltaA2)))
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))
    hxTranspose hsmall halpha hbeta hsigma
    (fun _ =>
      frobNorm_nonneg
        (ch7Problem711PerturbedInverseCandidate m AAT_inv
          (undetGramPerturbation A DeltaA2)))
    halpha_le hbeta_le hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op
    (fun hx =>
      higham21_lemma21_2_gram_nonsingInv_rectOpNorm2Le_frob_candidate_of_abs_left_product_bound
        hm A DeltaA2 AAT_inv c (hGramSmallNonneg hx) (hGramSmallLt hx)
        (hGramLeftInv hx) (hGramPerturbBound hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise Gram-perturbation version of the concrete Chapter 7
    candidate/Frobenius handoff.  The componentwise estimate supplies the
    absolute left-product contraction used by the previous theorem. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramE : x ≠ 0 → ∀ i j, 0 ≤ E i j)
    (hGramPerturbComponent : x ≠ 0 →
      ∀ i j, |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_abs_left_product_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv rho1 rho2 alpha beta sigma
    (eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E))
    hDeltaA1
    (fun hx =>
      mul_nonneg (hGramEpsNonneg hx)
        (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv E)))
    hGramSmallLt hGramLeftInv
    (fun hx =>
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A DeltaA2 AAT_inv E eps (hGramEpsNonneg hx) (hGramE hx)
        (hGramPerturbComponent hx))
    hxTranspose hsmall halpha hbeta hsigma halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation version of the concrete Chapter 7
    candidate/Frobenius handoff.  A componentwise rectangular bound on
    `DeltaA2` induces the Gram perturbation budget used by the componentwise
    theorem above. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 →
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_gram_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv
    (undetGramPerturbationComponentBudget A E eps)
    rho1 rho2 alpha beta sigma eps hDeltaA1 hDataEpsNonneg
    hGramSmallLt hGramLeftInv
    (fun hx =>
      undetGramPerturbationComponentBudget_nonneg A E
        (hDataEpsNonneg hx) (hDataE hx))
    (fun hx =>
      undetGramPerturbation_abs_le_componentBudget A DeltaA2 E
        (hDataEpsNonneg hx) (hDataE hx) (hDeltaA2Component hx))
    hxTranspose hsmall halpha hbeta hsigma halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with the Chapter 7 candidate factor
    replaced by a concrete conservative bound from the inverse-candidate
    infinity-norm estimate.  The remaining explicit source obligation is the
    smallness of the induced first product. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) *
                (1 /
                  (1 -
                    eps *
                      infNorm
                        (ch7InverseFirstProductSensitivity m AAT_inv
                          (undetGramPerturbationComponentBudget A E eps)))))
              * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let EGram : Fin m → Fin m → ℝ :=
    undetGramPerturbationComponentBudget A E eps
  let c : ℝ :=
    eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram)
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_ch7_candidate_frob_source_bounds_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E
      rho1 rho2 alpha beta sigma eps hDeltaA1 hDataEpsNonneg
      hGramSmallLt hGramLeftInv hDataE hDeltaA2Component hxTranspose
      hsmall halpha hbeta hsigma halpha_le hbeta_le ?_ hAOp
      hDeltaA1Op hDeltaA2Op
  intro hx
  have hGramBound :
      infNormBound m
        (absMatrix m
          (matMul m AAT_inv (undetGramPerturbation A DeltaA2)))
        c := by
    simpa [c, EGram] using
      higham21_lemma21_2_gram_left_product_infNormBound_of_componentwise_gram_bound
        A DeltaA2 AAT_inv EGram eps (hDataEpsNonneg hx)
        (by
          simpa [EGram] using
            undetGramPerturbationComponentBudget_nonneg A E
              (hDataEpsNonneg hx) (hDataE hx))
        (by
          simpa [EGram] using
            undetGramPerturbation_abs_le_componentBudget A DeltaA2 E
              (hDataEpsNonneg hx) (hDataE hx) (hDeltaA2Component hx))
  have hCand :
      frobNorm
          (ch7Problem711PerturbedInverseCandidate m AAT_inv
            (undetGramPerturbation A DeltaA2)) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) :=
    higham21_lemma21_2_ch7_candidate_frobNorm_bound_of_abs_left_product_bound
      hm AAT_inv (undetGramPerturbation A DeltaA2) c
      (by
        dsimp [c, EGram]
        exact mul_nonneg (hDataEpsNonneg hx)
          (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps))))
      (by simpa [c, EGram] using hGramSmallLt hx) hGramBound
  have hscaled :
      (sigma + beta) *
          frobNorm
            (ch7Problem711PerturbedInverseCandidate m AAT_inv
              (undetGramPerturbation A DeltaA2)) ≤
        (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) *
                (1 /
                  (1 -
                    eps *
                      infNorm
                        (ch7InverseFirstProductSensitivity m AAT_inv
                          (undetGramPerturbationComponentBudget A E eps)))))
              * infNorm AAT_inv)) := by
    simpa [c, EGram] using
      mul_le_mul_of_nonneg_left hCand (add_nonneg (hsigma hx) (hbeta hx))
  exact hscaled.trans (hConservativeFactor_le hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with a sufficient half-radius
    first-product condition.  This replaces the explicit `1 / (1 - c)` factor
    in the previous conservative handoff by the simpler source-facing bound
    using the constant `2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_half_radius_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallHalf : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let EGram : Fin m → Fin m → ℝ :=
    undetGramPerturbationComponentBudget A E eps
  let c : ℝ :=
    eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram)
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      hDeltaA1 hDataEpsNonneg ?_ hGramLeftInv hDataE
      hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
      halpha_le hbeta_le ?_ hAOp hDeltaA1Op hDeltaA2Op
  · intro hx
    have hhalf : c ≤ (1 / 2 : ℝ) := by
      simpa [c, EGram] using hGramSmallHalf hx
    nlinarith
  · intro hx
    have hc_nn : 0 ≤ c := by
      dsimp [c, EGram]
      exact mul_nonneg (hDataEpsNonneg hx)
        (infNorm_nonneg (ch7InverseFirstProductSensitivity m AAT_inv
          (undetGramPerturbationComponentBudget A E eps)))
    have hfactor :
        1 / (1 - c) ≤ 2 :=
      higham21_one_div_one_sub_le_two_of_nonneg_le_half hc_nn
        (by simpa [c, EGram] using hGramSmallHalf hx)
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hinner :
        (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
          (((m : ℝ) * 2) * infNorm AAT_inv) := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor hm_nonneg)
          (infNorm_nonneg AAT_inv)
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
      Real.sqrt_nonneg _
    have hsqrt :
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * (1 / (1 - c))) * infNorm AAT_inv) ≤
          Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv) :=
      mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
    have hscaled :
        (sigma + beta) *
            (Real.sqrt ((m : ℝ) * (m : ℝ)) *
              (((m : ℝ) *
                  (1 /
                    (1 -
                      eps *
                        infNorm
                          (ch7InverseFirstProductSensitivity m AAT_inv
                            (undetGramPerturbationComponentBudget A E eps)))))
                * infNorm AAT_inv)) ≤
          (sigma + beta) *
            (Real.sqrt ((m : ℝ) * (m : ℝ)) *
              (((m : ℝ) * 2) * infNorm AAT_inv)) := by
      simpa [c, EGram] using
        mul_le_mul_of_nonneg_left hsqrt (add_nonneg (hsigma hx) (hbeta hx))
    exact hscaled.trans (hConservativeFactor_le hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with a source-radius smallness
    condition.  The half-radius first-product condition is discharged from
    `eps <= rhoG` and `rhoG * || |AAT_inv| EGram ||_inf <= 1/2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramSmallRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hConservativeFactor_le : x ≠ 0 →
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  refine
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_half_radius_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      hDeltaA1 hDataEpsNonneg ?_ hGramLeftInv hDataE
      hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
      halpha_le hbeta_le hConservativeFactor_le hAOp hDeltaA1Op
      hDeltaA2Op
  intro hx
  have hsens_nonneg :
      0 ≤
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationComponentBudget A E eps)) :=
    infNorm_nonneg _
  exact
    (mul_le_mul_of_nonneg_right (hDataEpsLeRho hx) hsens_nonneg).trans
      (hGramSmallRadius hx)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-factor adapter for the conservative Chapter 7 candidate
    bound.  A bound on `sigma + beta` and a bound on `||AAT_inv||_inf`
    imply the concrete conservative factor inequality consumed by the
    rectangular data handoff. -/
theorem higham21_lemma21_2_conservative_ch7_factor_le_of_source_bounds
    {m : ℕ}
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho2 sigma beta tau omega : ℝ)
    (hsigma : 0 ≤ sigma)
    (hbeta : 0 ≤ beta)
    (hSigmaBeta_le : sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹) :
    (sigma + beta) *
        (Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
      (1 - rho2)⁻¹ := by
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hm2_nonneg : 0 ≤ (m : ℝ) * 2 :=
    mul_nonneg hm_nonneg (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((m : ℝ) * (m : ℝ)) :=
    Real.sqrt_nonneg _
  have hinv_nonneg : 0 ≤ infNorm AAT_inv :=
    infNorm_nonneg AAT_inv
  have hconcrete_nonneg :
      0 ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv) :=
    mul_nonneg hsqrt_nonneg (mul_nonneg hm2_nonneg hinv_nonneg)
  have htau_nonneg : 0 ≤ tau :=
    (add_nonneg hsigma hbeta).trans hSigmaBeta_le
  have hstep_left :
      (sigma + beta) *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) :=
    mul_le_mul_of_nonneg_right hSigmaBeta_le hconcrete_nonneg
  have hinner :
      ((m : ℝ) * 2) * infNorm AAT_inv ≤ ((m : ℝ) * 2) * omega :=
    mul_le_mul_of_nonneg_left hAATInv_le hm2_nonneg
  have hsize :
      Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * infNorm AAT_inv) ≤
        Real.sqrt ((m : ℝ) * (m : ℝ)) *
          (((m : ℝ) * 2) * omega) :=
    mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
  have hstep_right :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * infNorm AAT_inv)) ≤
        tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) :=
    mul_le_mul_of_nonneg_left hsize htau_nonneg
  exact (hstep_left.trans hstep_right).trans hSourceFactor_le

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with separated source-size scalar
    bounds.  The remaining scalar source obligation is the simplified factor
    involving an upper bound for `sigma + beta` and `||AAT_inv||_inf`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramSmallRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps rhoG
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hGramSmallRadius hGramLeftInv
    hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta hsigma
    halpha_le hbeta_le
    (fun hx =>
      higham21_lemma21_2_conservative_ch7_factor_le_of_source_bounds
        AAT_inv rho2 sigma beta tau omega (hsigma hx) (hbeta hx)
        (hSigmaBeta_le hx) hAATInv_le hSourceFactor_le)
    hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    rectangular data-perturbation handoff with separated source-size scalar
    bounds and a source Gram-budget radius certificate.  This wrapper replaces
    the exact induced Gram first-product radius by a larger componentwise source
    Gram budget. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_budget_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (EGram : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramBudget_le : x ≠ 0 →
      ∀ i j, undetGramPerturbationComponentBudget A E eps i j ≤ EGram i j)
    (hGramSourceRadius : x ≠ 0 →
      rhoG * infNorm (ch7InverseFirstProductSensitivity m AAT_inv EGram) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps rhoG
    tau omega hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      higham21_lemma21_2_gram_first_product_radius_of_componentwise_budget_bound
        A AAT_inv E EGram eps rhoG (hDataEpsNonneg hx)
        ((hDataEpsNonneg hx).trans (hDataEpsLeRho hx)) (hDataE hx)
        (hGramBudget_le hx) (hGramSourceRadius hx))
    hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta
    hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le hSourceFactor_le
    hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget specialization of the conservative rectangular
    data-perturbation handoff.  The induced Gram budget is bounded internally
    by `undetGramPerturbationRowNormBudget`, leaving only a radius condition for
    that row-norm source budget. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_row_norm_budget_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hGramRowNormRadius : x ≠ 0 →
      rhoG *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationRowNormBudget A E eps)) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_source_budget_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E
    (undetGramPerturbationRowNormBudget A E eps)
    rho1 rho2 alpha beta sigma eps rhoG tau omega
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      undetGramPerturbationComponentBudget_le_rowNormBudget A E
        (hDataEpsNonneg hx) (hDataE hx))
    hGramRowNormRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    sufficient row-budget radius certificate from separated infinity-norm
    bounds.  This turns the Chapter 7 first-product smallness condition for
    the row-norm Gram budget into the scalar source obligations
    `‖AAT_inv‖∞ <= omega`, `‖rowBudget‖∞ <= gamma`, and
    `rhoG * (omega * gamma) <= 1/2`. -/
theorem higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps rhoG omega gamma : ℝ)
    (hrhoG : 0 ≤ rhoG)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hRowBudget_le :
      infNorm (undetGramPerturbationRowNormBudget A E eps) ≤ gamma)
    (homega : 0 ≤ omega)
    (hRadius : rhoG * (omega * gamma) ≤ (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationRowNormBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  let G : Fin m → Fin m → ℝ := undetGramPerturbationRowNormBudget A E eps
  change rhoG * infNorm (matMul m (absMatrix m AAT_inv) G) ≤ (1 / 2 : ℝ)
  have hprod :
      infNorm (matMul m (absMatrix m AAT_inv) G) ≤ omega * gamma := by
    have hsub : infNorm (matMul m (absMatrix m AAT_inv) G) ≤
        infNorm (absMatrix m AAT_inv) * infNorm G :=
      infNorm_matMul_le hm (absMatrix m AAT_inv) G
    have habs : infNorm (absMatrix m AAT_inv) = infNorm AAT_inv :=
      infNorm_absMatrix hm AAT_inv
    have hmul : infNorm (absMatrix m AAT_inv) * infNorm G ≤ omega * gamma := by
      rw [habs]
      exact mul_le_mul hAATInv_le hRowBudget_le (infNorm_nonneg G) homega
    exact hsub.trans hmul
  exact (mul_le_mul_of_nonneg_left hprod hrhoG).trans hRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm Gram budget infinity-norm bound from uniform row-norm bounds on
    the data matrix and perturbation majorant. -/
theorem undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
    {m n : ℕ}
    (A E : Fin m → Fin n → ℝ)
    {eps a e : ℝ}
    (heps : 0 ≤ eps)
    (hArow : ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : 0 ≤ a)
    (he : 0 ≤ e) :
    infNorm (undetGramPerturbationRowNormBudget A E eps) ≤
      (m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)) := by
  let C : ℝ := (n : ℝ) * (a * e + e * a + eps * e * e)
  have hinner_nonneg : 0 ≤ a * e + e * a + eps * e * e := by
    exact add_nonneg
      (add_nonneg (mul_nonneg ha he) (mul_nonneg he ha))
      (mul_nonneg (mul_nonneg heps he) he)
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg (by exact_mod_cast Nat.zero_le n) hinner_nonneg
  have hbound_entry :
      ∀ i j : Fin m, undetGramPerturbationRowNormBudget A E eps i j ≤ C := by
    intro i j
    have hAE :
        rectRowNorm2 A i * rectRowNorm2 E j ≤ a * e :=
      mul_le_mul (hArow i) (hErow j) (rectRowNorm2_nonneg E j) ha
    have hEA :
        rectRowNorm2 E i * rectRowNorm2 A j ≤ e * a :=
      mul_le_mul (hErow i) (hArow j) (rectRowNorm2_nonneg A j) he
    have hEE :
        eps * rectRowNorm2 E i * rectRowNorm2 E j ≤ eps * e * e := by
      have hEprod :
          rectRowNorm2 E i * rectRowNorm2 E j ≤ e * e :=
        mul_le_mul (hErow i) (hErow j) (rectRowNorm2_nonneg E j) he
      calc
        eps * rectRowNorm2 E i * rectRowNorm2 E j
            = eps * (rectRowNorm2 E i * rectRowNorm2 E j) := by ring
        _ ≤ eps * (e * e) := mul_le_mul_of_nonneg_left hEprod heps
        _ = eps * e * e := by ring
    have hsum :
        rectRowNorm2 A i * rectRowNorm2 E j +
            rectRowNorm2 E i * rectRowNorm2 A j +
            eps * rectRowNorm2 E i * rectRowNorm2 E j ≤
          a * e + e * a + eps * e * e :=
      add_le_add (add_le_add hAE hEA) hEE
    unfold undetGramPerturbationRowNormBudget C
    exact mul_le_mul_of_nonneg_left hsum (by exact_mod_cast Nat.zero_le n)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin m, |undetGramPerturbationRowNormBudget A E eps i j|
          = ∑ j : Fin m, undetGramPerturbationRowNormBudget A E eps i j := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_of_nonneg
              (undetGramPerturbationRowNormBudget_nonneg A E heps i j)
      _ ≤ ∑ _j : Fin m, C := by
            apply Finset.sum_le_sum
            intro j _
            exact hbound_entry i j
      _ = (m : ℝ) * C := by
            simp [C]
      _ = (m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)) := rfl
  · exact mul_nonneg (by exact_mod_cast Nat.zero_le m) hC_nonneg

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-sized row-norm radius certificate from uniform row-norm bounds on
    `A` and `E`. -/
theorem higham21_lemma21_2_row_norm_first_product_radius_of_row_norm_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps rhoG omega a e : ℝ)
    (heps : 0 ≤ eps)
    (hrhoG : 0 ≤ rhoG)
    (hArow : ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : 0 ≤ a)
    (he : 0 ≤ e)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hRadius :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        infNorm
          (ch7InverseFirstProductSensitivity m AAT_inv
            (undetGramPerturbationRowNormBudget A E eps)) ≤
      (1 / 2 : ℝ) := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
      hm A AAT_inv E eps rhoG omega
      ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))
      hrhoG hAATInv_le
      (undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
        A E heps hArow hErow ha he)
      homega hRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the Chapter 7 radius condition reduced
    to separated infinity-norm scalar bounds. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_infNorm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega gamma : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hRowBudget_le : x ≠ 0 →
      infNorm (undetGramPerturbationRowNormBudget A E eps) ≤ gamma)
    (hRowRadius : x ≠ 0 → rhoG * (omega * gamma) ≤ (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_radius_row_norm_budget_bounds_of_componentwise_data_bound
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
      rhoG tau omega hDeltaA1 hDataEpsNonneg hDataEpsLeRho
      (fun hx =>
        higham21_lemma21_2_row_norm_first_product_radius_of_infNorm_bounds
          hm A AAT_inv E eps rhoG omega gamma (hrhoG hx) hAATInv_le
          (hRowBudget_le hx) homega (hRowRadius hx))
      hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall halpha hbeta
      hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le hSourceFactor_le
      hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the row-budget infinity norm discharged
    from uniform row-norm bounds on `A` and `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega a e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hArow : x ≠ 0 → ∀ i : Fin m, rectRowNorm2 A i ≤ a)
    (hErow : x ≠ 0 → ∀ i : Fin m, rectRowNorm2 E i ≤ e)
    (ha : x ≠ 0 → 0 ≤ a)
    (he : x ≠ 0 → 0 ≤ e)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_infNorm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
    rhoG tau omega
    ((m : ℝ) * ((n : ℝ) * (a * e + e * a + eps * e * e)))
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    (fun hx =>
      undetGramPerturbationRowNormBudget_infNorm_le_of_row_norm_bounds
        A E (hDataEpsNonneg hx) (hArow hx) (hErow hx) (ha hx) (he hx))
    hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose hsmall
    halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-norm source-budget handoff with the row-norm bounds on `A` and `E`
    discharged from operator-2 certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_op_norm_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hSigmaBeta_le : x ≠ 0 → sigma + beta ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_row_norm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha beta sigma eps
    rhoG tau omega sigma e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    (fun hx i =>
      higham21_rectRowNorm2_le_of_rectOpNorm2Le A i (hsigma hx) (hAOp hx))
    (fun hx i =>
      higham21_rectRowNorm2_le_of_rectOpNorm2Le E i (he hx) (hEOp hx))
    hsigma he hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hbeta hsigma halpha_le hbeta_le hSigmaBeta_le hAATInv_le
    hSourceFactor_le hAOp hDeltaA1Op hDeltaA2Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-norm row-budget handoff with the `DeltaA2` operator certificate
    discharged from the componentwise data perturbation bound and an
    operator-2 certificate for `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      tau *
          (Real.sqrt ((m : ℝ) * (m : ℝ)) *
            (((m : ℝ) * 2) * omega)) ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_op_norm_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha (eps * e) sigma
    eps rhoG tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG
    hEOp he hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha
    (fun hx => mul_nonneg (hDataEpsNonneg hx) (he hx))
    hsigma halpha_le hEpsE_le hSigmaEpsE_le hAATInv_le hSourceFactor_le
    hAOp hDeltaA1Op
    (fun hx =>
      higham21_rectOpNorm2Le_of_componentwise_data_bound DeltaA2 E
        (hDataEpsNonneg hx) (hDeltaA2Component hx) (hEOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with the conservative source scalar factor
    supplied in the simpler quadratic dimension form. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_quadratic_source_factor
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_of_componentwise_data_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 alpha sigma eps rhoG
    tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
    hEpsE_le hRowRadius hGramLeftInv hDataE hDeltaA2Component hxTranspose
    hsmall halpha hsigma halpha_le hSigmaEpsE_le hAATInv_le
    (higham21_lemma21_2_source_factor_le_of_quadratic_bound
      m rho2 tau omega hSourceFactor_le)
    hAOp hDeltaA1Op

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with both perturbation operator certificates
    discharged from componentwise data bounds against the same majorant `E`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_op_bounds_quadratic_source_factor
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) *
                (sigma * e + e * sigma + eps * e * e)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA2_component_op_bounds_quadratic_source_factor
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 (eps * e) sigma eps
    rhoG tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp
    he hEpsE_le_rho2 hRowRadius hGramLeftInv hDataE hDeltaA2Component
    hxTranspose hsmall
    (fun hx => mul_nonneg (hDataEpsNonneg hx) (he hx))
    hsigma hEpsE_le_rho1 hSigmaEpsE_le hAATInv_le hSourceFactor_le hAOp
    (fun hx =>
      higham21_rectOpNorm2Le_of_componentwise_data_bound DeltaA1 E
        (hDataEpsNonneg hx) (hDeltaA1Component hx) (hEOp hx))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar row-radius adapter.  The source-sized envelope
    `sigma + eps * e <= tau` bounds the row-budget expression
    `sigma*e + e*sigma + eps*e*e` by `2*e*tau`. -/
theorem higham21_lemma21_2_row_radius_of_source_size_bound
    (m n : ℕ) {sigma eps e tau omega rhoG : ℝ}
    (heps : 0 ≤ eps)
    (he : 0 ≤ e)
    (homega : 0 ≤ omega)
    (hrhoG : 0 ≤ rhoG)
    (hSigmaEpsE_le : sigma + eps * e ≤ tau)
    (hSourceRadius :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) ≤
        (1 / 2 : ℝ)) :
    rhoG *
        (omega *
          ((m : ℝ) *
            ((n : ℝ) *
              (sigma * e + e * sigma + eps * e * e)))) ≤
      (1 / 2 : ℝ) := by
  have heps_e_nonneg : 0 ≤ eps * e := mul_nonneg heps he
  have hsigma_le_tau : sigma ≤ tau :=
    (le_add_of_nonneg_right heps_e_nonneg).trans hSigmaEpsE_le
  have hsum : sigma + (sigma + eps * e) ≤ tau + tau :=
    add_le_add hsigma_le_tau hSigmaEpsE_le
  have hrow_term :
      sigma * e + e * sigma + eps * e * e ≤ 2 * e * tau := by
    calc
      sigma * e + e * sigma + eps * e * e
          = e * (sigma + (sigma + eps * e)) := by ring
      _ ≤ e * (tau + tau) := mul_le_mul_of_nonneg_left hsum he
      _ = 2 * e * tau := by ring
  have hn :
      (n : ℝ) * (sigma * e + e * sigma + eps * e * e) ≤
        (n : ℝ) * (2 * e * tau) :=
    mul_le_mul_of_nonneg_left hrow_term (by exact_mod_cast Nat.zero_le n)
  have hm :
      (m : ℝ) *
          ((n : ℝ) * (sigma * e + e * sigma + eps * e * e)) ≤
        (m : ℝ) * ((n : ℝ) * (2 * e * tau)) :=
    mul_le_mul_of_nonneg_left hn (by exact_mod_cast Nat.zero_le m)
  have homega_mul :
      omega *
          ((m : ℝ) *
            ((n : ℝ) *
              (sigma * e + e * sigma + eps * e * e))) ≤
        omega * ((m : ℝ) * ((n : ℝ) * (2 * e * tau))) :=
    mul_le_mul_of_nonneg_left hm homega
  exact (mul_le_mul_of_nonneg_left homega_mul hrhoG).trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-size scalar adapter.  Separate source bounds for the unperturbed
    matrix size and the data perturbation size imply the combined
    `sigma + eps * e <= tau` envelope used by the row-radius handoff. -/
theorem higham21_lemma21_2_source_size_bound_of_separate_bounds
    {sigma eps e tauA tauE tau : ℝ}
    (hSigma_le : sigma ≤ tauA)
    (hEpsE_le : eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau) :
    sigma + eps * e ≤ tau := by
  exact (add_le_add hSigma_le hEpsE_le).trans hSourceSize

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar row-radius adapter from the flat source product form to the nested
    product shape consumed by the Chapter 7 first-product handoff. -/
theorem higham21_lemma21_2_row_radius_of_flat_source_product
    (m n : ℕ) {e tau omega rhoG : ℝ}
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ)) :
    rhoG *
        (omega *
          ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) ≤
      (1 / 2 : ℝ) := by
  have hshape :
      rhoG *
          (omega *
            ((m : ℝ) * ((n : ℝ) * (2 * e * tau)))) =
        2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG := by
    ring
  simpa [hshape] using hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with the row-radius scalar obligation
    reduced to the source-sized envelope `2*e*tau`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hRowRadius : x ≠ 0 →
      rhoG *
          (omega *
            ((m : ℝ) *
              ((n : ℝ) * (2 * e * tau)))) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigmaEpsE_le : x ≠ 0 → sigma + eps * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have homega : 0 ≤ omega :=
    (infNorm_nonneg AAT_inv).trans hAATInv_le
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_op_bounds_quadratic_source_factor
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
      tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
      hEpsE_le_rho1 hEpsE_le_rho2
      (fun hx =>
        higham21_lemma21_2_row_radius_of_source_size_bound m n
          (hDataEpsNonneg hx) (he hx) homega (hrhoG hx) (hSigmaEpsE_le hx)
          (hRowRadius hx))
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
      hsmall hsigma hSigmaEpsE_le hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with separated source-size bounds and a
    flat source-radius product.  This wrapper removes the combined
    `sigma + eps * e <= tau` and nested row-radius certificates from the public
    surface used by the guarded nonzero branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_separated_source_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hrhoG hEOp he
    hEpsE_le_rho1 hEpsE_le_rho2
    (fun hx =>
      higham21_lemma21_2_row_radius_of_flat_source_product m n
        (hFlatSourceRadius hx))
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hsigma
    (fun hx =>
      higham21_lemma21_2_source_size_bound_of_separate_bounds
        (hSigma_le hx) (hEpsE_le_tauE hx) hSourceSize)
    hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from one common perturbation-radius bound to the two
    separate radius inequalities used by the source-factor handoff. -/
theorem higham21_lemma21_2_epsE_le_radii_of_le_min
    {eps e rho1 rho2 : ℝ}
    (hEpsE_le_min : eps * e ≤ min rho1 rho2) :
    eps * e ≤ rho1 ∧ eps * e ≤ rho2 :=
  le_min_iff.mp hEpsE_le_min

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a common perturbation-radius bound.
    This replaces the duplicate `eps * e <= rho1` and `eps * e <= rho2`
    obligations by the single source-shaped inequality
    `eps * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_separated_source_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      (higham21_lemma21_2_epsE_le_radii_of_le_min
        (hEpsE_le_min hx)).1)
    (fun hx =>
      (higham21_lemma21_2_epsE_le_radii_of_le_min
        (hEpsE_le_min hx)).2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a source perturbation-size cap to the common
    `min rho1 rho2` radius bound. -/
theorem higham21_lemma21_2_epsE_le_min_of_source_radius
    {eps e rho rho1 rho2 : ℝ}
    (hEpsE_le_rho : eps * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2) :
    eps * e ≤ min rho1 rho2 :=
  hEpsE_le_rho.trans hrho_le_min

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a separate source perturbation-size cap.
    This replaces the direct `eps * e <= min rho1 rho2` obligation by
    `eps * e <= rho` together with `rho <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hEpsE_le_rho : x ≠ 0 → eps * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_source_radius
        (hEpsE_le_rho hx) hrho_le_min)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-radius adapter from the branch bound `eps <= rhoG` and a
    source product cap `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_epsE_le_source_radius_of_eps_le_rhoG
    {eps rhoG e rho : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_rho : rhoG * e ≤ rho) :
    eps * e ≤ rho :=
  (mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a source product cap for the
    perturbation-size radius.  This replaces `eps * e <= rho` by the branch
    bound `eps <= rhoG`, nonnegativity of `e`, and `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_product_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_min : rho ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 sigma eps
    rhoG tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_source_radius_of_eps_le_rhoG
        (hDataEpsLeRho hx) (he hx) (hRhoGE_le_rho hx))
    hrho_le_min hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hsigma
    hSigma_le hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from separate source radius comparisons to the common
    `min rho1 rho2` comparison. -/
theorem higham21_lemma21_2_source_radius_le_min_of_bounds
    {rho rho1 rho2 : ℝ}
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2) :
    rho ≤ min rho1 rho2 :=
  le_min hrho_le_rho1 hrho_le_rho2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with separate source comparisons from the
    perturbation cap `rho` to the two Lemma 21.2 smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_split_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_radius_product_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 sigma eps
    rhoG tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_rho
    (higham21_lemma21_2_source_radius_le_min_of_bounds
      hrho_le_rho1 hrho_le_rho2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from branch-wise `rhoG * e` bounds to the common
    `eps * e <= min rho1 rho2` radius condition. -/
theorem higham21_lemma21_2_epsE_le_min_of_eps_le_rhoG_product_bounds
    {eps rhoG e rho1 rho2 : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_rho1 : rhoG * e ≤ rho1)
    (hRhoGE_le_rho2 : rhoG * e ≤ rho2) :
    eps * e ≤ min rho1 rho2 :=
  le_min
    ((mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho1)
    ((mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_rho2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from one common `rhoG * e` product-radius bound to the two
    branch-wise product bounds used by the nonzero-branch source handoff. -/
theorem higham21_lemma21_2_rhoGE_le_radii_of_le_min
    {rhoG e rho1 rho2 : ℝ}
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2) :
    rhoG * e ≤ rho1 ∧ rhoG * e ≤ rho2 :=
  le_min_iff.mp hRhoGE_le_min

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    branch-wise perturbation-radius bounds imply the common min-radius bound. -/
theorem higham21_lemma21_2_epsE_le_min_of_branch_bounds
    {eps e rho1 rho2 : ℝ}
    (hEpsE_le_rho1 : eps * e ≤ rho1)
    (hEpsE_le_rho2 : eps * e ≤ rho2) :
    eps * e ≤ min rho1 rho2 :=
  le_min hEpsE_le_rho1 hEpsE_le_rho2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar source-size adapter from the branch perturbation bound
    `eps <= rhoG` and a product-size cap `rhoG * e <= tauE`. -/
theorem higham21_lemma21_2_epsE_le_tauE_of_eps_le_rhoG_product_bound
    {eps rhoG e tauE : ℝ}
    (hEps_le_rhoG : eps ≤ rhoG)
    (he : 0 ≤ e)
    (hRhoGE_le_tauE : rhoG * e ≤ tauE) :
    eps * e ≤ tauE :=
  (mul_le_mul_of_nonneg_right hEps_le_rhoG he).trans hRhoGE_le_tauE

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar nonnegativity adapter for a source radius majorant. -/
theorem higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
    {eps rhoG : ℝ}
    (hEps_nonneg : 0 ≤ eps)
    (hEps_le_rhoG : eps ≤ rhoG) :
    0 ≤ rhoG :=
  hEps_nonneg.trans hEps_le_rhoG

/-- A nonzero finite vector can exist only over a nonempty `Fin` domain. -/
theorem higham21_nonempty_fin_of_vec_ne_zero {n : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    Nonempty (Fin n) := by
  cases n with
  | zero =>
      exfalso
      exact hx (by funext i; exact Fin.elim0 i)
  | succ n =>
      exact ⟨⟨0, Nat.succ_pos n⟩⟩

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-envelope nonnegativity adapter for the nonzero branch. -/
theorem higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
    {m n : ℕ}
    {x : Fin n → ℝ}
    (E : Fin m → Fin n → ℝ)
    {e : ℝ}
    (hx : x ≠ 0)
    (hEOp : rectOpNorm2Le E e) :
    0 ≤ e := by
  letI : Nonempty (Fin n) := higham21_nonempty_fin_of_vec_ne_zero hx
  exact rectOpNorm2Le_radius_nonneg E hEOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with branch-wise source product bounds
    against the two Lemma 21.2 smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_rhoG_product_radius_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_rho1 : x ≠ 0 → rhoG * e ≤ rho1)
    (hRhoGE_le_rho2 : x ≠ 0 → rhoG * e ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_eps_le_rhoG_product_bounds
        (hDataEpsLeRho hx) (he hx)
        (hRhoGE_le_rho1 hx) (hRhoGE_le_rho2 hx))
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    componentwise/operator handoff with a common `rhoG * e` product-radius
    bound.  This replaces the two branch-wise product-radius obligations by the
    single source-shaped inequality `rhoG * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hEpsE_le_tauE : x ≠ 0 → eps * e ≤ tauE)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_rhoG_product_radius_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he
    (fun hx =>
      (higham21_lemma21_2_rhoGE_le_radii_of_le_min
        (hRhoGE_le_min hx)).1)
    (fun hx =>
      (higham21_lemma21_2_rhoGE_le_radii_of_le_min
        (hRhoGE_le_min hx)).2)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    hEpsE_le_tauE hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common product-radius handoff with the data-perturbation source-size
    obligation also expressed as a `rhoG * e` product bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_and_size_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 sigma eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (hSigma_le : x ≠ 0 → sigma ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 sigma eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_min hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hsigma hSigma_le
    (fun hx =>
      higham21_lemma21_2_epsE_le_tauE_of_eps_le_rhoG_product_bound
        (hDataEpsLeRho hx) (he hx) (hRhoGE_le_tauE hx))
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common `rhoG * e` product-radius and product-size handoff with the
    unperturbed matrix operator envelope written directly as the source-size
    quantity `tauA`.  This is the same dependency chain as the preceding
    wrapper with `sigma = tauA`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hrhoG : x ≠ 0 → 0 ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_common_rhoG_product_radius_and_size_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 tauA eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hrhoG hEOp he hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall htauA (fun _ => le_rfl) hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    `tauA` operator-envelope handoff with nonnegativity of the radius majorant
    derived from the source perturbation bounds `0 <= eps` and `eps <= rhoG`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_eps_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (he : x ≠ 0 → 0 ≤ e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    (fun hx =>
      higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
        (hDataEpsNonneg hx) (hDataEpsLeRho hx))
    hEOp he hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall htauA hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    `tauA` operator-envelope handoff with both radius nonnegativity side
    conditions derived from the source perturbation and operator certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_operator_envelopes
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (htauA : x ≠ 0 → 0 ≤ tauA)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_eps_nonneg
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hEOp
    (fun hx =>
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        E hx (hEOp hx))
    hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall htauA
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator-envelope handoff for the current nonzero branch.  The
    nonnegativity of both operator radii is derived from the `A` and `E`
    operator-envelope certificates on the active branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tauE tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hRhoGE_le_tauE : x ≠ 0 → rhoG * e ≤ tauE)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + tauE ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_tauA_op_rhoG_product_bounds_of_operator_envelopes
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tauE tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho
    hEOp hRhoGE_le_min hRhoGE_le_tauE hFlatSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    (fun hx =>
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        A hx (hAOp hx))
    hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator-envelope handoff with the perturbation-size contribution
    written directly as `rhoG * e`, removing the auxiliary `tauE` envelope. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA (rhoG * e) tau omega e hDeltaA1 hDataEpsNonneg
    hDataEpsLeRho hEOp hRhoGE_le_min (fun _ => le_rfl)
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the common product-radius
    condition derived from a source cap `rhoG * e <= rho` and separate
    comparisons of `rho` with the two smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hFlatSourceRadius : x ≠ 0 →
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    (fun hx =>
      (hRhoGE_le_rho hx).trans
        (higham21_lemma21_2_source_radius_le_min_of_bounds
          hrho_le_rho1 hrho_le_rho2))
    hFlatSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hSourceSize hAATInv_le
    hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter deriving the flat source-radius product from a source
    perturbation cap `rhoG * e <= rho`. -/
theorem higham21_lemma21_2_flat_source_radius_of_product_cap
    (m n : ℕ) {rhoG e rho tau omega : ℝ}
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hRhoGE_le_rho : rhoG * e ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ)) :
    2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
      (1 / 2 : ℝ) := by
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hfactor_nonneg :
      0 ≤ 2 * (m : ℝ) * (n : ℝ) * tau * omega := by
    have h2m : 0 ≤ (2 : ℝ) * (m : ℝ) :=
      mul_nonneg (by norm_num) hm_nonneg
    have h2mn : 0 ≤ (2 : ℝ) * (m : ℝ) * (n : ℝ) :=
      mul_nonneg h2m hn_nonneg
    have h2mnt : 0 ≤ (2 : ℝ) * (m : ℝ) * (n : ℝ) * tau :=
      mul_nonneg h2mn htau
    exact mul_nonneg h2mnt homega
  have hmul :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) *
          (rhoG * e) ≤
        (2 * (m : ℝ) * (n : ℝ) * tau * omega) * rho :=
    mul_le_mul_of_nonneg_left hRhoGE_le_rho hfactor_nonneg
  have hleft :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) *
          (rhoG * e) =
        2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG := by
    ring
  have hright :
      (2 * (m : ℝ) * (n : ℝ) * tau * omega) * rho =
        2 * (m : ℝ) * (n : ℝ) * tau * omega * rho := by
    ring
  have hflat :
      2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
        2 * (m : ℝ) * (n : ℝ) * tau * omega * rho := by
    simpa [hleft, hright] using hmul
  exact hflat.trans hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter deriving the flat source-radius product from the common
    product-radius bound `rhoG * e <= min rho1 rho2`. -/
theorem higham21_lemma21_2_flat_source_radius_of_common_product_radius
    (m n : ℕ) {rhoG e rho1 rho2 tau omega : ℝ}
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * min rho1 rho2 ≤
        (1 / 2 : ℝ)) :
    2 * (m : ℝ) * (n : ℝ) * e * tau * omega * rhoG ≤
      (1 / 2 : ℝ) :=
  higham21_lemma21_2_flat_source_radius_of_product_cap
    (rho := min rho1 rho2) m n htau homega hRhoGE_le_min hSourceRadius

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the source smallness condition bounds the second perturbation radius away
    from one. -/
theorem higham21_lemma21_2_rho2_lt_one_of_three_max_lt_one
    {rho1 rho2 : ℝ}
    (hsmall : 3 * max rho1 rho2 < 1) :
    rho2 < 1 := by
  have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    if the second source radius is nonnegative and below one, then the
    reciprocal factor `(1 - rho2)^{-1}` is at least one. -/
theorem higham21_lemma21_2_one_le_inv_one_sub_of_nonneg_lt_one
    {rho2 : ℝ}
    (hrho2_nonneg : 0 ≤ rho2)
    (hrho2_lt_one : rho2 < 1) :
    1 ≤ (1 - rho2)⁻¹ := by
  have hden_pos : 0 < 1 - rho2 := by linarith
  have hden_le_one : 1 - rho2 ≤ 1 := by linarith
  exact (one_le_inv₀ hden_pos).2 hden_le_one

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    unit source-factor bound implies the inverse-factor bound once
    `0 <= rho2` and the source smallness condition are known. -/
theorem higham21_lemma21_2_source_factor_le_inv_of_unit_bound
    (m : ℕ) {rho1 rho2 tau omega : ℝ}
    (hrho2_nonneg : 0 ≤ rho2)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hSourceFactor_le_one :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ 1) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹ :=
  hSourceFactor_le_one.trans
    (higham21_lemma21_2_one_le_inv_one_sub_of_nonneg_lt_one hrho2_nonneg
      (higham21_lemma21_2_rho2_lt_one_of_three_max_lt_one hsmall))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    a min-radius source-factor bound implies the unit source-factor bound under
    the source smallness condition. -/
theorem higham21_lemma21_2_source_factor_le_one_of_min_radius_bound
    (m : ℕ) {rho1 rho2 tau omega : ℝ}
    (hsmall : 3 * max rho1 rho2 < 1)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ min rho1 rho2) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ 1 := by
  have hmax_lt_one : max rho1 rho2 < 1 := by nlinarith
  have hmin_le_max : min rho1 rho2 ≤ max rho1 rho2 :=
    (min_le_left rho1 rho2).trans (le_max_left rho1 rho2)
  exact le_of_lt
    (lt_of_le_of_lt (hSourceFactor_le_min.trans hmin_le_max) hmax_lt_one)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a source-factor cap to the min-radius source-factor
    bound. -/
theorem higham21_lemma21_2_source_factor_le_min_of_cap
    (m : ℕ) {rho rho1 rho2 tau omega : ℝ}
    (hSourceFactor_le_rho :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2) :
    2 * (m : ℝ) ^ 2 * tau * omega ≤ min rho1 rho2 :=
  hSourceFactor_le_rho.trans
    (higham21_lemma21_2_source_radius_le_min_of_bounds
      hrho_le_rho1 hrho_le_rho2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    scalar adapter from a min-radius cap comparison to the two branch
    comparisons. -/
theorem higham21_lemma21_2_source_cap_le_radii_of_le_min
    {rho rho1 rho2 : ℝ}
    (hrho_le_min : rho ≤ min rho1 rho2) :
    rho ≤ rho1 ∧ rho ≤ rho2 :=
  ⟨hrho_le_min.trans (min_le_left rho1 rho2),
    hrho_le_min.trans (min_le_right rho1 rho2)⟩

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the source-size envelope implies nonnegativity of `tau` on the nonzero
    branch once the operator radii and data perturbation radius are available. -/
theorem higham21_lemma21_2_tau_nonneg_of_source_size
    {m n : ℕ}
    (A E : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {eps rhoG tauA tau e : ℝ}
    (hx : x ≠ 0)
    (hDataEpsNonneg : 0 ≤ eps)
    (hDataEpsLeRho : eps ≤ rhoG)
    (hEOp : rectOpNorm2Le E e)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAOp : rectOpNorm2Le A tauA) :
    0 ≤ tau := by
  have htauA : 0 ≤ tauA :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero A hx hAOp
  have he : 0 ≤ e :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
  have hrhoG : 0 ≤ rhoG :=
    higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
      hDataEpsNonneg hDataEpsLeRho
  exact (add_nonneg htauA (mul_nonneg hrhoG he)).trans hSourceSize

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    nonnegativity of an inverse-norm majorant follows from the infinity-norm
    certificate. -/
theorem higham21_lemma21_2_omega_nonneg_of_infNorm_bound
    {m : ℕ}
    (AAT_inv : Fin m → Fin m → ℝ)
    {omega : ℝ}
    (hAATInv_le : infNorm AAT_inv ≤ omega) :
    0 ≤ omega :=
  (infNorm_nonneg AAT_inv).trans hAATInv_le

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    in the nonzero branch, the common product-radius bound makes `rho2`
    nonnegative because `rhoG` and the operator envelope radius `e` are
    nonnegative. -/
theorem higham21_lemma21_2_rho2_nonneg_of_common_product_radius
    {m n : ℕ}
    (E : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {eps rhoG e rho1 rho2 : ℝ}
    (hx : x ≠ 0)
    (hDataEpsNonneg : 0 ≤ eps)
    (hDataEpsLeRho : eps ≤ rhoG)
    (hEOp : rectOpNorm2Le E e)
    (hRhoGE_le_min : rhoG * e ≤ min rho1 rho2) :
    0 ≤ rho2 := by
  have hrhoG : 0 ≤ rhoG :=
    higham21_lemma21_2_rhoG_nonneg_of_eps_nonneg_le
      hDataEpsNonneg hDataEpsLeRho
  have he : 0 ≤ e :=
    higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
  have hprod_nonneg : 0 ≤ rhoG * e := mul_nonneg hrhoG he
  exact hprod_nonneg.trans (hRhoGE_le_min.trans (min_le_right rho1 rho2))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the flat source-radius product
    derived from the same source perturbation cap used for the smallness radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (htau : 0 ≤ tau)
    (homega : 0 ≤ omega)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_rho hrho_le_rho1 hrho_le_rho2
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_product_cap
        m n htau homega (hRhoGE_le_rho hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    flat source-radius handoff with nonnegativity of `tau` and `omega`
    derived from the active source-size and inverse-norm certificates. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_product_bound_of_source_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_rho : x ≠ 0 → rhoG * e ≤ rho)
    (hrho_le_rho1 : rho ≤ rho1)
    (hrho_le_rho2 : rho ≤ rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_source_radius_split_cap
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_rho hrho_le_rho1 hrho_le_rho2
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_product_cap
        m n
        (higham21_lemma21_2_tau_nonneg_of_source_size A E hx
          (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
          hSourceSize (hAOp hx))
        (higham21_lemma21_2_omega_nonneg_of_infNorm_bound
          AAT_inv hAATInv_le)
        (hRhoGE_le_rho hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/product-size handoff with the flat source-radius product
    derived directly from the common `rhoG * e <= min rho1 rho2` product
    radius, avoiding an auxiliary source cap `rho`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_common_radius_product_bound_of_source_nonneg
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA tau omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * tau * omega * min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hSourceSize : tauA + rhoG * e ≤ tau)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * tau * omega ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA tau omega e hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp
    hRhoGE_le_min
    (fun hx =>
      higham21_lemma21_2_flat_source_radius_of_common_product_radius
        m n
        (higham21_lemma21_2_tau_nonneg_of_source_size A E hx
          (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
          hSourceSize (hAOp hx))
        (higham21_lemma21_2_omega_nonneg_of_infNorm_bound
          AAT_inv hAATInv_le)
        (hRhoGE_le_min hx) hSourceRadius)
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hsmall hSourceSize hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-operator/common-radius handoff with the source-size envelope
    specialized to the exact quantity `tauA + rhoG * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_product_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le :
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤
        (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_product_size_common_radius_product_bound_of_source_nonneg
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG
    tauA (tauA + rhoG * e) omega e hDeltaA1 hDataEpsNonneg
    hDataEpsLeRho hEOp hRhoGE_le_min hSourceRadius hGramLeftInv hDataE
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall le_rfl
    hAATInv_le hSourceFactor_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the inverse source-factor condition
    discharged from a unit source-factor bound in the nonzero branch.  The
    zero branch still uses only the first perturbed equation, as in the printed
    proof's separate `x = 0` case. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_unit_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_one : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤ 1)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · exact
      higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_product_bound
        hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG tauA omega e
        hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp hRhoGE_le_min
        hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
        hxTranspose hsmall hAATInv_le
        (higham21_lemma21_2_source_factor_le_inv_of_unit_bound m
          (higham21_lemma21_2_rho2_nonneg_of_common_product_radius E hx
            (hDataEpsNonneg hx) (hDataEpsLeRho hx) (hEOp hx)
            (hRhoGE_le_min hx))
          (hsmall hx) (hSourceFactor_le_one hx))
        hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the source factor supplied in the
    min-radius form.  The source smallness condition converts that min-radius
    bound to the unit source-factor condition consumed by the nonzero branch. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps rhoG tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hDataEpsLeRho : x ≠ 0 → eps ≤ rhoG)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hRhoGE_le_min : x ≠ 0 → rhoG * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + rhoG * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + rhoG * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_unit_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps rhoG tauA omega e
    hDeltaA1 hDataEpsNonneg hDataEpsLeRho hEOp hRhoGE_le_min hSourceRadius
    hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    hAATInv_le
    (fun hx =>
      higham21_lemma21_2_source_factor_le_one_of_min_radius_bound m
        (hsmall hx) (hSourceFactor_le_min hx))
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff specialized to the printed perturbation
    size `eps`, eliminating the auxiliary `rhoG` radius when the source bounds
    are already stated directly in terms of `eps * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps eps tauA omega e
    hDeltaA1 hDataEpsNonneg (fun _ => le_rfl) hEOp hEpsE_le_min
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with the printed smallness condition
    supplied by a common cap on the two perturbation-product radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le : rho1 ≤ rho)
    (hrho2_le : rho2 ≤ rho)
    (hrho_small : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    (fun _ =>
      higham21_lemma21_2_three_max_lt_one_of_common_bound
        rho1 rho2 rho hrho1_le hrho2_le hrho_small)
    hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with global scalar, operator-envelope,
    inverse, componentwise-data, and min-radius source-factor assumptions.
    The only remaining branch-dependent assumption is the nonzero-branch
    transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall eps tauA omega e
    hDeltaA1 (fun _ => hDataEpsNonneg) (fun _ => hEOp)
    (fun _ => hEpsE_le_min) hSourceRadius (fun _ => hGramLeftInv)
    (fun _ => hDataE) (fun _ => hDeltaA1Component)
    (fun _ => hDeltaA2Component) hxTranspose hrho1_le_small
    hrho2_le_small hrhoSmall hAATInv_le (fun _ => hSourceFactor_le_min)
    (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    global min-factor handoff with the printed smallness shape
    `3 * max rho1 rho2 < 1`, avoiding an auxiliary common-smallness radius. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 (max rho1 rho2)
    eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose (le_max_left rho1 rho2) (le_max_right rho1 rho2) hsmall
    hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    printed-smallness/global min-factor handoff with the scalar source-radius
    condition supplied against `max rho1 rho2`.  In the nonzero branch,
    `min rho1 rho2 <= max rho1 rho2` and nonnegativity of the source
    coefficient convert this to the min-radius condition consumed downstream. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_min_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  · have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hDeltaA1
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  · let coeff : ℝ :=
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega
    have htauA : 0 ≤ tauA :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero A hx hAOp
    have he : 0 ≤ e :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero E hx hEOp
    have homega : 0 ≤ omega :=
      higham21_lemma21_2_omega_nonneg_of_infNorm_bound AAT_inv
        hAATInv_le
    have hcoeff_nonneg : 0 ≤ coeff := by
      have htwo : 0 ≤ (2 : ℝ) := by norm_num
      have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hsize : 0 ≤ tauA + eps * e :=
        add_nonneg htauA (mul_nonneg hDataEpsNonneg he)
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg htwo hm_nonneg) hn_nonneg)
          hsize)
        homega
    have hmin_le_max : min rho1 rho2 ≤ max rho1 rho2 :=
      (min_le_left rho1 rho2).trans (le_max_left rho1 rho2)
    have hSourceRadius :
        2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
            min rho1 rho2 ≤
          (1 / 2 : ℝ) := by
      change coeff * min rho1 rho2 ≤ (1 / 2 : ℝ)
      exact
        (mul_le_mul_of_nonneg_left hmin_le_max hcoeff_nonneg).trans
          (by simpa [coeff] using hSourceRadiusMax)
    exact
      higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_min_factor_global_bounds
        hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
        hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius
        hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
        hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    printed-smallness/max-radius handoff with the perturbation-radius and
    source-factor min-radius obligations supplied by one scalar max bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_combined_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactorMax :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        min rho1 rho2)
    (hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_min_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp
    ((le_max_left (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega)).trans
      hRadiusFactorMax)
    hSourceRadiusMax hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hsmall hAATInv_le
    ((le_max_right (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega)).trans
      hRadiusFactorMax)
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common-radius version of the printed-smallness/max-radius combined-factor
    handoff.  This packages the two source radii by a single scalar majorant
    `rho`, matching the printed `max` smallness condition more closely while
    keeping the scalar radius and operator-envelope obligations explicit. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  have hRadiusFactorMin :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        min rho rho := by
    simpa using hRadiusFactor
  have hSourceRadiusMax :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max rho rho ≤
        (1 / 2 : ℝ) := by
    simpa using hSourceRadius
  have hsmallMax : 3 * max rho rho < 1 := by
    simpa using hsmall
  simpa [min_self, max_self] using
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_max_radius_combined_factor_global_bounds
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho rho eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hRadiusFactorMin hSourceRadiusMax
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hsmallMax hAATInv_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    combined-factor handoff with the common radius instantiated by the
    concrete scalar
    `max (eps * e) (2*m^2*(tauA + eps*e)*omega)`.  This removes the auxiliary
    radius parameter from the previous wrapper while keeping the scalar
    smallness, source-radius, operator-envelope, and componentwise-data
    obligations explicit. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
    hm A x DeltaA1 DeltaA2 b y AAT_inv E
    (max (eps * e)
      (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega))
    eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp le_rfl
    hCombinedSourceRadius hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose hCombinedSmall hAATInv_le hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size/common-radius handoff with common-smallness and source-factor
    caps separated. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_min : x ≠ 0 → eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_rho1 : rhoFactor ≤ rho1)
    (hFactorCap_le_rho2 : rhoFactor ≤ rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
    (fun hx =>
      higham21_lemma21_2_source_factor_le_min_of_cap m
        (hSourceFactor_le_cap hx) hFactorCap_le_rho1 hFactorCap_le_rho2)
    hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-factor-cap handoff with global scalar, operator-envelope, and
    componentwise data assumptions.  The only remaining branch-dependent
    assumption is the nonzero-branch transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_rho1 : rhoFactor ≤ rho1)
    (hFactorCap_le_rho2 : rhoFactor ≤ rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall rhoFactor
    eps tauA omega e hDeltaA1 (fun _ => hDataEpsNonneg)
    (fun _ => hEOp) (fun _ => hEpsE_le_min) hSourceRadius
    (fun _ => hGramLeftInv) (fun _ => hDataE)
    (fun _ => hDeltaA1Component) (fun _ => hDeltaA2Component)
    hxTranspose hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
    (fun _ => hSourceFactor_le_cap) hFactorCap_le_rho1 hFactorCap_le_rho2
    (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    global source-factor-cap handoff with the cap comparison supplied as a
    single min-radius bound. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_min_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 rhoSmall rhoFactor eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hEpsE_le_min : eps * e ≤ min rho1 rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hrho1_le_small : rho1 ≤ rhoSmall)
    (hrho2_le_small : rho2 ≤ rhoSmall)
    (hrhoSmall : 3 * rhoSmall < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_cap :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ rhoFactor)
    (hFactorCap_le_min : rhoFactor ≤ min rho1 rho2)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  rcases higham21_lemma21_2_source_cap_le_radii_of_le_min
      hFactorCap_le_min with
    ⟨hFactorCap_le_rho1, hFactorCap_le_rho2⟩
  exact
    higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_common_smallness_factor_cap_global_bounds
      hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 rhoSmall rhoFactor
      eps tauA omega e hDeltaA1 hDataEpsNonneg hEOp hEpsE_le_min
      hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hrho1_le_small hrho2_le_small hrhoSmall hAATInv_le
      hSourceFactor_le_cap hFactorCap_le_rho1 hFactorCap_le_rho2 hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size `eps`-specialized handoff with the source perturbation-radius
    condition supplied as separate bounds for the two perturbation radii. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_branch_radius_min_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hEpsE_le_rho1 : x ≠ 0 → eps * e ≤ rho1)
    (hEpsE_le_rho2 : x ≠ 0 → eps * e ≤ rho2)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          min rho1 rho2 ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_min : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ min rho1 rho2)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E rho1 rho2 eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp
    (fun hx =>
      higham21_lemma21_2_epsE_le_min_of_branch_bounds
        (hEpsE_le_rho1 hx) (hEpsE_le_rho2 hx))
    hSourceRadius hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
    hxTranspose hsmall hAATInv_le hSourceFactor_le_min hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    exact-size `eps` handoff with both perturbation radii instantiated by the
    common conservative majorant `eps * e`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_factor_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hEOp : x ≠ 0 → rectOpNorm2Le E e)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          (eps * e) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : x ≠ 0 →
      ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * (eps * e) < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_radius : x ≠ 0 →
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ eps * e)
    (hAOp : x ≠ 0 → rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_branch_radius_min_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E (eps * e) (eps * e) eps tauA omega e
    hDeltaA1 hDataEpsNonneg hEOp (fun _ => le_rfl) (fun _ => le_rfl)
    (by simpa using hSourceRadius) hGramLeftInv hDataE hDeltaA1Component
    hDeltaA2Component hxTranspose
    (fun hx =>
      higham21_lemma21_2_three_max_lt_one_of_common_bound
        (eps * e) (eps * e) (eps * e) le_rfl le_rfl (hsmall hx))
    hAATInv_le (fun hx => by simpa using hSourceFactor_le_radius hx) hAOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-style self-radius `eps` handoff with global scalar, operator-envelope,
    and componentwise data assumptions.  The only remaining branch-dependent
    assumption is the nonzero-branch transpose representation of `x`. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          (eps * e) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * (eps * e) < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hSourceFactor_le_radius :
      2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega ≤ eps * e)
    (hAOp : rectOpNorm2Le A tauA) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_self_radius_factor_bound
    hm A x DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e hDeltaA1
    (fun _ => hDataEpsNonneg) (fun _ => hEOp) hSourceRadius
    (fun _ => hGramLeftInv) (fun _ => hDataE) (fun _ => hDeltaA1Component)
    (fun _ => hDeltaA2Component) hxTranspose (fun _ => hsmall)
    hAATInv_le (fun _ => hSourceFactor_le_radius) (fun _ => hAOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with perturbed Gram nonsingularity discharged
    from a componentwise bound on the Gram perturbation.  The remaining
    nonzero-branch matrix-analysis obligation is the concrete operator-2 bound
    for the perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_componentwise_gram_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv E : Fin m → Fin m → ℝ)
    (rho1 rho2 alpha beta sigma eta eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hGramEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps * infNorm (ch7InverseFirstProductSensitivity m AAT_inv E) < 1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hGramE : x ≠ 0 → ∀ i j, 0 ≤ E i j)
    (hGramPerturbComponent : x ≠ 0 →
      ∀ i j, |undetGramPerturbation A DeltaA2 i j| ≤ eps * E i j)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_gram_bound
        hm A DeltaA2 AAT_inv E eps (hGramEpsNonneg hx)
        (hGramSmallLt hx) (hGramLeftInv hx) (hGramE hx)
        (hGramPerturbComponent hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    guarded source-factor handoff with perturbed Gram nonsingularity discharged
    from a componentwise bound on the rectangular perturbation `DeltaA2`.
    The only remaining nonzero-branch matrix-analysis obligation is the
    concrete operator-2 bound for the perturbed Gram inverse. -/
theorem higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds_of_componentwise_data_bound
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho1 rho2 alpha beta sigma eta eps : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDataEpsNonneg : x ≠ 0 → 0 ≤ eps)
    (hGramSmallLt : x ≠ 0 →
      eps *
          infNorm
            (ch7InverseFirstProductSensitivity m AAT_inv
              (undetGramPerturbationComponentBudget A E eps)) <
        1)
    (hGramLeftInv : x ≠ 0 → IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : x ≠ 0 → ∀ i k, 0 ≤ E i k)
    (hDeltaA2Component : x ≠ 0 →
      ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x ≠ 0 →
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : x ≠ 0 → 3 * max rho1 rho2 < 1)
    (halpha : x ≠ 0 → 0 ≤ alpha)
    (hbeta : x ≠ 0 → 0 ≤ beta)
    (hsigma : x ≠ 0 → 0 ≤ sigma)
    (heta : x ≠ 0 → 0 ≤ eta)
    (halpha_le : x ≠ 0 → alpha ≤ rho1)
    (hbeta_le : x ≠ 0 → beta ≤ rho2)
    (hGramFactor_le : x ≠ 0 → (sigma + beta) * eta ≤ (1 - rho2)⁻¹)
    (hAOp : x ≠ 0 → rectOpNorm2Le A sigma)
    (hDeltaA1Op : x ≠ 0 → rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : x ≠ 0 → rectOpNorm2Le DeltaA2 beta)
    (hGramInvOp : x ≠ 0 →
      rectOpNorm2Le
        (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_single_min_norm_of_nonzero_branch_gram_inverse_source_bounds
    A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta sigma eta
    hDeltaA1
    (fun hx =>
      higham21_lemma21_2_perturbed_gram_det_ne_zero_of_componentwise_data_bound
        hm A DeltaA2 AAT_inv E eps (hDataEpsNonneg hx)
        (hGramSmallLt hx) (hGramLeftInv hx) (hDataE hx)
        (hDeltaA2Component hx))
    hxTranspose hsmall halpha hbeta hsigma heta halpha_le hbeta_le
    hGramFactor_le hAOp hDeltaA1Op hDeltaA2Op hGramInvOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped pseudoinverse handoff for the remaining beta argument.
    If `Bplus` is a perturbed pseudoinverse for `B = A + DeltaA2` whose
    domain projection fixes `x`, and `Bplus` has the source perturbation
    operator bound, then the existing separate-operator bridge proves the
    single-perturbation minimum-norm system.

    The still-open matrix perturbation work is to instantiate the projection
    and operator-bound hypotheses for the concrete `(A + DeltaA2)^+`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_perturbed_pseudoinverse
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hDomainSym :
      IsSymmetricFiniteMatrix
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)))
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let y : Fin m → ℝ := rectMatMulVec (finiteTranspose Bplus) x
  have hDeltaA2 :
      rectMatMulVec (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y = x := by
    simpa [y] using
      higham21_lemma21_2_perturbed_pseudoinverse_transpose_solves_of_domain_projection
        (fun i j => A i j + DeltaA2 i j) Bplus x hDomainSym hDomainX
  have hy : vecNorm2 y ≤ eta * vecNorm2 x := by
    simpa [y] using
      higham21_lemma21_2_dual_vector_bound_of_perturbed_pseudoinverse_op_bound
        Bplus x heta hBplusOp
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_dual_factor
      A x DeltaA1 DeltaA2 b y rho1 rho2 alpha beta eta hsq hDeltaA1 hDeltaA2
      hsmall halpha hbeta heta halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op hy

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Moore--Penrose specialization of the perturbed-pseudoinverse beta handoff.
    A pseudoinverse certificate supplies the domain-projection symmetry needed
    by the source proof; the remaining open perturbation work is the projection
    fixing `x` and the operator bound for the concrete perturbed pseudoinverse. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_moore_penrose_pseudoinverse_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (Bplus : Fin n → Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (fun i j => A i j + DeltaA2 i j) Bplus)
    (hDomainX :
      rectMatMulVec
        (rectMatMul Bplus (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp : rectOpNorm2Le Bplus eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x :=
  higham21_lemma21_2_symmetrized_min_norm_of_separate_op_bounds_and_perturbed_pseudoinverse
    A x DeltaA1 DeltaA2 b Bplus rho1 rho2 alpha beta eta hsq hDeltaA1
    hMP.domain_projection_symmetric hDomainX hsmall halpha hbeta heta
    halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op hBplusOp

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse specialization of the beta handoff for
    `B = A + DeltaA2`.  Under nonsingularity of `B Bᵀ`, the source table
    `Bᵀ(BBᵀ)⁻¹` supplies the Moore--Penrose certificate used by the previous
    wrapper. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hDomainX :
      rectMatMulVec
        (rectMatMul
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          (fun i j => A i j + DeltaA2 i j)) x = x)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hMP : RectMoorePenrosePseudoinverse m n B (undetAplusOfGramNonsingInv B) :=
    higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero B (by
      simpa [B] using hdet)
  exact
    higham21_lemma21_2_symmetrized_min_norm_of_moore_penrose_pseudoinverse_bound
      A x DeltaA1 DeltaA2 b (undetAplusOfGramNonsingInv B)
      rho1 rho2 alpha beta eta hsq hDeltaA1 hMP
      (by simpa [B] using hDomainX) hsmall halpha hbeta heta
      halpha_le hbeta_le heta_le hDeltaA1Op hDeltaA2Op
      (by simpa [B] using hBplusOp)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete Gram-pseudoinverse range specialization of the beta handoff.
    Instead of assuming the domain projection fixes `x` directly, it suffices
    that `x` is explicitly represented as `(A + DeltaA2)^+ yB`. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (yB : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxRange :
      x =
        rectMatMulVec
          (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
          yB)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  refine
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_bound
      A x DeltaA1 DeltaA2 b rho1 rho2 alpha beta eta hsq hDeltaA1 hdet
      ?_ hsmall halpha hbeta heta halpha_le hbeta_le heta_le
      hDeltaA1Op hDeltaA2Op hBplusOp
  rw [hxRange]
  simpa [B] using
    higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
      B (by simpa [B] using hdet) yB

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    source-shaped Gram-pseudoinverse range handoff.  The printed hypothesis
    `x = (A + DeltaA2)ᵀ y` supplies the concrete pseudoinverse-range
    representation needed by the beta/minimum-norm argument. -/
theorem higham21_lemma21_2_symmetrized_min_norm_of_transpose_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (rho1 rho2 alpha beta eta : ℝ)
    (hsq : vecNorm2Sq x ≠ 0)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hxTranspose :
      x =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * max rho1 rho2 < 1)
    (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (halpha_le : alpha ≤ rho1)
    (hbeta_le : beta ≤ rho2)
    (heta_le : eta ≤ (1 - rho2)⁻¹)
    (hDeltaA1Op : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2Op : rectOpNorm2Le DeltaA2 beta)
    (hBplusOp :
      rectOpNorm2Le
        (undetAplusOfGramNonsingInv (fun i j => A i j + DeltaA2 i j))
        eta) :
    RectMinNormSolution m n
      (fun i j => A i j +
        undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  refine
    higham21_lemma21_2_symmetrized_min_norm_of_gram_pseudoinverse_range
      A x DeltaA1 DeltaA2 b (matMulVec m (rectGram B) y)
      rho1 rho2 alpha beta eta hsq hDeltaA1 hdet ?_
      hsmall halpha hbeta heta halpha_le hbeta_le heta_le
      hDeltaA1Op hDeltaA2Op hBplusOp
  calc
    x = rectTransposeMulVec B y := by
      simpa [B] using hxTranspose
    _ =
        rectMatMulVec (undetAplusOfGramNonsingInv B)
          (matMulVec m (rectGram B) y) := by
      exact
        higham21_lemma21_2_gram_pseudoinverse_range_of_transpose
          B (by simpa [B] using hdet) y

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Frobenius-squared norm bound for the projector mixture used to replace
    two perturbation blocks by one. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frobNormSq_le {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormSqRect (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) ≤
      frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
  have h :=
    lsLemma20_6Perturbation_frobNormSqRect_le
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
  simpa [undetLemma21_2SymmetrizedPerturbation, frobNormSqRect_finiteTranspose, add_comm]
    using h

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Frobenius-norm form of the printed bound
    `||Delta A||_F <= (||Delta A_1||_F^2 + ||Delta A_2||_F^2)^(1/2)` for the
    projector mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_frob_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormRect (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) := by
  have h :=
    lsLemma20_6Perturbation_norm_bound_two_frob
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
  simpa [undetLemma21_2SymmetrizedPerturbation, frobNormRect_finiteTranspose, add_comm]
    using h

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 norm form of the printed bound for the projector mixture.  If
    the two original perturbation blocks have operator-2 bounds `alpha` and
    `beta`, then the constructed perturbation has bound
    `(alpha^2 + beta^2)^(1/2)`. -/
theorem higham21_lemma21_2_symmetrized_perturbation_op_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2)
      (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  have hDeltaA2T : rectOpNorm2Le (finiteTranspose DeltaA2) beta :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le DeltaA2 hbeta hDeltaA2
  have hDeltaA1T : rectOpNorm2Le (finiteTranspose DeltaA1) alpha :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le DeltaA1 halpha hDeltaA1
  have hbase :
      rectOpNorm2Le
        (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))
        (Real.sqrt (beta ^ 2 + alpha ^ 2)) :=
    lsLemma20_6Perturbation_norm_bound_two_operator
      x hsq (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)
      hbeta halpha hDeltaA2T hDeltaA1T
  have htrans :
      rectOpNorm2Le
        (finiteTranspose
          (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1)))
        (Real.sqrt (beta ^ 2 + alpha ^ 2)) :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (lsLemma20_6Perturbation x (finiteTranspose DeltaA2) (finiteTranspose DeltaA1))
      (Real.sqrt_nonneg _) hbase
  have hrad : beta ^ 2 + alpha ^ 2 = alpha ^ 2 + beta ^ 2 := by ring
  simpa [undetLemma21_2SymmetrizedPerturbation, hrad] using htrans

private theorem higham21_right_nonneg_le_sqrt_sq_add_sq
    (a b : ℝ) (hb : 0 ≤ b) :
    b ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hb_sq : b ^ 2 ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg a]
  have hsqrt : Real.sqrt (b ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.sqrt_le_sqrt hb_sq
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hb] using hsqrt

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    squared Frobenius-norm form of the printed perturbation bound for the
    source-case single perturbation.  In the zero branch the perturbation is
    `DeltaA2`; in the nonzero branch it is the projector mixture. -/
theorem higham21_lemma21_2_single_perturbation_frobNormSq_le {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormSqRect (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
  by_cases hx : x = 0
  · have hD1 : 0 ≤ frobNormSqRect DeltaA1 := frobNormSqRect_nonneg DeltaA1
    have hbound :
        frobNormSqRect DeltaA2 ≤ frobNormSqRect DeltaA1 + frobNormSqRect DeltaA2 := by
      nlinarith
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_frobNormSq_le
        x hsq DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    Frobenius-norm form of the printed perturbation bound for the source-case
    single perturbation. -/
theorem higham21_lemma21_2_single_perturbation_frob_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) :
    frobNormRect (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) := by
  by_cases hx : x = 0
  · have hbound :
        frobNormRect DeltaA2 ≤
          Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq
        (frobNormRect DeltaA1) (frobNormRect DeltaA2)
        (frobNormRect_nonneg DeltaA2)
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_frob_bound
        x hsq DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    squared row-wise 2-norm form of the printed perturbation bound for the
    projector mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_rowNormSq_le {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    vecNorm2Sq
        (fun j : Fin n =>
          undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) ≤
      vecNorm2Sq (fun j : Fin n => DeltaA1 i j) +
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
  let C1 : Fin n → Fin 1 → ℝ := fun j _ => DeltaA2 i j
  let C2 : Fin n → Fin 1 → ℝ := fun j _ => DeltaA1 i j
  have hbase :=
    lsLemma20_6Perturbation_frobNormSqRect_le x hsq C1 C2
  have hleft :
      frobNormSqRect (lsLemma20_6Perturbation x C1 C2) =
        vecNorm2Sq
          (fun j : Fin n =>
            undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C1, C2,
      undetLemma21_2SymmetrizedPerturbation, lsLemma20_6Perturbation,
      finiteTranspose, matMulRectLeft]
  have hC1 :
      frobNormSqRect C1 =
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C1]
  have hC2 :
      frobNormSqRect C2 =
        vecNorm2Sq (fun j : Fin n => DeltaA1 i j) := by
    simp [frobNormSqRect, vecNorm2Sq, C2]
  calc
    vecNorm2Sq
        (fun j : Fin n =>
          undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
        = frobNormSqRect (lsLemma20_6Perturbation x C1 C2) := hleft.symm
    _ ≤ frobNormSqRect C1 + frobNormSqRect C2 := hbase
    _ = vecNorm2Sq (fun j : Fin n => DeltaA1 i j) +
        vecNorm2Sq (fun j : Fin n => DeltaA2 i j) := by
          rw [hC1, hC2]
          ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-wise 2-norm form of the printed perturbation bound for the projector
    mixture. -/
theorem higham21_lemma21_2_symmetrized_perturbation_row_bound {m n : ℕ}
    (x : Fin n → ℝ) (hsq : vecNorm2Sq x ≠ 0)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) := by
  apply (sq_le_sq₀
    (rectRowNorm2_nonneg
      (undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2) i)
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  simpa [rectRowNorm2, vecNorm2_sq] using
    higham21_lemma21_2_symmetrized_perturbation_rowNormSq_le
      x hsq DeltaA1 DeltaA2 i

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    row-wise 2-norm form of the printed perturbation bound for the source-case
    single perturbation.  In the zero branch the perturbation is `DeltaA2`;
    in the nonzero branch it is the projector mixture. -/
theorem higham21_lemma21_2_single_perturbation_row_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) := by
  by_cases hx : x = 0
  · have hbound :
        rectRowNorm2 DeltaA2 i ≤
          Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 + rectRowNorm2 DeltaA2 i ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq
        (rectRowNorm2 DeltaA1 i) (rectRowNorm2 DeltaA2 i)
        (rectRowNorm2_nonneg DeltaA2 i)
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_row_bound
        x hsq DeltaA1 DeltaA2 i

private theorem higham21_sqrt_sq_add_sq_le_sqrt_two_mul
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha_le : a ≤ c) (hb_le : b ≤ c) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt 2 * c := by
  have ha_sq : a ^ 2 ≤ c ^ 2 := (sq_le_sq₀ ha hc).mpr ha_le
  have hb_sq : b ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hb hc).mpr hb_le
  apply (sq_le_sq₀
    (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hc)).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    entrywise row-relative perturbation bounds imply the row-2-norm bound used
    by the row-wise backward-error model. -/
theorem higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
    {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA : ∀ i k, |DeltaA i k| ≤ eta * |A i k|)
    (i : Fin m) :
    rectRowNorm2 DeltaA i ≤ eta * rectRowNorm2 A i := by
  calc
    rectRowNorm2 DeltaA i
        ≤ vecNorm2 (fun k : Fin n => eta * |A i k|) := by
          simpa [rectRowNorm2] using
            vecNorm2_le_of_abs_le
              (fun k : Fin n => DeltaA i k)
              (fun k : Fin n => eta * |A i k|)
              (fun k => hDeltaA i k)
    _ = eta * rectRowNorm2 A i := by
          rw [vecNorm2_smul, abs_of_nonneg heta, vecNorm2_abs]
          rfl

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    common row-wise relative-bound corollary for the source-case single
    perturbation.  If both input perturbations are bounded row-by-row by
    `eta * ||A(i,:)||_2`, the constructed single perturbation is bounded
    row-by-row by `sqrt 2 * eta * ||A(i,:)||_2`. -/
theorem higham21_lemma21_2_single_perturbation_row_bound_of_common_row_bound
    {m n : ℕ}
    (x : Fin n → ℝ)
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i ≤
      Real.sqrt 2 * eta * rectRowNorm2 A i := by
  have hrow :=
    higham21_lemma21_2_single_perturbation_row_bound
      x DeltaA1 DeltaA2 i
  have hcommon_nonneg : 0 ≤ eta * rectRowNorm2 A i :=
    mul_nonneg heta (rectRowNorm2_nonneg A i)
  have hsqrt :
      Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 +
          rectRowNorm2 DeltaA2 i ^ 2) ≤
        Real.sqrt 2 * (eta * rectRowNorm2 A i) :=
    higham21_sqrt_sq_add_sq_le_sqrt_two_mul
      (rectRowNorm2_nonneg DeltaA1 i)
      (rectRowNorm2_nonneg DeltaA2 i)
      hcommon_nonneg (hDeltaA1 i) (hDeltaA2 i)
  calc
    rectRowNorm2 (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) i
        ≤ Real.sqrt (rectRowNorm2 DeltaA1 i ^ 2 +
            rectRowNorm2 DeltaA2 i ^ 2) := hrow
    _ ≤ Real.sqrt 2 * (eta * rectRowNorm2 A i) := hsqrt
    _ = Real.sqrt 2 * eta * rectRowNorm2 A i := by ring

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    operator-2 norm form of the printed perturbation bound for the source-case
    single perturbation. -/
theorem higham21_lemma21_2_single_perturbation_op_bound {m n : ℕ}
    (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    rectOpNorm2Le (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)
      (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  by_cases hx : x = 0
  · have hbeta_le : beta ≤ Real.sqrt (alpha ^ 2 + beta ^ 2) :=
      higham21_right_nonneg_le_sqrt_sq_add_sq alpha beta hbeta
    have hbound :
        rectOpNorm2Le DeltaA2 (Real.sqrt (alpha ^ 2 + beta ^ 2)) :=
      rectOpNorm2Le_mono hbeta_le hDeltaA2
    simpa [undetLemma21_2SinglePerturbation, hx] using hbound
  · have hsq : vecNorm2Sq x ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_op_bound
        x hsq DeltaA1 DeltaA2 halpha hbeta hDeltaA1 hDeltaA2

-- ============================================================
-- §21.3  Row-wise backward error for underdetermined systems
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    a row-wise backward-error witness for an underdetermined system.

    The computed vector `x_hat` is the exact minimum 2-norm solution of the
    row-wise perturbed rectangular system `(A + ΔA) x = b`, and each row
    perturbation is bounded relative to the corresponding row of `A` in the
    Euclidean norm. -/
structure UndetRowwiseBackwardErrorFeasible (m n : ℕ)
    (A ΔA : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ) : Prop where
  /-- The row-wise error factor is nonnegative. -/
  eta_nonneg : 0 ≤ eta
  /-- `x_hat` is the minimum 2-norm solution of the perturbed system. -/
  min_norm :
    RectMinNormSolution m n (fun i j => A i j + ΔA i j) b x_hat
  /-- Each row perturbation is bounded by `eta` times the original row norm. -/
  row_bound : ∀ i : Fin m, rectRowNorm2 ΔA i ≤ eta * rectRowNorm2 A i

/-- Existence form of the Chapter 21 row-wise backward-error predicate. -/
def UndetRowwiseBackwardErrorBounded (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ) : Prop :=
  ∃ ΔA : Fin m → Fin n → ℝ,
    UndetRowwiseBackwardErrorFeasible m n A ΔA b x_hat eta

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    source-facing constructor for a row-wise backward-error certificate.
    This packages the definition used by Theorem 21.4; it does not by itself
    prove that a particular QR implementation supplies such a witness. -/
theorem higham21_rowwise_backward_error_bound_witness
    (m n : ℕ)
    (A ΔA : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ)
    (heta : 0 ≤ eta)
    (hmin :
      RectMinNormSolution m n (fun i j => A i j + ΔA i j) b x_hat)
    (hrow : ∀ i : Fin m, rectRowNorm2 ΔA i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat eta :=
  ⟨ΔA, ⟨heta, hmin, hrow⟩⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    row-wise backward-error certificates are monotone in the displayed error
    factor.  This is a small packaging lemma for later source statements whose
    printed coefficient is a conservative upper bound for a proved one. -/
theorem higham21_rowwise_backward_error_bound_mono
    {m n : ℕ}
    {A : Fin m → Fin n → ℝ}
    {b : Fin m → ℝ}
    {x_hat : Fin n → ℝ}
    {eta eta' : ℝ}
    (hcert : UndetRowwiseBackwardErrorBounded m n A b x_hat eta)
    (heta' : 0 ≤ eta')
    (hle : eta ≤ eta') :
    UndetRowwiseBackwardErrorBounded m n A b x_hat eta' := by
  rcases hcert with ⟨DeltaA, hfeas⟩
  refine ⟨DeltaA, ?_⟩
  refine ⟨heta', hfeas.min_norm, ?_⟩
  intro i
  exact le_trans (hfeas.row_bound i)
    (mul_le_mul_of_nonneg_right hle (rectRowNorm2_nonneg A i))

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    once the Lemma 21.2 single perturbation is known to make `x_hat` a
    minimum-norm solution, common row-wise relative bounds on the two source
    perturbations give a row-wise backward-error witness with factor
    `sqrt 2 * eta`. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hmin :
      RectMinNormSolution m n
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        b x_hat)
    (hDeltaA1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat (Real.sqrt 2 * eta) :=
  higham21_rowwise_backward_error_bound_witness m n A
    (undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2) b x_hat
    (Real.sqrt 2 * eta)
    (mul_nonneg (Real.sqrt_nonneg 2) heta)
    hmin
    (fun i => by
      simpa [mul_assoc] using
        higham21_lemma21_2_single_perturbation_row_bound_of_common_row_bound
          x_hat A DeltaA1 DeltaA2 heta hDeltaA1 hDeltaA2 i)

/-- Higham's row-scaled condition number with a supplied pseudoinverse:
    the exact operator norm of |Aplus| |A|. -/
noncomputable def higham21Cond2With
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ) : ℝ :=
  complexMatrixOp2
    (realRectToCMatrix
      (rectMatMul (absMatrixRect Aplus) (absMatrixRect A)))

theorem higham21Cond2With_nonneg
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ) :
    0 ≤ higham21Cond2With A Aplus :=
  complexMatrixOp2_nonneg _

/-- A common relative row bound implies the exact pseudoinverse-product
    radius used by Lemma 21.2. -/
theorem higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
    {m n : ℕ}
    (A Delta : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (eta : ℝ)
    (heta : 0 ≤ eta)
    (hrow : ∀ i : Fin m,
      rectRowNorm2 Delta i ≤ eta * rectRowNorm2 A i) :
    rectOpNorm2Le (rectMatMul Aplus Delta)
      (eta * Real.sqrt (n : ℝ) * higham21Cond2With A Aplus) := by
  let C : Fin n → Fin n → ℝ :=
    rectMatMul (absMatrixRect Aplus) (absMatrixRect A)
  let one : Fin n → ℝ := fun _ => 1
  have honeNorm : vecNorm2 one = Real.sqrt (n : ℝ) := by
    simp [one, vecNorm2, vecNorm2Sq, Finset.sum_const, Fintype.card_fin]
  have hrow_l1 : ∀ i : Fin m,
      rectRowNorm2 A i ≤
        rectMatMulVec (absMatrixRect A) one i := by
    intro i
    let s : ℝ := ∑ j : Fin n, |A i j|
    have hsum_nonneg : 0 ≤ s :=
      Finset.sum_nonneg (fun j _ => abs_nonneg (A i j))
    have hsq :
        vecNorm2Sq (fun j : Fin n => A i j) ≤ s ^ 2 := by
      dsimp only [s]
      exact vecNorm2Sq_le_sum_abs_sq (fun j : Fin n => A i j)
    have hnorm :
        vecNorm2 (fun j : Fin n => A i j) ≤ s := by
      unfold vecNorm2
      calc
        Real.sqrt (vecNorm2Sq (fun j : Fin n => A i j)) ≤
            Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hsq
        _ = s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg]
    simpa [s, rectRowNorm2, rectMatMulVec, absMatrixRect, one] using hnorm
  have hCop :
      rectOpNorm2Le C (higham21Cond2With A Aplus) := by
    simpa [C, higham21Cond2With] using
      (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le C le_rfl)
  intro x
  rw [rectMatMulVec_rectMatMul]
  have hDeltaAction : ∀ i : Fin m,
      |rectMatMulVec Delta x i| ≤
        eta * rectRowNorm2 A i * vecNorm2 x := by
    intro i
    have hcs :
        |rectMatMulVec Delta x i| ≤
          rectRowNorm2 Delta i * vecNorm2 x := by
      simpa [rectMatMulVec, rectRowNorm2] using
        (abs_vecInnerProduct_le_vecNorm2_mul
          (fun j : Fin n => Delta i j) x)
    calc
      |rectMatMulVec Delta x i| ≤
          rectRowNorm2 Delta i * vecNorm2 x := hcs
      _ ≤ (eta * rectRowNorm2 A i) * vecNorm2 x :=
        mul_le_mul_of_nonneg_right (hrow i) (vecNorm2_nonneg x)
      _ = eta * rectRowNorm2 A i * vecNorm2 x := rfl
  have hDeltaBudget : ∀ i : Fin m,
      |rectMatMulVec Delta x i| ≤
        eta * rectMatMulVec (absMatrixRect A) one i * vecNorm2 x := by
    intro i
    calc
      |rectMatMulVec Delta x i| ≤
          eta * rectRowNorm2 A i * vecNorm2 x := hDeltaAction i
      _ ≤ eta * rectMatMulVec (absMatrixRect A) one i * vecNorm2 x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hrow_l1 i) heta)
          (vecNorm2_nonneg x)
  have hpoint : ∀ i : Fin n,
      |rectMatMulVec Aplus (rectMatMulVec Delta x) i| ≤
        (eta * vecNorm2 x) * rectMatMulVec C one i := by
    intro i
    calc
      |rectMatMulVec Aplus (rectMatMulVec Delta x) i| ≤
          ∑ k : Fin m,
            |Aplus i k| * |rectMatMulVec Delta x k| :=
        abs_rectMatMulVec_le Aplus (rectMatMulVec Delta x) i
      _ ≤ ∑ k : Fin m,
            |Aplus i k| *
              (eta * rectMatMulVec (absMatrixRect A) one k *
                vecNorm2 x) := by
        exact Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hDeltaBudget k)
            (abs_nonneg (Aplus i k)))
      _ = (eta * vecNorm2 x) * rectMatMulVec C one i := by
        rw [show rectMatMulVec C one =
            rectMatMulVec (absMatrixRect Aplus)
              (rectMatMulVec (absMatrixRect A) one) by
          exact rectMatMulVec_rectMatMul
            (absMatrixRect Aplus) (absMatrixRect A) one]
        simp only [rectMatMulVec, absMatrixRect]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have haction :
      vecNorm2
          (rectMatMulVec Aplus (rectMatMulVec Delta x)) ≤
        (eta * vecNorm2 x) *
          vecNorm2 (rectMatMulVec C one) := by
    calc
      vecNorm2 (rectMatMulVec Aplus (rectMatMulVec Delta x)) ≤
          vecNorm2
            (fun i : Fin n =>
              (eta * vecNorm2 x) * rectMatMulVec C one i) :=
        vecNorm2_le_of_abs_le _ _ hpoint
      _ = (eta * vecNorm2 x) *
            vecNorm2 (rectMatMulVec C one) := by
        rw [vecNorm2_smul, abs_of_nonneg
          (mul_nonneg heta (vecNorm2_nonneg x))]
  calc
    vecNorm2 (rectMatMulVec Aplus (rectMatMulVec Delta x)) ≤
        (eta * vecNorm2 x) *
          vecNorm2 (rectMatMulVec C one) := haction
    _ ≤ (eta * vecNorm2 x) *
          (higham21Cond2With A Aplus * vecNorm2 one) :=
      mul_le_mul_of_nonneg_left (hCop one)
        (mul_nonneg heta (vecNorm2_nonneg x))
    _ = (eta * Real.sqrt (n : ℝ) *
          higham21Cond2With A Aplus) * vecNorm2 x := by
      rw [honeNorm]
      ring

theorem higham21_sqrt_nat_le_nat (n : ℕ) :
    Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hone_le : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hself : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      calc
        (n : ℝ) = (n : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hone_le hn_nonneg
        _ = (n : ℝ) ^ 2 := by ring
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hself
      _ = (n : ℝ) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hn_nonneg]

theorem higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds_nat_factor
    {m n : ℕ}
    (A Delta : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (eta : ℝ)
    (heta : 0 ≤ eta)
    (hrow : ∀ i : Fin m,
      rectRowNorm2 Delta i ≤ eta * rectRowNorm2 A i) :
    rectOpNorm2Le (rectMatMul Aplus Delta)
      (eta * (n : ℝ) * higham21Cond2With A Aplus) := by
  apply rectOpNorm2Le_mono
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (higham21_sqrt_nat_le_nat n) heta)
      (higham21Cond2With_nonneg A Aplus))
  exact
    higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
      A Delta Aplus eta heta hrow

set_option maxHeartbeats 1200000
/-- Higham, 2nd ed., Chapter 21, Lemma 21.2: the minimum-norm core of the
    printed pseudoinverse-product argument.  This separates the source lemma's
    constructed perturbation from the later row-wise backward-error wrapper. -/
theorem higham21_lemma21_2_single_min_norm_of_pseudoinverse_products
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (rho1 rho2 : ℝ)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho1)
    (hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho2)
    (hsmall : 3 * max rho1 rho2 < 1) :
    RectMinNormSolution m n
      (fun i j =>
        A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  by_cases hx : x = 0
  case pos =>
    have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hFirst
    simpa [undetLemma21_2SinglePerturbation, hx] using hzero
  case neg =>
    let z : Fin n → ℝ := rectMatMulVec (finiteTranspose A) y
    have hrho1 : 0 ≤ rho1 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA1) hx hProd1
    have hrho2 : 0 ≤ rho2 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA2) hx hProd2
    have hAplusTz :
        rectMatMulVec (finiteTranspose Aplus) z = y := by
      calc
        rectMatMulVec (finiteTranspose Aplus) z =
            rectMatMulVec (finiteTranspose (rectMatMul A Aplus)) y := by
              simpa [z] using
                (higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
                  Aplus A y)
        _ = rectMatMulVec (finiteTranspose (idMatrix m)) y := by
          rw [hRight]
        _ = y := by
          ext i
          simp [rectMatMulVec, finiteTranspose, idMatrix]
    have hDeltaA2T :
        rectMatMulVec (finiteTranspose DeltaA2) y =
          rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z := by
      rw [hAplusTz.symm]
      exact
        higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
          DeltaA2 Aplus z
    have hSecondMat :
        x = rectMatMulVec
          (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y := by
      simpa [rectTransposeMulVec, rectMatMulVec, finiteTranspose] using hSecond
    have hxsum :
        x = fun j =>
          z j +
            rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
      calc
        x = rectMatMulVec
              (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y :=
          hSecondMat
        _ = fun j =>
              rectMatMulVec (finiteTranspose A) y j +
                rectMatMulVec (finiteTranspose DeltaA2) y j := by
              simpa [finiteTranspose] using
                (rectMatMulVec_mat_add
                  (finiteTranspose A) (finiteTranspose DeltaA2) y)
        _ = fun j =>
              z j +
                rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
              rw [hDeltaA2T]
    have hProd2T :
        rectOpNorm2Le (finiteTranspose (rectMatMul Aplus DeltaA2)) rho2 :=
      rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
        (rectMatMul Aplus DeltaA2) hrho2 hProd2
    have hcancel :
        (fun j =>
          x j +
            -rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j) = z := by
      ext j
      have hj := congrFun hxsum j
      linarith
    have htri :=
      vecNorm2_add_le x
        (fun j =>
          -rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z j)
    rw [hcancel, vecNorm2_neg] at htri
    have hlower :
        (1 - rho2) * vecNorm2 z ≤ vecNorm2 x := by
      calc
        (1 - rho2) * vecNorm2 z =
            vecNorm2 z - rho2 * vecNorm2 z := by ring
        _ ≤ vecNorm2 z -
              vecNorm2
                (rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z) :=
            sub_le_sub_left (hProd2T z) _
        _ ≤ vecNorm2 x := (sub_le_iff_le_add).2 htri
    have hden : 0 < 1 - rho2 := by
      have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
      nlinarith
    have hz :
        vecNorm2 z ≤ (1 / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2 z =
            ((1 - rho2) * vecNorm2 z) / (1 - rho2) := by
              field_simp [ne_of_gt hden]
        _ ≤ vecNorm2 x / (1 - rho2) :=
              (div_le_div_iff_of_pos_right hden).2 hlower
        _ = (1 / (1 - rho2)) * vecNorm2 x := by
              simp only [div_eq_mul_inv, one_mul, mul_comm]
    have hProductSub :
        rectOpNorm2Le
          (rectMatMul Aplus (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rho1 + rho2) := by
      rw [rectMatMul_sub_right]
      exact
        rectOpNorm2Le_sub
          (rectMatMul Aplus DeltaA1) (rectMatMul Aplus DeltaA2)
          hProd1 hProd2
    have hActionZ :=
      higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
        z DeltaA1 DeltaA2 Aplus (add_nonneg hrho1 hrho2) hProductSub
    rw [hAplusTz] at hActionZ
    have hAction :
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
          ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y)
            ≤ (rho1 + rho2) * vecNorm2 z := hActionZ
        _ ≤ (rho1 + rho2) *
              ((1 / (1 - rho2)) * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left hz (add_nonneg hrho1 hrho2)
        _ = ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
            simp [div_eq_mul_inv, mul_assoc]
    have hsq : ¬ vecNorm2Sq x = 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hminSym :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
        A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hFirst hSecondMat.symm
        hsmall hAction
    simpa [undetLemma21_2SinglePerturbation, hx] using hminSym

/-- Direct Lemma 21.2 row-wise handoff from the printed pseudoinverse-product
    smallness condition.  The proof constructs the source symmetrization in
    the nonzero branch and uses the second perturbation in the zero branch. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (rho1 rho2 eta : ℝ)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho1)
    (hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho2)
    (hsmall : 3 * max rho1 rho2 < 1)
    (heta : 0 ≤ eta)
    (hrow1 : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hrow2 : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x (Real.sqrt 2 * eta) := by
  by_cases hx : x = 0
  case pos =>
    have hzero :
        RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x :=
      higham21_lemma21_2_zero_branch_min_norm_of_deltaA2
        A x DeltaA1 DeltaA2 b hx hFirst
    have hmin :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
          b x := by
      simpa [undetLemma21_2SinglePerturbation, hx] using hzero
    exact
      higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
        A DeltaA1 DeltaA2 b x heta hmin hrow1 hrow2
  case neg =>
    let z : Fin n → ℝ := rectMatMulVec (finiteTranspose A) y
    have hrho1 : 0 ≤ rho1 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA1) hx hProd1
    have hrho2 : 0 ≤ rho2 :=
      higham21_lemma21_2_op_radius_nonneg_of_vec_ne_zero
        (x := x) (rectMatMul Aplus DeltaA2) hx hProd2
    have hAplusTz :
        rectMatMulVec (finiteTranspose Aplus) z = y := by
      calc
        rectMatMulVec (finiteTranspose Aplus) z =
            rectMatMulVec (finiteTranspose (rectMatMul A Aplus)) y := by
              simpa [z] using
                (higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
                  Aplus A y)
        _ = rectMatMulVec (finiteTranspose (idMatrix m)) y := by
          rw [hRight]
        _ = y := by
          ext i
          simp [rectMatMulVec, finiteTranspose, idMatrix]
    have hDeltaA2T :
        rectMatMulVec (finiteTranspose DeltaA2) y =
          rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z := by
      rw [hAplusTz.symm]
      exact
        higham21_lemma21_2_pseudoinverse_transpose_action_eq_domain_projection
          DeltaA2 Aplus z
    have hSecondMat :
        x = rectMatMulVec
          (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y := by
      simpa [rectTransposeMulVec, rectMatMulVec, finiteTranspose] using hSecond
    have hxsum :
        x = fun j =>
          z j +
            rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
      calc
        x = rectMatMulVec
              (finiteTranspose (fun i j => A i j + DeltaA2 i j)) y :=
          hSecondMat
        _ = fun j =>
              rectMatMulVec (finiteTranspose A) y j +
                rectMatMulVec (finiteTranspose DeltaA2) y j := by
              simpa [finiteTranspose] using
                (rectMatMulVec_mat_add
                  (finiteTranspose A) (finiteTranspose DeltaA2) y)
        _ = fun j =>
              z j +
                rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z j := by
              rw [hDeltaA2T]
    have hProd2T :
        rectOpNorm2Le (finiteTranspose (rectMatMul Aplus DeltaA2)) rho2 :=
      rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
        (rectMatMul Aplus DeltaA2) hrho2 hProd2
    have hcancel :
        (fun j =>
          x j +
            -rectMatMulVec
              (finiteTranspose (rectMatMul Aplus DeltaA2)) z j) = z := by
      ext j
      have hj := congrFun hxsum j
      linarith
    have htri :=
      vecNorm2_add_le x
        (fun j =>
          -rectMatMulVec
            (finiteTranspose (rectMatMul Aplus DeltaA2)) z j)
    rw [hcancel, vecNorm2_neg] at htri
    have hlower :
        (1 - rho2) * vecNorm2 z ≤ vecNorm2 x := by
      calc
        (1 - rho2) * vecNorm2 z =
            vecNorm2 z - rho2 * vecNorm2 z := by ring
        _ ≤ vecNorm2 z -
              vecNorm2
                (rectMatMulVec
                  (finiteTranspose (rectMatMul Aplus DeltaA2)) z) :=
            sub_le_sub_left (hProd2T z) _
        _ ≤ vecNorm2 x := (sub_le_iff_le_add).2 htri
    have hden : 0 < 1 - rho2 := by
      have hrho2_le : rho2 ≤ max rho1 rho2 := le_max_right rho1 rho2
      nlinarith
    have hz :
        vecNorm2 z ≤ (1 / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2 z =
            ((1 - rho2) * vecNorm2 z) / (1 - rho2) := by
              field_simp [ne_of_gt hden]
        _ ≤ vecNorm2 x / (1 - rho2) :=
              (div_le_div_iff_of_pos_right hden).2 hlower
        _ = (1 / (1 - rho2)) * vecNorm2 x := by
              simp only [div_eq_mul_inv, one_mul, mul_comm]
    have hProductSub :
        rectOpNorm2Le
          (rectMatMul Aplus (fun i j => DeltaA1 i j - DeltaA2 i j))
          (rho1 + rho2) := by
      rw [rectMatMul_sub_right]
      exact
        rectOpNorm2Le_sub
          (rectMatMul Aplus DeltaA1) (rectMatMul Aplus DeltaA2)
          hProd1 hProd2
    have hActionZ :=
      higham21_lemma21_2_transpose_action_bound_of_pseudoinverse_product_bound
        z DeltaA1 DeltaA2 Aplus (add_nonneg hrho1 hrho2) hProductSub
    rw [hAplusTz] at hActionZ
    have hAction :
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y) ≤
          ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
      calc
        vecNorm2
            (rectMatMulVec
              (finiteTranspose (fun i j => DeltaA1 i j - DeltaA2 i j)) y)
            ≤ (rho1 + rho2) * vecNorm2 z := hActionZ
        _ ≤ (rho1 + rho2) *
              ((1 / (1 - rho2)) * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left hz (add_nonneg hrho1 hrho2)
        _ = ((rho1 + rho2) / (1 - rho2)) * vecNorm2 x := by
            simp [div_eq_mul_inv, mul_assoc]
    have hsq : ¬ vecNorm2Sq x = 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hx
    have hminSym :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SymmetrizedPerturbation x DeltaA1 DeltaA2 i j)
          b x :=
      higham21_lemma21_2_symmetrized_min_norm_of_transpose_action_bound
        A x DeltaA1 DeltaA2 b y rho1 rho2 hsq hFirst hSecondMat.symm
        hsmall hAction
    have hmin :
        RectMinNormSolution m n
          (fun i j =>
            A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
          b x := by
      simpa [undetLemma21_2SinglePerturbation, hx] using hminSym
    exact
      higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
        A DeltaA1 DeltaA2 b x heta hmin hrow1 hrow2

/-- The exact operator-2 norm of the source product `A^+ DeltaA` appearing in
    the smallness hypothesis of Lemma 21.2. -/
noncomputable def higham21Lemma21_2ProductNorm2 {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) : ℝ :=
  complexMatrixOp2
    (realRectToCMatrix
      (rectMatMul (undetAplusOfGramNonsingInv A) DeltaA))

/-- Canonical minimum-norm core of Lemma 21.2, with the source smallness
    condition stated using exact operator norms rather than supplied radii. -/
theorem higham21_lemma21_2_single_min_norm_of_exact_product_norms
    {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall :
      3 * max (higham21Lemma21_2ProductNorm2 A DeltaA1)
          (higham21Lemma21_2ProductNorm2 A DeltaA2) < 1)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    RectMinNormSolution m n
      (fun i j =>
        A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x := by
  let Aplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv A
  let rho1 : ℝ := higham21Lemma21_2ProductNorm2 A DeltaA1
  let rho2 : ℝ := higham21Lemma21_2ProductNorm2 A DeltaA2
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho1 := by
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
      (rectMatMul Aplus DeltaA1)
      (by simp [rho1, higham21Lemma21_2ProductNorm2, Aplus])
  have hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho2 := by
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
      (rectMatMul Aplus DeltaA2)
      (by simp [rho2, higham21Lemma21_2ProductNorm2, Aplus])
  exact
    higham21_lemma21_2_single_min_norm_of_pseudoinverse_products
      A Aplus DeltaA1 DeltaA2 b x y rho1 rho2 hRight hFirst hSecond
      hProd1 hProd2 (by simpa [rho1, rho2] using hsmall)

/-- The source-case perturbation is literally
    `DeltaA1 G1 + DeltaA2 G2`, with `G1 = xx^T/(x^T x)` and `G2 = I-G1`.
    In the zero branch this reads `G1=0`, `G2=I`, and `DeltaA=DeltaA2`. -/
theorem higham21_lemma21_2_single_perturbation_eq_projector_mixture
    {m n : ℕ} (x : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j =
      matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j := by
  by_cases hx : x = 0
  · subst x
    have hP :
        lsLemma20_6Projector (0 : Fin n → ℝ) =
          (0 : Fin n → Fin n → ℝ) := by
      ext a c
      simp [lsLemma20_6Projector]
    have hQ :
        lsLemma20_6ProjectorComplement (0 : Fin n → ℝ) =
          idMatrix n := by
      ext a c
      simp [lsLemma20_6ProjectorComplement, hP]
    have hid : matMulRectRight DeltaA2 (idMatrix n) i j = DeltaA2 i j := by
      have h := congrFun (congrFun (rectMatMul_id_right DeltaA2) i) j
      simpa [rectMatMul, matMulRectRight] using h
    simp only [undetLemma21_2SinglePerturbation, hP, hQ, hid]
    simp [matMulRectRight]
  · simpa [undetLemma21_2SinglePerturbation, hx] using
      higham21_lemma21_2_symmetrized_perturbation_eq_right_projector_mixture
        x DeltaA1 DeltaA2 i j

/-- The rank-one source projector is idempotent also in the `x=0` branch. -/
theorem higham21_lemma21_2_projector_idempotent_all {n : ℕ}
    (x : Fin n → ℝ) :
    matMul n (lsLemma20_6Projector x) (lsLemma20_6Projector x) =
      lsLemma20_6Projector x := by
  by_cases hx : x = 0
  · subst x
    ext i j
    simp [matMul, lsLemma20_6Projector]
  · exact lsLemma20_6Projector_idempotent x
      (higham21_vecNorm2Sq_ne_zero_of_ne_zero hx)

/-- A source-facing bundle for Higham's Lemma 21.2.  It records the explicit
    projector construction, an exact transpose witness, minimum-norm recovery,
    and the printed `p=2` and Frobenius square-sum norm bounds. -/
structure Higham21Lemma21_2SourceBundle {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop where
  min_norm :
    RectMinNormSolution m n
      (fun i j =>
        A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
      b x
  transpose_witness : ∃ dual : Fin m → ℝ,
    x = rectTransposeMulVec
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j)
        dual
  projector_mixture : ∀ i j,
    undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2 i j =
      matMulRectRight DeltaA1 (lsLemma20_6Projector x) i j +
        matMulRectRight DeltaA2 (lsLemma20_6ProjectorComplement x) i j
  projector_symmetric :
    IsSymmetricFiniteMatrix (lsLemma20_6Projector x)
  projector_idempotent :
    matMul n (lsLemma20_6Projector x) (lsLemma20_6Projector x) =
      lsLemma20_6Projector x
  projector_sum : ∀ i j,
    lsLemma20_6Projector x i j +
      lsLemma20_6ProjectorComplement x i j = idMatrix n i j
  op2_bound :
    complexMatrixOp2
        (realRectToCMatrix
          (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)) ≤
      Real.sqrt
        (complexMatrixOp2 (realRectToCMatrix DeltaA1) ^ 2 +
          complexMatrixOp2 (realRectToCMatrix DeltaA2) ^ 2)
  frobenius_bound :
    frobNormRect
        (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2) ≤
      Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 (Kielbasinski--Schwetlick),
    canonical exact-norm formulation.  Full row rank is represented by Gram
    nonsingularity; `m <= n` is retained explicitly from the source statement. -/
theorem higham21_lemma21_2_source_bundle
    {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (_hmn : m ≤ n)
    (hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hFirst :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x = b)
    (hSecond :
      x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall :
      3 * max (higham21Lemma21_2ProductNorm2 A DeltaA1)
          (higham21Lemma21_2ProductNorm2 A DeltaA2) < 1) :
    Higham21Lemma21_2SourceBundle A DeltaA1 DeltaA2 b x := by
  have hmin :=
    higham21_lemma21_2_single_min_norm_of_exact_product_norms
      A DeltaA1 DeltaA2 b x y hFirst hSecond hsmall hdet
  obtain ⟨ytilde, hytilde⟩ :=
    RectMinNormSolution.exists_transpose_witness hmin
  refine
    { min_norm := hmin
      transpose_witness := ⟨ytilde, hytilde.symm⟩
      projector_mixture := ?_
      projector_symmetric := ?_
      projector_idempotent := ?_
      projector_sum := ?_
      op2_bound := ?_
      frobenius_bound := ?_ }
  · intro i j
    exact higham21_lemma21_2_single_perturbation_eq_projector_mixture
      x DeltaA1 DeltaA2 i j
  · intro i j
    exact lsLemma20_6Projector_symmetric x i j
  · exact higham21_lemma21_2_projector_idempotent_all x
  · intro i j
    exact lsLemma20_6Projector_add_complement x i j
  · let alpha : ℝ := complexMatrixOp2 (realRectToCMatrix DeltaA1)
    let beta : ℝ := complexMatrixOp2 (realRectToCMatrix DeltaA2)
    have hOp :
        rectOpNorm2Le
          (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)
          (Real.sqrt (alpha ^ 2 + beta ^ 2)) :=
      higham21_lemma21_2_single_perturbation_op_bound
        x DeltaA1 DeltaA2
        (by
          simpa [alpha] using
            (complexMatrixOp2_nonneg (realRectToCMatrix DeltaA1)))
        (by
          simpa [beta] using
            (complexMatrixOp2_nonneg (realRectToCMatrix DeltaA2)))
        (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
          DeltaA1 le_rfl)
        (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
          DeltaA2 le_rfl)
    simpa [alpha, beta] using
      (complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
        (undetLemma21_2SinglePerturbation x DeltaA1 DeltaA2)
        (Real.sqrt_nonneg _) hOp)
  · exact higham21_lemma21_2_single_perturbation_frob_bound
      x DeltaA1 DeltaA2

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff with a common source radius
    `rho`.  This version matches the printed smallness/radius shape more
    directly than the self-radius wrapper while still leaving the QR/Q-method
    row-bound obligations explicit. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    A DeltaA1 DeltaA2 b x_hat heta
    (higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_common_radius_printed_smallness_common_radius_combined_factor_global_bounds
      hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E rho eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hRadiusFactor hSourceRadius
      hGramLeftInv hDataE hDeltaA1Component hDeltaA2Component
      hxTranspose hsmall hAATInv_le hAOp)
    hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    common-radius row-wise handoff from entrywise row-relative perturbation
    bounds. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_entrywise_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (rho eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Entry : ∀ i k, |DeltaA1 i k| ≤ eta * |A i k|)
    (hDeltaA2Entry : ∀ i k, |DeltaA2 i k| ≤ eta * |A i k|) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E rho eps tauA omega e eta
    hDeltaA1 hDataEpsNonneg hEOp hRadiusFactor hSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose hsmall
    hAATInv_le hAOp heta
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA1 heta hDeltaA1Entry i)
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA2 heta hDeltaA2Entry i)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    common-radius row-wise handoff specialized to the relative componentwise
    data majorant `E = |A|`. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_abs_data_source_operator_envelopes_exact_size_eps_common_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (rho eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hAbsAOp : rectOpNorm2Le (fun i j => |A i j|) e)
    (hRadiusFactor :
      max (eps * e)
          (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤ rho)
    (hSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega * rho ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * |A i k|)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * |A i k|)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hsmall : 3 * rho < 1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eps) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_common_radius_global_entrywise_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv (fun i j => |A i j|)
    rho eps tauA omega e eps hDeltaA1 hDataEpsNonneg hAbsAOp
    hRadiusFactor hSourceRadius hGramLeftInv
    (fun i k => abs_nonneg (A i k))
    hDeltaA1Component hDeltaA2Component hxTranspose hsmall hAATInv_le
    hAOp hDataEpsNonneg hDeltaA1Component hDeltaA2Component

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff.  The latest
    source-envelope version of Lemma 21.2 supplies the single perturbed
    minimum-norm system, and common row-wise source perturbation bounds then
    package it as the row-wise backward-error predicate used in Theorem 21.4. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
    A DeltaA1 DeltaA2 b x_hat heta
    (higham21_lemma21_2_single_min_norm_of_nonzero_branch_conservative_ch7_factor_deltaA_components_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
      hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e
      hDeltaA1 hDataEpsNonneg hEOp hCombinedSourceRadius hGramLeftInv
      hDataE hDeltaA1Component hDeltaA2Component hxTranspose
      hCombinedSmall hAATInv_le hAOp)
    hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff from entrywise row-relative
    perturbation bounds.  This is a stronger sufficient condition for the
    row-wise hypotheses consumed by Theorem 21.4. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_entrywise_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (E : Fin m → Fin n → ℝ)
    (eps tauA omega e eta : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hEOp : rectOpNorm2Le E e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDataE : ∀ i k, 0 ≤ E i k)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * E i k)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * E i k)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA)
    (heta : 0 ≤ eta)
    (hDeltaA1Entry : ∀ i k, |DeltaA1 i k| ≤ eta * |A i k|)
    (hDeltaA2Entry : ∀ i k, |DeltaA2 i k| ≤ eta * |A i k|) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eta) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv E eps tauA omega e eta
    hDeltaA1 hDataEpsNonneg hEOp hCombinedSourceRadius hGramLeftInv
    hDataE hDeltaA1Component hDeltaA2Component hxTranspose
    hCombinedSmall hAATInv_le hAOp heta
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA1 heta hDeltaA1Entry i)
    (fun i =>
      higham21_rectRowNorm2_le_of_entrywise_row_relative_bound
        A DeltaA2 heta hDeltaA2Entry i)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2 and Section 21.3:
    source-shaped row-wise backward-error handoff specialized to the relative
    componentwise data majorant `E = |A|`.  The componentwise perturbation
    bounds then supply the row-wise hypotheses directly. -/
theorem higham21_lemma21_2_rowwise_backward_error_bound_of_abs_data_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_bounds
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin m → Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (y : Fin m → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (eps tauA omega e : ℝ)
    (hDeltaA1 :
      rectMatMulVec (fun i j => A i j + DeltaA1 i j) x_hat = b)
    (hDataEpsNonneg : 0 ≤ eps)
    (hAbsAOp : rectOpNorm2Le (fun i j => |A i j|) e)
    (hCombinedSourceRadius :
      2 * (m : ℝ) * (n : ℝ) * (tauA + eps * e) * omega *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) ≤
        (1 / 2 : ℝ))
    (hGramLeftInv : IsLeftInverse m (rectGram A) AAT_inv)
    (hDeltaA1Component : ∀ i k, |DeltaA1 i k| ≤ eps * |A i k|)
    (hDeltaA2Component : ∀ i k, |DeltaA2 i k| ≤ eps * |A i k|)
    (hxTranspose : x_hat ≠ 0 →
      x_hat =
        rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y)
    (hCombinedSmall :
      3 *
          max (eps * e)
            (2 * (m : ℝ) ^ 2 * (tauA + eps * e) * omega) <
        1)
    (hAATInv_le : infNorm AAT_inv ≤ omega)
    (hAOp : rectOpNorm2Le A tauA) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat
      (Real.sqrt 2 * eps) :=
  higham21_lemma21_2_rowwise_backward_error_bound_of_source_operator_envelopes_exact_size_eps_combined_factor_self_radius_global_entrywise_bounds
    hm A x_hat DeltaA1 DeltaA2 b y AAT_inv (fun i j => |A i j|)
    eps tauA omega e eps hDeltaA1 hDataEpsNonneg hAbsAOp
    hCombinedSourceRadius hGramLeftInv
    (fun i k => abs_nonneg (A i k))
    hDeltaA1Component hDeltaA2Component hxTranspose hCombinedSmall
    hAATInv_le hAOp hDataEpsNonneg hDeltaA1Component hDeltaA2Component

-- ============================================================
-- §21.2  Theorem 21.3: normwise backward-error model
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    feasibility predicate for the normwise Frobenius backward error
    `eta_F(y)` of an approximate minimum 2-norm underdetermined solution.

    This reuses the Chapter 20 weighted Frobenius perturbation cost
    `||[DeltaA, theta Delta b]||_F`; the Ch21-specific change is that `y`
    must be a minimum 2-norm solution of the perturbed rectangular system. -/
def UndetNormwiseBackwardErrorFeasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) : Prop :=
  RectMinNormSolution m n
    (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) y

/-- Attainable weighted Frobenius costs in the Chapter 21 Theorem 21.3
    normwise backward-error definition. -/
noncomputable def undetNormwiseBackwardErrorValuesF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Set ℝ :=
  {eta | ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
    UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
      eta = lsNormwiseBackwardErrorCostF theta DeltaA Deltab}

/-- Infimum model of Higham Chapter 21 Theorem 21.3's normwise backward
    error `eta_F(y)`.  The source writes a minimum and gives the Sun-Sun
    closed formula; those attainment and singular-value formula rows remain
    separate selected targets. -/
noncomputable def undetNormwiseBackwardErrorEtaF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sInf (undetNormwiseBackwardErrorValuesF theta A b y)

/-- The Chapter 21 attainable-cost set is bounded below by zero. -/
theorem undetNormwiseBackwardErrorValuesF.bddBelow {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    BddBelow (undetNormwiseBackwardErrorValuesF theta A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab

/-- The Chapter 21 normwise backward-error infimum model is nonnegative. -/
theorem undetNormwiseBackwardErrorEtaF_nonneg {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    0 ≤ undetNormwiseBackwardErrorEtaF theta A b y := by
  unfold undetNormwiseBackwardErrorEtaF
  apply Real.sInf_nonneg
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab

/-- Any feasible Chapter 21 normwise perturbation gives an upper bound on
    the infimum model `eta_F(y)`. -/
theorem undetNormwiseBackwardErrorEtaF_le_costF_of_feasible
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas :
      UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetNormwiseBackwardErrorEtaF theta A b y ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  unfold undetNormwiseBackwardErrorEtaF
  exact csInf_le (undetNormwiseBackwardErrorValuesF.bddBelow theta A b y)
    ⟨DeltaA, Deltab, hfeas, rfl⟩

/-- Zero is an attainable Chapter 21 normwise backward-error cost when `y`
    is already a minimum 2-norm solution of the original data. -/
theorem undetNormwiseBackwardErrorValuesF.zero_mem_of_rectMinNormSolution
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hmin : RectMinNormSolution m n A b y) :
    (0 : ℝ) ∈ undetNormwiseBackwardErrorValuesF theta A b y := by
  rw [← lsNormwiseBackwardErrorCostF_zero (m := m) (n := n) theta]
  refine ⟨(0 : Fin m → Fin n → ℝ), (0 : Fin m → ℝ), ?_, rfl⟩
  simpa [UndetNormwiseBackwardErrorFeasible] using hmin

/-- If `y` is already a minimum 2-norm solution of the original data, then
    the Chapter 21 infimum model gives zero backward error. -/
theorem undetNormwiseBackwardErrorEtaF_eq_zero_of_rectMinNormSolution
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hmin : RectMinNormSolution m n A b y) :
    undetNormwiseBackwardErrorEtaF theta A b y = 0 := by
  apply le_antisymm
  · unfold undetNormwiseBackwardErrorEtaF
    exact csInf_le (undetNormwiseBackwardErrorValuesF.bddBelow theta A b y)
      (undetNormwiseBackwardErrorValuesF.zero_mem_of_rectMinNormSolution
        theta A b y hmin)
  · exact undetNormwiseBackwardErrorEtaF_nonneg theta A b y

/-- In the Chapter 21 Theorem 21.3 weighted Frobenius model, perturbing only
    the right-hand side by `-b` has cost `theta * ||b||_2`, for nonnegative
    source weight `theta`. -/
theorem undetNormwiseBackwardErrorCostF_zero_deltaA_neg_deltab
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta) (b : Fin m → ℝ) :
    lsNormwiseBackwardErrorCostF (m := m) (n := n) theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i) = theta * vecNorm2 b := by
  have hleft : 0 ≤ lsNormwiseBackwardErrorCostF theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i) :=
    lsNormwiseBackwardErrorCostF_nonneg theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i)
  have hright : 0 ≤ theta * vecNorm2 b :=
    mul_nonneg htheta (vecNorm2_nonneg b)
  apply (sq_eq_sq₀ hleft hright).mp
  rw [lsNormwiseBackwardErrorCostF_sq]
  rw [show frobNormSqRect (0 : Fin m → Fin n → ℝ) = 0 by
    simp [frobNormSqRect]]
  have hneg : vecNorm2Sq (fun i : Fin m => -b i) = vecNorm2Sq b := by
    unfold vecNorm2Sq
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg]
  rw [show (theta * vecNorm2 b) ^ 2 = theta ^ 2 * vecNorm2 b ^ 2 by ring]
  rw [vecNorm2_sq]
  ring

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    the source zero-vector candidate `y = 0` has attainable cost
    `theta * ||b||_2` in the underdetermined normwise backward-error model. -/
theorem undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    theta * vecNorm2 b ∈
      undetNormwiseBackwardErrorValuesF theta A b (0 : Fin n → ℝ) := by
  refine ⟨(0 : Fin m → Fin n → ℝ), (fun i => -b i), ?_, ?_⟩
  · unfold UndetNormwiseBackwardErrorFeasible
    constructor
    · ext i
      simp [rectMatMulVec]
    · intro z _hz
      change vecNorm2 (fun _ : Fin n => 0) ≤ vecNorm2 z
      rw [vecNorm2_zero]
      exact vecNorm2_nonneg z
  · exact (undetNormwiseBackwardErrorCostF_zero_deltaA_neg_deltab
      theta htheta b).symm

/-- Any feasible perturbation for the Chapter 21 zero-vector candidate must
    pay at least the weighted right-hand-side cost `theta * ||b||_2`. -/
theorem undetNormwiseBackwardErrorCostF_ge_theta_vecNorm_of_zero_feasible
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas :
      UndetNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ) DeltaA Deltab) :
    theta * vecNorm2 b ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  have hDeltab : Deltab = fun i : Fin m => -b i := by
    ext i
    have hi := congrFun hfeas.system_eq i
    have hzero : (0 : ℝ) = b i + Deltab i := by
      simpa [rectMatMulVec] using hi
    linarith
  have hweighted : theta * vecNorm2 Deltab ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_weighted_deltab_le htheta DeltaA Deltab
  simpa [hDeltab, vecNorm2_neg] using hweighted

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    zero-vector branch of the Sun--Sun normwise Frobenius backward-error
    formula, `eta_F(0) = theta * ||b||_2`, stated for nonnegative `theta`. -/
theorem higham21_thm21_3_etaF_zero
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    undetNormwiseBackwardErrorEtaF theta A b (0 : Fin n → ℝ) =
      theta * vecNorm2 b := by
  apply le_antisymm
  · unfold undetNormwiseBackwardErrorEtaF
    exact csInf_le
      (undetNormwiseBackwardErrorValuesF.bddBelow theta A b (0 : Fin n → ℝ))
      (undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero theta htheta A b)
  · unfold undetNormwiseBackwardErrorEtaF
    apply le_csInf
    · exact ⟨theta * vecNorm2 b,
        undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero theta htheta A b⟩
    · intro eta heta
      rcases heta with ⟨DeltaA, Deltab, hfeas, rfl⟩
      exact undetNormwiseBackwardErrorCostF_ge_theta_vecNorm_of_zero_feasible
        htheta A b DeltaA Deltab hfeas

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    residual for an approximate underdetermined solution, using the source
    sign convention `r = b - A y`. -/
noncomputable def undetResidualHigham {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Fin m → ℝ :=
  fun i => b i - rectMatMulVec A y i

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    source-residual identity for any feasible perturbation in the
    underdetermined normwise backward-error model.  If `y` is an exact
    minimum-norm solution of `(A + DeltaA)y = b + Deltab`, then the source
    residual `b - A y` equals `DeltaA*y - Deltab`. -/
theorem UndetNormwiseBackwardErrorFeasible.source_residual_eq
    {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {y : Fin n → ℝ}
    {DeltaA : Fin m → Fin n → ℝ} {Deltab : Fin m → ℝ}
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetResidualHigham A b y =
      fun i => rectMatMulVec DeltaA y i - Deltab i := by
  ext i
  have hi := congrFun hfeas.system_eq i
  unfold undetResidualHigham rectMatMulVec at *
  simp_rw [add_mul] at hi
  rw [Finset.sum_add_distrib] at hi
  linarith

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    scalar residual lower-bound dependency for the nonzero Sun--Sun route.
    Any feasible perturbation pair has weighted cost at least the scalar
    `phi` branch formed from the source residual `b - A*y`.  The full
    nonzero formula still requires the singular-value term. -/
theorem UndetNormwiseBackwardErrorFeasible.phi_le_costF
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {y : Fin n → ℝ}
    {DeltaA : Fin m → Fin n → ℝ} {Deltab : Fin m → ℝ}
    (hy : y ≠ 0)
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    lsNormwiseBackwardErrorPhi theta (undetResidualHigham A b y) y ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
  lsNormwiseBackwardErrorPhi_le_costF_of_residual_eq_deltaA_y_sub_deltab
    htheta hy (undetResidualHigham A b y) DeltaA Deltab
    hfeas.source_residual_eq

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    source-facing model of `I - y y^+` in the nonzero-`y` branch.  This reuses
    the Chapter 20 rank-one complement-projector infrastructure. -/
noncomputable abbrev undetApproxComplementProjector {n : ℕ}
    (y : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  lsResidualComplementProjector y

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    source matrix `A(I - y y^+)` appearing in the nonzero Sun--Sun formula. -/
noncomputable def undetNormwiseBackwardErrorFormulaMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  rectMatMul A (undetApproxComplementProjector y)

/-- The row singular value sigma_m used in Theorem 21.3, represented as the
    least column singular value of the transposed wide matrix. -/
noncomputable def higham21SigmaMinRow
    {m n : ℕ} (M : Fin (m + 1) → Fin n → ℝ) : ℝ :=
  wedinLemma20_11_sigmaMinCol (finiteTranspose M)

theorem higham21SigmaMinRow_nonneg
    {m n : ℕ} (M : Fin (m + 1) → Fin n → ℝ) :
    0 ≤ higham21SigmaMinRow M := by
  simpa only [higham21SigmaMinRow] using
    wedinLemma20_11_sigmaMinCol_nonneg (finiteTranspose M)

theorem higham21SigmaMinRow_mul_vecNorm2_le_rectTransposeMulVec
    {m n : ℕ} (M : Fin (m + 1) → Fin n → ℝ)
    (u : Fin (m + 1) → ℝ) :
    higham21SigmaMinRow M * vecNorm2 u ≤
      vecNorm2 (rectTransposeMulVec M u) := by
  simpa only [higham21SigmaMinRow, rectTransposeMulVec, rectMatMulVec,
    finiteTranspose] using
    (wedinLemma20_11_sigmaMinCol_mul_vecNorm2_le_rectMatMulVec
      (finiteTranspose M) u)

theorem higham21SigmaMinRow_exists_real_attaining_vector_sq
    {m n : ℕ} (M : Fin (m + 1) → Fin n → ℝ) :
    ∃ u : Fin (m + 1) → ℝ, u ≠ 0 ∧
      vecNorm2Sq (rectTransposeMulVec M u) =
        higham21SigmaMinRow M ^ 2 * vecNorm2Sq u := by
  simpa only [higham21SigmaMinRow, rectTransposeMulVec, rectMatMulVec,
    finiteTranspose] using
    (realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq
      (finiteTranspose M))

theorem higham21SigmaMinRow_exists_real_attaining_vector
    {m n : ℕ} (M : Fin (m + 1) → Fin n → ℝ) :
    ∃ u : Fin (m + 1) → ℝ, u ≠ 0 ∧
      vecNorm2 (rectTransposeMulVec M u) =
        higham21SigmaMinRow M * vecNorm2 u := by
  obtain ⟨u, hu, hsq⟩ :=
    higham21SigmaMinRow_exists_real_attaining_vector_sq M
  refine ⟨u, hu, ?_⟩
  have hleft : 0 ≤ vecNorm2 (rectTransposeMulVec M u) :=
    vecNorm2_nonneg _
  have hright : 0 ≤ higham21SigmaMinRow M * vecNorm2 u :=
    mul_nonneg (higham21SigmaMinRow_nonneg M) (vecNorm2_nonneg u)
  have hsquares :
      vecNorm2 (rectTransposeMulVec M u) ^ 2 =
        (higham21SigmaMinRow M * vecNorm2 u) ^ 2 := by
    calc
      vecNorm2 (rectTransposeMulVec M u) ^ 2 =
          vecNorm2Sq (rectTransposeMulVec M u) := vecNorm2_sq _
      _ = higham21SigmaMinRow M ^ 2 * vecNorm2Sq u := hsq
      _ = higham21SigmaMinRow M ^ 2 * vecNorm2 u ^ 2 := by
        rw [vecNorm2_sq u]
      _ = (higham21SigmaMinRow M * vecNorm2 u) ^ 2 := by ring
  nlinarith

/-- Entry expansion of the Chapter 21 source matrix `A(I - y y^+)`. -/
theorem undetNormwiseBackwardErrorFormulaMatrix_apply {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    undetNormwiseBackwardErrorFormulaMatrix A y i j =
      ∑ k : Fin n, A i k *
        (idMatrix n k j - y k * y j / vecNorm2Sq y) := by
  rfl

/-- Applying the Chapter 21 source matrix `A(I - y y^+)` is the same as first
    projecting with `I - y y^+`, then applying `A`. -/
theorem undetNormwiseBackwardErrorFormulaMatrix_mulVec_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y x : Fin n → ℝ) :
    rectMatMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) x =
      rectMatMulVec A (rectMatMulVec (undetApproxComplementProjector y) x) := by
  rw [undetNormwiseBackwardErrorFormulaMatrix, rectMatMulVec_rectMatMul]

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    the source matrix `A(I - y y^+)` annihilates the nonzero candidate
    direction `y`. -/
theorem higham21_thm21_3_formulaMatrix_mulVec_candidate_eq_zero
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ)
    (hysq : vecNorm2Sq y ≠ 0) :
    rectMatMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) y = 0 := by
  have hcomp : rectMatMulVec (undetApproxComplementProjector y) y = 0 := by
    simpa [undetApproxComplementProjector, rectMatMulVec, matMulVec] using
      (lsResidualComplementProjector_mulVec_residual y hysq)
  rw [undetNormwiseBackwardErrorFormulaMatrix_mulVec_eq A y y, hcomp]
  ext i
  simp [rectMatMulVec]

set_option maxHeartbeats 800000
/-- The right-projector Pythagorean identity used in both directions of the
    nonzero branch of Theorem 21.3. -/
theorem higham21_thm21_3_right_projector_frobNormSqRect_pythagoras
    {m n : ℕ} (DeltaA : Fin m → Fin n → ℝ)
    (y : Fin n → ℝ) (hy : y ≠ 0) :
    frobNormSqRect DeltaA =
      vecNorm2Sq (rectMatMulVec DeltaA y) / vecNorm2Sq y +
        frobNormSqRect
          (rectMatMul DeltaA (undetApproxComplementProjector y)) := by
  have hysq : vecNorm2Sq y ≠ 0 :=
    higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have haction :
      (fun j : Fin m =>
        ∑ i : Fin n, y i * finiteTranspose DeltaA i j) =
        rectMatMulVec DeltaA y := by
    ext j
    simp only [finiteTranspose, rectMatMulVec]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcompTranspose :
      finiteTranspose
          (rectMatMul DeltaA (undetApproxComplementProjector y)) =
        matMulRectLeft (lsLemma20_6ProjectorComplement y)
          (finiteTranspose DeltaA) := by
    ext i j
    simp only [finiteTranspose, rectMatMul, matMulRectLeft]
    apply Finset.sum_congr rfl
    intro k _
    have hsymm :
        undetApproxComplementProjector y k i =
          lsLemma20_6ProjectorComplement y i k := by
      simpa [undetApproxComplementProjector, lsResidualComplementProjector] using
        (lsLemma20_6ProjectorComplement_symmetric y k i)
    rw [hsymm]
    ring
  have hcompFrob :
      frobNormSqRect
          (matMulRectLeft (lsLemma20_6ProjectorComplement y)
            (finiteTranspose DeltaA)) =
        frobNormSqRect
          (rectMatMul DeltaA (undetApproxComplementProjector y)) := by
    rw [hcompTranspose.symm, frobNormSqRect_finiteTranspose]
  have hbase :=
    lsLemma20_6Projector_transpose_action_vecNorm2Sq_add_complement_frobNormSqRect
      y hysq (finiteTranspose DeltaA)
  rw [haction, hcompFrob, frobNormSqRect_finiteTranspose] at hbase
  field_simp [hysq]
  linarith

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    scalar right-hand side of the nonzero Sun--Sun formula, parameterized by
    the smallest singular value of `A(I - y y^+)`. This definition is used
    by the completed equality and attainment results later in this file and
    in `Higham21Theorem21_3Attainment`. -/
noncomputable def undetNormwiseBackwardErrorNonzeroFormulaRHS {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) : ℝ :=
  Real.sqrt
    (theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
        (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) +
      sigma ^ 2)

/-- Radicand nonnegativity for the scalar right-hand side in the nonzero
    branch of Higham Chapter 21, Theorem 21.3.  This is only scalar formula
    bookkeeping; it does not assert the Sun--Sun equality with `eta_F(y)`. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_radicand_nonneg
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) :
    0 ≤
      theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
          (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) +
        sigma ^ 2 := by
  have htheta_sq : 0 ≤ theta ^ 2 := sq_nonneg theta
  have hy_sq : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
  have hnum : 0 ≤ theta ^ 2 * vecNorm2Sq y := mul_nonneg htheta_sq hy_sq
  have hden : 0 ≤ 1 + theta ^ 2 * vecNorm2Sq y := by
    exact add_nonneg zero_le_one hnum
  have hleft :
      0 ≤ theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) :=
    div_nonneg hnum hden
  have hres :
      0 ≤ vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y :=
    div_nonneg (vecNorm2Sq_nonneg _) hy_sq
  exact add_nonneg (mul_nonneg hleft hres) (sq_nonneg sigma)

/-- The scalar right-hand side in the nonzero branch of Higham Chapter 21,
    Theorem 21.3 is nonnegative. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_nonneg
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) :
    0 ≤ undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  unfold undetNormwiseBackwardErrorNonzeroFormulaRHS
  exact Real.sqrt_nonneg _

/-- Squared form of the scalar right-hand side in the nonzero branch of
    Higham Chapter 21, Theorem 21.3.  This prepares the later lower/upper
    bound route against the Sun--Sun formula but does not close it. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_sq
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ^ 2 =
      theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
          (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) +
        sigma ^ 2 := by
  unfold undetNormwiseBackwardErrorNonzeroFormulaRHS
  exact Real.sq_sqrt
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_radicand_nonneg
      theta A b y sigma)

set_option maxHeartbeats 2000000
/-- Higham, 2nd ed., Chapter 21, Theorem 21.3: every feasible
    perturbation for a nonzero candidate has squared weighted Frobenius cost
    at least the squared Sun--Sun formula, with the row singular value of
    `A(I - y y^+)`. -/
theorem higham21_thm21_3_nonzeroFormulaRHS_sq_le_costF_sq_of_feasible
    {m n : Nat} (theta : Real)
    (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) {y : Fin n -> Real}
    (hy : Not (y = 0))
    (DeltaA : Fin (m + 1) -> Fin n -> Real)
    (Deltab : Fin (m + 1) -> Real)
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
          (higham21SigmaMinRow
            (undetNormwiseBackwardErrorFormulaMatrix A y)) ^ 2 <=
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab ^ 2 := by
  let P : Fin n -> Fin n -> Real := undetApproxComplementProjector y
  let M : Fin (m + 1) -> Fin n -> Real :=
    undetNormwiseBackwardErrorFormulaMatrix A y
  let E : Fin (m + 1) -> Fin n -> Real := rectMatMul DeltaA P
  let w : Fin (m + 1) -> Real := rectMatMulVec DeltaA y
  let r : Fin (m + 1) -> Real := undetResidualHigham A b y
  let Y : Real := vecNorm2Sq y
  let T : Real := theta ^ 2
  let D : Real := 1 + T * Y
  let sigma : Real := higham21SigmaMinRow M

  have hYne : Not (Y = 0) := by
    simpa [Y] using higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have hYpos : 0 < Y :=
    lt_of_le_of_ne' (by simpa [Y] using vecNorm2Sq_nonneg y) hYne
  have hDpos : 0 < D := by
    simpa [D, T, Y] using lsNormwiseBackwardErrorMu_den_pos theta y

  have hsigma_sq : sigma ^ 2 <= frobNormSqRect E := by
    let B : Fin (m + 1) -> Fin n -> Real :=
      fun i j => A i j + DeltaA i j
    let z : Fin (m + 1) -> Real :=
      Classical.choose (RectMinNormSolution.exists_transpose_witness hfeas)
    have hz : rectTransposeMulVec (fun i j => A i j + DeltaA i j) z = y :=
      Classical.choose_spec (RectMinNormSolution.exists_transpose_witness hfeas)
    have hzB : rectTransposeMulVec B z = y := by
      simpa [B] using hz
    have hz_ne : Not (z = 0) := by
      intro hz0
      apply hy
      calc
        y = rectTransposeMulVec B z := hzB.symm
        _ = rectTransposeMulVec B 0 := by rw [hz0]
        _ = 0 := by
          ext j
          simp [rectTransposeMulVec]
    have hzNormPos : 0 < vecNorm2 z := by
      have hnorm_ne : Not (vecNorm2 z = 0) := by
        intro hzero
        apply hz_ne
        ext i
        exact (vecNorm2_eq_zero_iff z).mp hzero i
      exact lt_of_le_of_ne' (vecNorm2_nonneg z) hnorm_ne
    have hPzero : rectMatMulVec P y = 0 := by
      simpa [P, undetApproxComplementProjector, rectMatMulVec, matMulVec] using
        (lsResidualComplementProjector_mulVec_residual y hYne)
    have hPsymm : forall i j : Fin n, P i j = P j i := by
      intro i j
      simpa [P, undetApproxComplementProjector,
        lsResidualComplementProjector] using
        (lsLemma20_6ProjectorComplement_symmetric y i j)
    have hPtranspose : rectTransposeMulVec P y = rectMatMulVec P y := by
      ext j
      unfold rectTransposeMulVec rectMatMulVec
      apply Finset.sum_congr rfl
      intro i _
      rw [hPsymm i j]
    have htransProduct :
        rectTransposeMulVec (rectMatMul B P) z =
          rectTransposeMulVec P (rectTransposeMulVec B z) := by
      ext j
      unfold rectTransposeMulVec rectMatMul
      calc
        Finset.univ.sum (fun i : Fin (m + 1) =>
            (Finset.univ.sum (fun k : Fin n => B i k * P k j)) * z i) =
          Finset.univ.sum (fun i : Fin (m + 1) =>
            Finset.univ.sum (fun k : Fin n => (B i k * P k j) * z i)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
        _ = Finset.univ.sum (fun k : Fin n =>
              Finset.univ.sum (fun i : Fin (m + 1) =>
                (B i k * P k j) * z i)) := by
              rw [Finset.sum_comm]
        _ = Finset.univ.sum (fun k : Fin n => P k j *
              Finset.univ.sum (fun i : Fin (m + 1) => B i k * z i)) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
    have hBPzero : rectTransposeMulVec (rectMatMul B P) z = 0 := by
      calc
        rectTransposeMulVec (rectMatMul B P) z =
            rectTransposeMulVec P (rectTransposeMulVec B z) := htransProduct
        _ = rectTransposeMulVec P y := by rw [hzB]
        _ = rectMatMulVec P y := hPtranspose
        _ = 0 := hPzero
    have hMEeq :
        (fun i j => M i j + E i j) = rectMatMul B P := by
      simpa [M, E, B, P, undetNormwiseBackwardErrorFormulaMatrix] using
        (rectMatMul_add_left A DeltaA
          (undetApproxComplementProjector y)).symm
    have hsplit :
        rectTransposeMulVec (fun i j => M i j + E i j) z =
          fun j => rectTransposeMulVec M z j + rectTransposeMulVec E z j := by
      ext j
      unfold rectTransposeMulVec
      calc
        Finset.univ.sum (fun i : Fin (m + 1) =>
            (M i j + E i j) * z i) =
          Finset.univ.sum (fun i : Fin (m + 1) =>
            M i j * z i + E i j * z i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = Finset.univ.sum (fun i : Fin (m + 1) => M i j * z i) +
            Finset.univ.sum (fun i : Fin (m + 1) => E i j * z i) :=
              Finset.sum_add_distrib
    have hsumzero :
        rectTransposeMulVec (fun i j => M i j + E i j) z = 0 := by
      rw [hMEeq]
      exact hBPzero
    rw [hsplit] at hsumzero
    have hrelation :
        rectTransposeMulVec M z =
          fun j => -rectTransposeMulVec E z j := by
      ext j
      have hj := congrFun hsumzero j
      simp only [Pi.zero_apply] at hj
      linarith
    have hsigma_action :
        sigma * vecNorm2 z <= vecNorm2 (rectTransposeMulVec M z) := by
      simpa [sigma] using
        (higham21SigmaMinRow_mul_vecNorm2_le_rectTransposeMulVec M z)
    have hEaction :
        vecNorm2 (rectTransposeMulVec E z) <=
          frobNormRect E * vecNorm2 z := by
      simpa only [rectTransposeMulVec, rectMatMulVec, finiteTranspose] using
        (vecNorm2_rectMatMulVec_finiteTranspose_le_frobNormRect_mul E z)
    have hprod : sigma * vecNorm2 z <= frobNormRect E * vecNorm2 z := by
      calc
        sigma * vecNorm2 z <= vecNorm2 (rectTransposeMulVec M z) :=
          hsigma_action
        _ = vecNorm2 (rectTransposeMulVec E z) := by
          rw [hrelation, vecNorm2_neg]
        _ <= frobNormRect E * vecNorm2 z := hEaction
    have hsigma_le : sigma <= frobNormRect E :=
      le_of_mul_le_mul_right hprod hzNormPos
    have hsigma_nonneg : 0 <= sigma := by
      simpa [sigma] using higham21SigmaMinRow_nonneg M
    have habs : abs sigma <= abs (frobNormRect E) := by
      simpa [abs_of_nonneg hsigma_nonneg,
        abs_of_nonneg (frobNormRect_nonneg E)] using hsigma_le
    have hsquares : sigma ^ 2 <= frobNormRect E ^ 2 :=
      (sq_le_sq).mpr habs
    simpa [frobNormRect_sq] using hsquares

  have hres : r = fun i => w i - Deltab i := by
    simpa [r, w] using hfeas.source_residual_eq
  have hscalar :
      T * Y / D * (vecNorm2Sq r / Y) <=
        vecNorm2Sq w / Y + T * vecNorm2Sq Deltab := by
    let q : Fin (m + 1) -> Real :=
      fun i => w i + T * Y * Deltab i
    have hWB :
        vecNorm2Sq w + T * Y * vecNorm2Sq Deltab =
          Finset.univ.sum (fun i : Fin (m + 1) =>
            (w i) ^ 2 + T * Y * (Deltab i) ^ 2) := by
      unfold vecNorm2Sq
      calc
        Finset.univ.sum (fun i : Fin (m + 1) => w i ^ 2) +
            T * Y * Finset.univ.sum (fun i : Fin (m + 1) => Deltab i ^ 2) =
          Finset.univ.sum (fun i : Fin (m + 1) => w i ^ 2) +
            Finset.univ.sum (fun i : Fin (m + 1) => T * Y * Deltab i ^ 2) := by
              rw [Finset.mul_sum]
        _ = Finset.univ.sum (fun i : Fin (m + 1) =>
              w i ^ 2 + T * Y * Deltab i ^ 2) :=
              Finset.sum_add_distrib.symm
    have hcomplete_sum :
        D * (vecNorm2Sq w + T * Y * vecNorm2Sq Deltab) =
          T * Y * vecNorm2Sq r + vecNorm2Sq q := by
      calc
        D * (vecNorm2Sq w + T * Y * vecNorm2Sq Deltab) =
            D * Finset.univ.sum (fun i : Fin (m + 1) =>
              ((w i) ^ 2 + T * Y * (Deltab i) ^ 2)) := by rw [hWB]
        _ = Finset.univ.sum (fun i : Fin (m + 1) =>
              D * ((w i) ^ 2 + T * Y * (Deltab i) ^ 2)) := by
                rw [Finset.mul_sum]
        _ = Finset.univ.sum (fun i : Fin (m + 1) =>
              (T * Y * (w i - Deltab i) ^ 2 +
                (w i + T * Y * Deltab i) ^ 2)) := by
                apply Finset.sum_congr rfl
                intro i _
                dsimp [D]
                ring
        _ = T * Y * Finset.univ.sum (fun i : Fin (m + 1) =>
              (w i - Deltab i) ^ 2) +
              Finset.univ.sum (fun i : Fin (m + 1) =>
                (w i + T * Y * Deltab i) ^ 2) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = T * Y * vecNorm2Sq r + vecNorm2Sq q := by
                simp only [vecNorm2Sq]
                rw [hres]
    have hq_nonneg : 0 <= vecNorm2Sq q := vecNorm2Sq_nonneg q
    have hTYR_le :
        T * Y * vecNorm2Sq r <=
          D * (vecNorm2Sq w + T * Y * vecNorm2Sq Deltab) := by
      rw [hcomplete_sum]
      linarith
    have hTR_le :
        T * vecNorm2Sq r <=
          D * (vecNorm2Sq w / Y + T * vecNorm2Sq Deltab) := by
      have hmul :
          (T * vecNorm2Sq r) * Y <=
            (D * (vecNorm2Sq w / Y + T * vecNorm2Sq Deltab)) * Y := by
        calc
          (T * vecNorm2Sq r) * Y = T * Y * vecNorm2Sq r := by ring
          _ <= D * (vecNorm2Sq w + T * Y * vecNorm2Sq Deltab) := hTYR_le
          _ = (D * (vecNorm2Sq w / Y + T * vecNorm2Sq Deltab)) * Y := by
            field_simp [hYne] <;> ring
      exact le_of_mul_le_mul_right hmul hYpos
    have hformula :
        T * Y / D * (vecNorm2Sq r / Y) =
          T * vecNorm2Sq r / D := by
      field_simp [hYne, ne_of_gt hDpos]
    rw [hformula]
    have hdiv :
        T * vecNorm2Sq r / D <=
          ((vecNorm2Sq w / Y + T * vecNorm2Sq Deltab) * D) / D :=
      (div_le_div_iff_of_pos_right hDpos).2 (by
        simpa [mul_comm] using hTR_le)
    calc
      T * vecNorm2Sq r / D <=
          ((vecNorm2Sq w / Y + T * vecNorm2Sq Deltab) * D) / D := hdiv
      _ = vecNorm2Sq w / Y + T * vecNorm2Sq Deltab := by
        field_simp [ne_of_gt hDpos]

  have hpyth :
      frobNormSqRect DeltaA = vecNorm2Sq w / Y + frobNormSqRect E := by
    simpa [w, Y, E, P] using
      (higham21_thm21_3_right_projector_frobNormSqRect_pythagoras
        DeltaA y hy)
  rw [undetNormwiseBackwardErrorNonzeroFormulaRHS_sq,
    lsNormwiseBackwardErrorCostF_sq]
  change
    T * Y / D * (vecNorm2Sq r / Y) + sigma ^ 2 <=
      frobNormSqRect DeltaA + T * vecNorm2Sq Deltab
  calc
    T * Y / D * (vecNorm2Sq r / Y) + sigma ^ 2 <=
        (vecNorm2Sq w / Y + T * vecNorm2Sq Deltab) +
          frobNormSqRect E := add_le_add hscalar hsigma_sq
    _ = frobNormSqRect DeltaA + T * vecNorm2Sq Deltab := by
      rw [hpyth] <;> ring

/-- Higham, 2nd ed., Chapter 21, Theorem 21.3: every feasible
    perturbation for a nonzero candidate has weighted Frobenius cost at least
    the Sun--Sun formula. -/
theorem higham21_thm21_3_nonzeroFormulaRHS_le_costF_of_feasible
    {m n : Nat} (theta : Real)
    (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) {y : Fin n -> Real}
    (hy : Not (y = 0))
    (DeltaA : Fin (m + 1) -> Fin n -> Real)
    (Deltab : Fin (m + 1) -> Real)
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
          (higham21SigmaMinRow
            (undetNormwiseBackwardErrorFormulaMatrix A y)) <=
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  apply (sq_le_sq₀
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_nonneg theta A b y _)
    (lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab)).mp
  exact
    higham21_thm21_3_nonzeroFormulaRHS_sq_le_costF_sq_of_feasible
      theta A b hy DeltaA Deltab hfeas

/-- Positive singular-value branch of the scalar right-hand side in Higham
    Chapter 21, Theorem 21.3: a positive supplied singular-value parameter
    makes the displayed formula positive. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_pos_of_sigma_pos
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  unfold undetNormwiseBackwardErrorNonzeroFormulaRHS
  apply Real.sqrt_pos.2
  have hsigma_sq_pos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hleft :
      0 ≤ theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
          (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) := by
    have htheta_sq : 0 ≤ theta ^ 2 := sq_nonneg theta
    have hy_sq : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
    have hnum : 0 ≤ theta ^ 2 * vecNorm2Sq y := mul_nonneg htheta_sq hy_sq
    have hden : 0 ≤ 1 + theta ^ 2 * vecNorm2Sq y :=
      add_nonneg zero_le_one hnum
    have hleft_factor :
        0 ≤ theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) :=
      div_nonneg hnum hden
    have hres :
        0 ≤ vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y :=
      div_nonneg (vecNorm2Sq_nonneg _) hy_sq
    exact mul_nonneg hleft_factor hres
  exact add_pos_of_nonneg_of_pos hleft hsigma_sq_pos

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    in the degenerate `sigma = 0` specialization of the nonzero Sun--Sun
    scalar formula, the displayed right-hand side reduces to the residual
    scalar `phi` branch.  This does not assert the full singular-value
    equality with `eta_F(y)`. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_eq_phi_of_sigma_zero
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) {y : Fin n → ℝ}
    (hy : y ≠ 0) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y 0 =
      lsNormwiseBackwardErrorPhi theta (undetResidualHigham A b y) y := by
  apply (sq_eq_sq₀
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_nonneg theta A b y 0)
    (lsNormwiseBackwardErrorPhi_nonneg theta (undetResidualHigham A b y) y)).mp
  rw [undetNormwiseBackwardErrorNonzeroFormulaRHS_sq]
  rw [lsNormwiseBackwardErrorPhi_eq_theta_mul_norm_div_sqrt_den htheta hy]
  have hy_sq_ne : vecNorm2Sq y ≠ 0 :=
    higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have hden_pos : 0 < 1 + theta ^ 2 * vecNorm2Sq y :=
    lsNormwiseBackwardErrorMu_den_pos theta y
  rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hden_pos), vecNorm2_sq]
  field_simp [hy_sq_ne, ne_of_gt hden_pos]
  ring

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    lower-bound dependency for the `sigma = 0` specialization of the nonzero
    scalar formula.  Every feasible perturbation has cost at least this
    degenerate right-hand side, via the residual `phi` lower bound. -/
theorem UndetNormwiseBackwardErrorFeasible.nonzeroFormulaRHS_le_costF_of_sigma_zero
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {y : Fin n → ℝ}
    {DeltaA : Fin m → Fin n → ℝ} {Deltab : Fin m → ℝ}
    (hy : y ≠ 0)
    (hfeas : UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y 0 ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  rw [undetNormwiseBackwardErrorNonzeroFormulaRHS_eq_phi_of_sigma_zero
    htheta A b hy]
  exact hfeas.phi_le_costF htheta hy

/-- Lower-bound handoff for the nonzero branch of Higham Chapter 21,
    Theorem 21.3: once every feasible perturbation has cost at least the
    displayed nonzero RHS, the RHS is below the infimum model `eta_F(y)`.
    The singular-vector proof of that pointwise lower bound remains open. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty)
    (hlower :
      ∀ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab →
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
            lsNormwiseBackwardErrorCostF theta DeltaA Deltab) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
      undetNormwiseBackwardErrorEtaF theta A b y := by
  unfold undetNormwiseBackwardErrorEtaF
  apply le_csInf hnonempty
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, hfeas, heta_eq⟩
  rw [heta_eq]
  exact hlower DeltaA Deltab hfeas

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    lower-bound corollary for the `sigma = 0` specialization.  Combining the
    degenerate RHS-to-`phi` bridge with the feasible-cost lower bound shows
    that this scalar branch is below the `eta_F(y)` infimum whenever the
    attainable-cost set is nonempty.  The full singular-value lower route
    remains open. -/
theorem undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_sigma_zero
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) {y : Fin n → ℝ}
    (hy : y ≠ 0)
    (hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y 0 ≤
      undetNormwiseBackwardErrorEtaF theta A b y :=
  undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
    theta A b y 0 hnonempty
    (fun _DeltaA _Deltab hfeas =>
      hfeas.nonzeroFormulaRHS_le_costF_of_sigma_zero htheta hy)

/-- Upper-bound handoff for the nonzero branch of Higham Chapter 21,
    Theorem 21.3: an attaining feasible perturbation gives
    `eta_F(y) <=` the displayed nonzero RHS. -/
theorem undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_eq
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hatt :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y ≤
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  rcases hatt with ⟨DeltaA, Deltab, hfeas, hcost⟩
  calc
    undetNormwiseBackwardErrorEtaF theta A b y ≤
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
      undetNormwiseBackwardErrorEtaF_le_costF_of_feasible
        theta A b y DeltaA Deltab hfeas
    _ = undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := hcost

/-- Inequality-form upper-bound handoff for the nonzero branch of Higham
    Chapter 21, Theorem 21.3: it is enough to exhibit a feasible perturbation
    whose weighted cost is bounded by the displayed nonzero RHS. -/
theorem undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_le
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hupper :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y ≤
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  rcases hupper with ⟨DeltaA, Deltab, hfeas, hcost⟩
  exact
    (undetNormwiseBackwardErrorEtaF_le_costF_of_feasible
      theta A b y DeltaA Deltab hfeas).trans hcost

/-- Certificate form of the open nonzero equality in Higham Chapter 21,
    Theorem 21.3.  It isolates the two remaining obligations for the
    Sun--Sun proof: a pointwise lower bound for all feasible perturbations
    and one feasible perturbation attaining the displayed nonzero RHS. -/
theorem undetNormwiseBackwardErrorEtaF_eq_nonzeroFormulaRHS_of_formula_certificate
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hlower :
      ∀ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab →
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
            lsNormwiseBackwardErrorCostF theta DeltaA Deltab)
    (hatt :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y =
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  rcases hatt with ⟨DeltaA, Deltab, hfeas, hcost⟩
  have hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty :=
    ⟨lsNormwiseBackwardErrorCostF theta DeltaA Deltab,
      DeltaA, Deltab, hfeas, rfl⟩
  exact le_antisymm
    (undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_eq
      theta A b y sigma ⟨DeltaA, Deltab, hfeas, hcost⟩)
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
      theta A b y sigma hnonempty hlower)

/-- Inequality-form certificate for the open nonzero equality in Higham
    Chapter 21, Theorem 21.3.  A pointwise lower bound for every feasible
    perturbation and one feasible perturbation whose cost is no larger than the
    displayed nonzero RHS already force the infimum model to equal the RHS. -/
theorem undetNormwiseBackwardErrorEtaF_eq_nonzeroFormulaRHS_of_formula_upper_certificate
    {m n : ℕ} (theta : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (y : Fin n → ℝ) (sigma : ℝ)
    (hlower :
      ∀ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab →
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ≤
            lsNormwiseBackwardErrorCostF theta DeltaA Deltab)
    (hupper :
      ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
        UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
          lsNormwiseBackwardErrorCostF theta DeltaA Deltab ≤
            undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma) :
    undetNormwiseBackwardErrorEtaF theta A b y =
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma := by
  rcases hupper with ⟨DeltaA, Deltab, hfeas, hcost⟩
  have hnonempty : (undetNormwiseBackwardErrorValuesF theta A b y).Nonempty :=
    ⟨lsNormwiseBackwardErrorCostF theta DeltaA Deltab,
      DeltaA, Deltab, hfeas, rfl⟩
  exact le_antisymm
    (undetNormwiseBackwardErrorEtaF_le_nonzeroFormulaRHS_of_exists_feasible_cost_le
      theta A b y sigma ⟨DeltaA, Deltab, hfeas, hcost⟩)
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
      theta A b y sigma hnonempty hlower)

/-- Minimum-norm feasibility is equivalent to exact feasibility together with
    a transpose-range witness.  The forward implication uses finite-dimensional
    range attainment; the reverse implication is the standard orthogonality
    characterization of a minimum 2-norm solution. -/
theorem undetNormwiseBackwardErrorFeasible_iff_system_eq_and_exists_transpose_witness
    {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (y : Fin n -> Real)
    (DeltaA : Fin m -> Fin n -> Real) (Deltab : Fin m -> Real) :
    UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab <->
      rectMatMulVec (fun i j => A i j + DeltaA i j) y =
          (fun i => b i + Deltab i) /\
        exists z : Fin m -> Real,
          rectTransposeMulVec (fun i j => A i j + DeltaA i j) z = y := by
  unfold UndetNormwiseBackwardErrorFeasible
  constructor
  · intro h
    exact ⟨h.system_eq, h.exists_transpose_witness⟩
  · rintro ⟨hsystem, z, hz⟩
    have hsolve :
        rectMatMulVec (fun i j => A i j + DeltaA i j)
            (rectTransposeMulVec (fun i j => A i j + DeltaA i j) z) =
          fun i => b i + Deltab i := by
      rw [hz]
      exact hsystem
    simpa [hz] using
      (higham21_eq21_4_rect_transpose_min_norm_of_solves
        (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i) z hsolve)

/-- Pairing identity for a rectangular matrix and its transpose. -/
theorem higham21_rectTransposeMulVec_pairing
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (u : Fin m -> Real) (x : Fin n -> Real) :
    (∑ j : Fin n, rectTransposeMulVec A u j * x j) =
      ∑ i : Fin m, u i * rectMatMulVec A x i := by
  unfold rectTransposeMulVec rectMatMulVec
  calc
    (∑ j : Fin n, (∑ i : Fin m, A i j * u i) * x j) =
        ∑ j : Fin n, ∑ i : Fin m, (A i j * u i) * x j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, (A i j * u i) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin m, u i * ∑ j : Fin n, A i j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Triangle inequality for the weighted Frobenius perturbation cost. -/
theorem higham21_lsNormwiseBackwardErrorCostF_add_le
    {m n : Nat} (theta : Real)
    (A1 A2 : Fin m -> Fin n -> Real) (b1 b2 : Fin m -> Real) :
    lsNormwiseBackwardErrorCostF theta
        (fun i j => A1 i j + A2 i j) (fun i => b1 i + b2 i) <=
      lsNormwiseBackwardErrorCostF theta A1 b1 +
        lsNormwiseBackwardErrorCostF theta A2 b2 := by
  unfold lsNormwiseBackwardErrorCostF
  have hweighted :
      lsNormwiseBackwardErrorWeightedMatrix theta
          (fun i j => A1 i j + A2 i j) (fun i => b1 i + b2 i) =
        fun i j =>
          lsNormwiseBackwardErrorWeightedMatrix theta A1 b1 i j +
            lsNormwiseBackwardErrorWeightedMatrix theta A2 b2 i j := by
    ext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [lsNormwiseBackwardErrorWeightedMatrix, mul_add]
  rw [hweighted]
  exact frobNormRect_add_le _ _

/-- Simultaneous scalar multiplication is homogeneous for the weighted cost. -/
theorem higham21_lsNormwiseBackwardErrorCostF_smul
    {m n : Nat} (theta t : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    lsNormwiseBackwardErrorCostF theta
        (fun i j => t * A i j) (fun i => t * b i) =
      |t| * lsNormwiseBackwardErrorCostF theta A b := by
  unfold lsNormwiseBackwardErrorCostF
  have hweighted :
      lsNormwiseBackwardErrorWeightedMatrix theta
          (fun i j => t * A i j) (fun i => t * b i) =
        fun i j =>
          t * lsNormwiseBackwardErrorWeightedMatrix theta A b i j := by
    ext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [lsNormwiseBackwardErrorWeightedMatrix] <;> ring
  rw [hweighted, frobNormRect_smul]

/-- An arbitrarily small signed scalar can avoid one forbidden affine root. -/
theorem higham21_exists_signed_small_parameter
    (a U K eps : Real) (hU : 0 < U) (hK : 0 <= K) (heps : 0 < eps) :
    exists t : Real, a + t * U ≠ 0 /\ |t| * K <= eps := by
  let d : Real := eps / (2 * (K + 1))
  have hden : 0 < 2 * (K + 1) := by positivity
  have hd : 0 < d := div_pos heps hden
  have hdK : d * K <= eps := by
    dsimp [d]
    have hdK_eq : d * K = eps * K / (2 * (K + 1)) := by
      dsimp [d]
      ring
    rw [hdK_eq]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (le_of_lt heps) hK]
  by_cases hplus : a + d * U ≠ 0
  · refine ⟨d, hplus, ?_⟩
    simpa [abs_of_pos hd] using hdK
  · have hplus_eq : a + d * U = 0 := not_ne_iff.mp hplus
    refine ⟨-d, ?_, ?_⟩
    · intro hminus
      have hdu : d * U = 0 := by nlinarith
      exact (mul_ne_zero (ne_of_gt hd) (ne_of_gt hU)) hdu
    · simpa [abs_of_pos hd] using hdK

/-- Residual-correcting matrix part of the nonzero Theorem 21.3 witness. -/
noncomputable def higham21Thm21_3ResidualDeltaA
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (y : Fin n -> Real) :
    Fin m -> Fin n -> Real :=
  let r := undetResidualHigham A b y
  let den := 1 + theta ^ 2 * vecNorm2Sq y
  fun i j => (theta ^ 2 / den) * r i * y j

/-- Residual-correcting right-hand-side part of the witness. -/
noncomputable def higham21Thm21_3ResidualDeltab
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (y : Fin n -> Real) :
    Fin m -> Real :=
  let r := undetResidualHigham A b y
  let den := 1 + theta ^ 2 * vecNorm2Sq y
  fun i => -(1 / den) * r i

/-- Rank-one cancellation of the projected transpose action along `u`. -/
noncomputable def higham21Thm21_3CancellationDeltaA
    {m n : Nat} (A : Fin m -> Fin n -> Real) (y : Fin n -> Real)
    (u : Fin m -> Real) : Fin m -> Fin n -> Real :=
  lsNormwiseBackwardErrorRankOneDeltaA u
    (rectTransposeMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) u)

/-- The small residual-preserving signed perturbation. -/
noncomputable abbrev higham21Thm21_3SignedExtraDeltaA
    {m n : Nat} (t : Real) (u : Fin m -> Real) (y : Fin n -> Real) :
    Fin m -> Fin n -> Real :=
  lsNormwiseBackwardErrorRankTwoExtraDeltaA t u y

/-- Full epsilon-approximating matrix perturbation family. -/
noncomputable def higham21Thm21_3ApproxDeltaA
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (y : Fin n -> Real)
    (u : Fin m -> Real) (t : Real) : Fin m -> Fin n -> Real :=
  fun i j =>
    higham21Thm21_3ResidualDeltaA theta A b y i j +
      higham21Thm21_3CancellationDeltaA A y u i j +
        higham21Thm21_3SignedExtraDeltaA t u y i j

/-- Full epsilon-approximating right-hand-side perturbation family. -/
noncomputable def higham21Thm21_3ApproxDeltab
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (y : Fin n -> Real)
    (u : Fin m -> Real) (t : Real) : Fin m -> Real :=
  fun i => higham21Thm21_3ResidualDeltab theta A b y i + t * u i

/-- The residual rank-one term has the required action on `y`. -/
theorem higham21Thm21_3ResidualDeltaA_mulVec
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (y : Fin n -> Real) :
    rectMatMulVec (higham21Thm21_3ResidualDeltaA theta A b y) y =
      fun i =>
        (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y)) *
          vecNorm2Sq y * undetResidualHigham A b y i := by
  ext i
  unfold rectMatMulVec higham21Thm21_3ResidualDeltaA
  calc
    (∑ j : Fin n,
        (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) *
          undetResidualHigham A b y i * y j) * y j) =
        (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) *
          undetResidualHigham A b y i) * ∑ j : Fin n, y j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y)) *
          vecNorm2Sq y * undetResidualHigham A b y i := by
      change
        (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) *
            undetResidualHigham A b y i) * vecNorm2Sq y = _
      ring

/-- The residual rank-one term vanishes after right projection. -/
theorem higham21Thm21_3ResidualDeltaA_projector_eq_zero
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (y : Fin n -> Real) (hy : y ≠ 0) :
    rectMatMul (higham21Thm21_3ResidualDeltaA theta A b y)
        (undetApproxComplementProjector y) = 0 := by
  have hysq : vecNorm2Sq y ≠ 0 :=
    higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  ext i j
  have hproj :=
    lsResidualComplementProjector_transpose_mul_residual y hysq j
  unfold rectMatMul higham21Thm21_3ResidualDeltaA
  calc
    (∑ k : Fin n,
        (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) *
          undetResidualHigham A b y i * y k) *
            undetApproxComplementProjector y k j) =
        (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) *
          undetResidualHigham A b y i) *
            (∑ k : Fin n,
              lsResidualComplementProjector y k j * y k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [undetApproxComplementProjector]
          ring
    _ = 0 := by rw [hproj, mul_zero]

/-- The cancellation rank-one term annihilates `y`. -/
theorem higham21Thm21_3CancellationDeltaA_mulVec_eq_zero
    {m n : Nat} (A : Fin m -> Fin n -> Real) (y : Fin n -> Real)
    (u : Fin m -> Real) (hy : y ≠ 0) :
    rectMatMulVec (higham21Thm21_3CancellationDeltaA A y u) y = 0 := by
  let M := undetNormwiseBackwardErrorFormulaMatrix A y
  let w := rectTransposeMulVec M u
  have hysq : vecNorm2Sq y ≠ 0 :=
    higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have hMy : rectMatMulVec M y = 0 := by
    simpa [M] using
      higham21_thm21_3_formulaMatrix_mulVec_candidate_eq_zero A y hysq
  have hwy : (∑ j : Fin n, w j * y j) = 0 := by
    rw [higham21_rectTransposeMulVec_pairing M u y, hMy]
    simp
  simpa [higham21Thm21_3CancellationDeltaA, M, w, hwy] using
    (lsNormwiseBackwardErrorRankOneDeltaA_mulVec u w y)

/-- The transpose action of `A - A(I-yy+)` is rank one in `y`. -/
theorem higham21_rectTransposeMulVec_sub_formulaMatrix_eq_rankOne
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (y : Fin n -> Real) (u : Fin m -> Real) :
    (fun j =>
      rectTransposeMulVec A u j -
        rectTransposeMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) u j) =
      fun j =>
        (y j / vecNorm2Sq y) *
          (∑ i : Fin m, u i * rectMatMulVec A y i) := by
  let v : Fin n -> Real := rectTransposeMulVec A u
  have hformula : forall j : Fin n,
      rectTransposeMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) u j =
        ∑ k : Fin n, undetApproxComplementProjector y j k * v k := by
    intro j
    unfold undetNormwiseBackwardErrorFormulaMatrix rectTransposeMulVec rectMatMul
    calc
      (∑ i : Fin m,
          (∑ k : Fin n, A i k * undetApproxComplementProjector y k j) * u i) =
          ∑ i : Fin m, ∑ k : Fin n,
            (A i k * undetApproxComplementProjector y k j) * u i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
      _ = ∑ k : Fin n, ∑ i : Fin m,
            (A i k * undetApproxComplementProjector y k j) * u i := by
              rw [Finset.sum_comm]
      _ = ∑ k : Fin n, undetApproxComplementProjector y j k * v k := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [v, rectTransposeMulVec]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              simp only [undetApproxComplementProjector]
              rw [lsResidualComplementProjector_symmetric]
              ring
  ext j
  rw [hformula j]
  have happly := lsLemma20_6ProjectorComplement_apply_vec y v j
  simp only [undetApproxComplementProjector] at happly
  rw [happly]
  have hpair :
      (∑ k : Fin n, y k * v k) =
        ∑ i : Fin m, u i * rectMatMulVec A y i := by
    calc
      (∑ k : Fin n, y k * v k) = ∑ k : Fin n, v k * y k := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ i : Fin m, u i * rectMatMulVec A y i := by
        simpa [v] using higham21_rectTransposeMulVec_pairing A u y
  rw [hpair]
  ring

/-- The full signed family solves the perturbed system exactly. -/
theorem higham21Thm21_3Approx_system_eq
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (y : Fin n -> Real) (u : Fin m -> Real) (t : Real) (hy : y ≠ 0) :
    rectMatMulVec
        (fun i j => A i j + higham21Thm21_3ApproxDeltaA theta A b y u t i j) y =
      fun i => b i + higham21Thm21_3ApproxDeltab theta A b y u t i := by
  let r := undetResidualHigham A b y
  let Y := vecNorm2Sq y
  let den := 1 + theta ^ 2 * Y
  have hY : Y ≠ 0 := by
    simpa [Y] using higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have hden : den ≠ 0 := by
    exact ne_of_gt (by
      dsimp [den, Y]
      exact lsNormwiseBackwardErrorMu_den_pos theta y)
  have hden' : 1 + theta ^ 2 * vecNorm2Sq y ≠ 0 := by
    simpa [den, Y] using hden
  have hR := higham21Thm21_3ResidualDeltaA_mulVec theta A b y
  have hC := higham21Thm21_3CancellationDeltaA_mulVec_eq_zero A y u hy
  have hE :=
    lsNormwiseBackwardErrorRankTwoExtraDeltaA_mulVec
      (beta := t) u hY
  ext i
  have hRi := congrFun hR i
  have hCi := congrFun hC i
  have hEi := congrFun hE i
  unfold rectMatMulVec higham21Thm21_3ApproxDeltaA
    higham21Thm21_3ApproxDeltab at *
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hRi, hCi, hEi]
  dsimp [higham21Thm21_3ResidualDeltab, r, Y, den]
  unfold undetResidualHigham
  unfold rectMatMulVec
  field_simp [hden'] <;> ring

/-- The signed family has a rank-one transpose action, with coefficient
    determined by its exact perturbed right-hand side. -/
theorem higham21Thm21_3Approx_transpose_action
    {m n : Nat} (theta : Real)
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (y : Fin n -> Real) (u : Fin m -> Real) (t : Real)
    (hy : y ≠ 0) (hu : u ≠ 0) :
    rectTransposeMulVec
        (fun i j => A i j + higham21Thm21_3ApproxDeltaA theta A b y u t i j) u =
      fun j =>
        ((∑ i : Fin m,
            u i * (b i + higham21Thm21_3ApproxDeltab theta A b y u t i)) /
          vecNorm2Sq y) * y j := by
  let M := undetNormwiseBackwardErrorFormulaMatrix A y
  let w := rectTransposeMulVec M u
  let Y := vecNorm2Sq y
  let U := vecNorm2Sq u
  let alpha := theta ^ 2 / (1 + theta ^ 2 * Y)
  let lambda :=
    (∑ i : Fin m, u i * rectMatMulVec A y i) / Y +
      alpha * (∑ i : Fin m, undetResidualHigham A b y i * u i) +
        t * U / Y
  have hY : Y ≠ 0 := by
    simpa [Y] using higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have hU : U ≠ 0 := by
    simpa [U] using higham21_vecNorm2Sq_ne_zero_of_ne_zero hu
  have hdiff :=
    higham21_rectTransposeMulVec_sub_formulaMatrix_eq_rankOne A y u
  have hcancel :
      rectTransposeMulVec (higham21Thm21_3CancellationDeltaA A y u) u =
        fun j => -w j := by
    simpa [higham21Thm21_3CancellationDeltaA, M, w, rectTransposeMulVec] using
      (lsNormwiseBackwardErrorRankOneDeltaA_transpose_mul
        (p := u) (u := w) hU)
  have hraw :
      rectTransposeMulVec
          (fun i j => A i j + higham21Thm21_3ApproxDeltaA theta A b y u t i j) u =
        fun j => lambda * y j := by
    ext j
    have hdiffj := congrFun hdiff j
    have hcancelj := congrFun hcancel j
    unfold rectTransposeMulVec higham21Thm21_3ApproxDeltaA at *
    simp_rw [add_mul, Finset.sum_add_distrib]
    have hres :
        (∑ i : Fin m,
          higham21Thm21_3ResidualDeltaA theta A b y i j * u i) =
          alpha * (∑ i : Fin m, undetResidualHigham A b y i * u i) * y j := by
      unfold higham21Thm21_3ResidualDeltaA
      dsimp [alpha, Y]
      calc
        (∑ i : Fin m,
            (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) *
              undetResidualHigham A b y i * y j) * u i) =
            ∑ i : Fin m,
              (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) * y j) *
                (undetResidualHigham A b y i * u i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y) * y j) *
              ∑ i : Fin m, undetResidualHigham A b y i * u i := by
          rw [Finset.mul_sum]
        _ = (theta ^ 2 / (1 + theta ^ 2 * vecNorm2Sq y)) *
              (∑ i : Fin m, undetResidualHigham A b y i * u i) * y j := by
          ring
    have hextra :
        (∑ i : Fin m,
          higham21Thm21_3SignedExtraDeltaA t u y i j * u i) =
          (t * U / Y) * y j := by
      simp only [higham21Thm21_3SignedExtraDeltaA,
        lsNormwiseBackwardErrorRankTwoExtraDeltaA]
      dsimp [U, Y, vecNorm2Sq]
      calc
        (∑ i : Fin m,
            (t / vecNorm2Sq y * u i * y j) * u i) =
            ∑ i : Fin m, (t / vecNorm2Sq y * y j) * (u i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (t / vecNorm2Sq y * y j) * ∑ i : Fin m, u i ^ 2 := by
          rw [Finset.mul_sum]
        _ = (t * (∑ i : Fin m, u i ^ 2) / vecNorm2Sq y) * y j := by
          ring
    rw [hres, hcancelj, hextra]
    simp only [w, rectTransposeMulVec]
    dsimp [lambda]
    rw [show y j / Y = (1 / Y) * y j by field_simp [hY]] at hdiffj
    linear_combination hdiffj
  have hsystem := higham21Thm21_3Approx_system_eq theta A b y u t hy
  have hpair :=
    higham21_rectTransposeMulVec_pairing
      (fun i j => A i j + higham21Thm21_3ApproxDeltaA theta A b y u t i j)
      u y
  rw [hraw, hsystem] at hpair
  have hlambda :
      lambda =
        (∑ i : Fin m,
          u i * (b i + higham21Thm21_3ApproxDeltab theta A b y u t i)) / Y := by
    have hleft :
        (∑ j : Fin n, lambda * y j * y j) = lambda * Y := by
      simp only [Y, vecNorm2Sq]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hleft] at hpair
    apply (eq_div_iff hY).2
    exact hpair
  rw [hraw, hlambda]

/-- The `t = 0` member has cost exactly the displayed Theorem 21.3 RHS. -/
theorem higham21Thm21_3Approx_cost_zero_eq_formulaRHS_of_attaining
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real) (b : Fin (m + 1) -> Real)
    (y : Fin n -> Real) (u : Fin (m + 1) -> Real)
    (hy : y ≠ 0) (hu : u ≠ 0)
    (hattain :
      vecNorm2Sq
          (rectTransposeMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) u) =
        higham21SigmaMinRow (undetNormwiseBackwardErrorFormulaMatrix A y) ^ 2 *
          vecNorm2Sq u) :
    lsNormwiseBackwardErrorCostF theta
        (higham21Thm21_3ApproxDeltaA theta A b y u 0)
        (higham21Thm21_3ApproxDeltab theta A b y u 0) =
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
        (higham21SigmaMinRow (undetNormwiseBackwardErrorFormulaMatrix A y)) := by
  let r := undetResidualHigham A b y
  let Y := vecNorm2Sq y
  let R := vecNorm2Sq r
  let den := 1 + theta ^ 2 * Y
  let M := undetNormwiseBackwardErrorFormulaMatrix A y
  let sigma := higham21SigmaMinRow M
  let w := rectTransposeMulVec M u
  let DR := higham21Thm21_3ResidualDeltaA theta A b y
  let DP := higham21Thm21_3CancellationDeltaA A y u
  let db := higham21Thm21_3ResidualDeltab theta A b y
  let base : Fin (m + 1) -> Fin n -> Real := fun i j => DR i j + DP i j
  have hY : Y ≠ 0 := by
    simpa [Y] using higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
  have hU : vecNorm2Sq u ≠ 0 :=
    higham21_vecNorm2Sq_ne_zero_of_ne_zero hu
  have hden : den ≠ 0 := by
    exact ne_of_gt (by
      dsimp [den, Y]
      exact lsNormwiseBackwardErrorMu_den_pos theta y)
  have hDRy := higham21Thm21_3ResidualDeltaA_mulVec theta A b y
  have hDPy := higham21Thm21_3CancellationDeltaA_mulVec_eq_zero A y u hy
  have hDRP :=
    higham21Thm21_3ResidualDeltaA_projector_eq_zero theta A b y hy
  have hbasey :
      rectMatMulVec base y =
        fun i => (theta ^ 2 / den * Y) * r i := by
    rw [show base = fun i j => DR i j + DP i j by rfl]
    rw [rectMatMulVec_mat_add, hDRy, hDPy]
    ext i
    simp only [Pi.zero_apply, add_zero]
    dsimp [DR, r, Y, den]
  have hbaseP :
      rectMatMul base (undetApproxComplementProjector y) =
        rectMatMul DP (undetApproxComplementProjector y) := by
    rw [show base = fun i j => DR i j + DP i j by rfl]
    rw [rectMatMul_add_left, hDRP]
    ext i j
    simp
  have hDPprojector :
      frobNormSqRect DP =
        frobNormSqRect (rectMatMul DP (undetApproxComplementProjector y)) := by
    have hpyth :=
      higham21_thm21_3_right_projector_frobNormSqRect_pythagoras DP y hy
    rw [hDPy] at hpyth
    simpa [vecNorm2Sq] using hpyth
  have hDPfrob : frobNormSqRect DP = sigma ^ 2 := by
    have hrank :=
      lsNormwiseBackwardErrorRankOneDeltaA_frobNormSq
        (p := u) (u := w) hU
    have hattain' : vecNorm2Sq w = sigma ^ 2 * vecNorm2Sq u := by
      simpa [w, sigma, M] using hattain
    rw [show DP = lsNormwiseBackwardErrorRankOneDeltaA u w by
      rfl, hrank, hattain']
    apply (div_eq_iff hU).2
    rfl
  have hbasefrob :
      frobNormSqRect base =
        (theta ^ 2 / den) ^ 2 * Y * R + sigma ^ 2 := by
    have hpyth :=
      higham21_thm21_3_right_projector_frobNormSqRect_pythagoras base y hy
    rw [hbasey, hbaseP, <- hDPprojector, hDPfrob] at hpyth
    have hnorm :
        vecNorm2Sq (fun i : Fin (m + 1) => (theta ^ 2 / den * Y) * r i) =
          (theta ^ 2 / den * Y) ^ 2 * R := by
      simpa [R] using vecNorm2Sq_smul (theta ^ 2 / den * Y) r
    rw [hnorm] at hpyth
    rw [hpyth]
    change
      (theta ^ 2 / den * Y) ^ 2 * R / Y + sigma ^ 2 =
        (theta ^ 2 / den) ^ 2 * Y * R + sigma ^ 2
    field_simp [hY]
  have hdbnorm : vecNorm2Sq db = (1 / den) ^ 2 * R := by
    simpa [db, higham21Thm21_3ResidualDeltab, r, den] using
      vecNorm2Sq_smul (-(1 / den)) r
  have hcostsq :
      lsNormwiseBackwardErrorCostF theta base db ^ 2 =
        theta ^ 2 * R / den + sigma ^ 2 := by
    rw [lsNormwiseBackwardErrorCostF_sq, hbasefrob, hdbnorm]
    field_simp [hden] <;> ring
  have hrhssq :
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y sigma ^ 2 =
        theta ^ 2 * R / den + sigma ^ 2 := by
    rw [undetNormwiseBackwardErrorNonzeroFormulaRHS_sq]
    change
      theta ^ 2 * Y / den * (R / Y) + sigma ^ 2 =
        theta ^ 2 * R / den + sigma ^ 2
    field_simp [hY, hden]
  have hbase_eq :
      higham21Thm21_3ApproxDeltaA theta A b y u 0 = base := by
    ext i j
    simp [higham21Thm21_3ApproxDeltaA, base, DR, DP,
      higham21Thm21_3SignedExtraDeltaA,
      lsNormwiseBackwardErrorRankTwoExtraDeltaA]
  have hdb_eq :
      higham21Thm21_3ApproxDeltab theta A b y u 0 = db := by
    ext i
    simp [higham21Thm21_3ApproxDeltab, db]
  rw [hbase_eq, hdb_eq]
  apply (sq_eq_sq₀
    (lsNormwiseBackwardErrorCostF_nonneg theta base db)
    (undetNormwiseBackwardErrorNonzeroFormulaRHS_nonneg theta A b y sigma)).mp
  rw [hcostsq, hrhssq]

/-- Cost of the signed family is at most its exact `t = 0` value plus the
    homogeneous cost of the small residual-preserving term. -/
theorem higham21Thm21_3Approx_cost_le_formulaRHS_add
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real) (b : Fin (m + 1) -> Real)
    (y : Fin n -> Real) (u : Fin (m + 1) -> Real) (t : Real)
    (hy : y ≠ 0) (hu : u ≠ 0)
    (hattain :
      vecNorm2Sq
          (rectTransposeMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) u) =
        higham21SigmaMinRow (undetNormwiseBackwardErrorFormulaMatrix A y) ^ 2 *
          vecNorm2Sq u) :
    lsNormwiseBackwardErrorCostF theta
        (higham21Thm21_3ApproxDeltaA theta A b y u t)
        (higham21Thm21_3ApproxDeltab theta A b y u t) <=
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
          (higham21SigmaMinRow (undetNormwiseBackwardErrorFormulaMatrix A y)) +
        |t| * lsNormwiseBackwardErrorCostF theta
          (higham21Thm21_3SignedExtraDeltaA 1 u y) u := by
  let baseA := higham21Thm21_3ApproxDeltaA theta A b y u 0
  let baseb := higham21Thm21_3ApproxDeltab theta A b y u 0
  let E := higham21Thm21_3SignedExtraDeltaA 1 u y
  have hA :
      higham21Thm21_3ApproxDeltaA theta A b y u t =
        fun i j => baseA i j + t * E i j := by
    ext i j
    simp [higham21Thm21_3ApproxDeltaA, baseA, E,
      higham21Thm21_3SignedExtraDeltaA,
      lsNormwiseBackwardErrorRankTwoExtraDeltaA]
    ring
  have hb :
      higham21Thm21_3ApproxDeltab theta A b y u t =
        fun i => baseb i + t * u i := by
    ext i
    simp [higham21Thm21_3ApproxDeltab, baseb]
  rw [hA, hb]
  calc
    lsNormwiseBackwardErrorCostF theta
          (fun i j => baseA i j + t * E i j) (fun i => baseb i + t * u i) <=
        lsNormwiseBackwardErrorCostF theta baseA baseb +
          lsNormwiseBackwardErrorCostF theta
            (fun i j => t * E i j) (fun i => t * u i) :=
      higham21_lsNormwiseBackwardErrorCostF_add_le theta baseA
        (fun i j => t * E i j) baseb (fun i => t * u i)
    _ = undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
          (higham21SigmaMinRow (undetNormwiseBackwardErrorFormulaMatrix A y)) +
        |t| * lsNormwiseBackwardErrorCostF theta E u := by
      rw [higham21Thm21_3Approx_cost_zero_eq_formulaRHS_of_attaining
        htheta A b y u hy hu hattain]
      rw [higham21_lsNormwiseBackwardErrorCostF_smul]

/-- Higham, Theorem 21.3, nonzero upper route: for every positive epsilon,
    an explicit signed perturbation is feasible and has weighted cost at most
    the printed formula plus epsilon.  No exact attaining feasible witness is
    asserted. -/
theorem higham21_thm21_3_nonzero_upper_epsilon
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real) (b : Fin (m + 1) -> Real)
    (y : Fin n -> Real) (hy : y ≠ 0)
    (eps : Real) (heps : 0 < eps) :
    exists (DeltaA : Fin (m + 1) -> Fin n -> Real)
        (Deltab : Fin (m + 1) -> Real),
      UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab /\
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab <=
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
              (higham21SigmaMinRow
                (undetNormwiseBackwardErrorFormulaMatrix A y)) + eps := by
  let M := undetNormwiseBackwardErrorFormulaMatrix A y
  obtain ⟨u, hu, hattain⟩ :=
    higham21SigmaMinRow_exists_real_attaining_vector_sq M
  let db0 := higham21Thm21_3ResidualDeltab theta A b y
  let U := vecNorm2Sq u
  let a := ∑ i : Fin (m + 1), u i * (b i + db0 i)
  let K := lsNormwiseBackwardErrorCostF theta
    (higham21Thm21_3SignedExtraDeltaA 1 u y) u
  have hU : 0 < U := by
    exact lt_of_le_of_ne (vecNorm2Sq_nonneg u)
      (Ne.symm (by simpa [U] using higham21_vecNorm2Sq_ne_zero_of_ne_zero hu))
  have hK : 0 <= K := by
    exact lsNormwiseBackwardErrorCostF_nonneg theta
      (higham21Thm21_3SignedExtraDeltaA 1 u y) u
  obtain ⟨t, ht, htcost⟩ :=
    higham21_exists_signed_small_parameter a U K eps hU hK heps
  let DeltaA := higham21Thm21_3ApproxDeltaA theta A b y u t
  let Deltab := higham21Thm21_3ApproxDeltab theta A b y u t
  refine ⟨DeltaA, Deltab, ?_, ?_⟩
  · apply
      (undetNormwiseBackwardErrorFeasible_iff_system_eq_and_exists_transpose_witness
        A b y DeltaA Deltab).2
    have hsystem :
        rectMatMulVec (fun i j => A i j + DeltaA i j) y =
          fun i => b i + Deltab i := by
      simpa [DeltaA, Deltab] using
        higham21Thm21_3Approx_system_eq theta A b y u t hy
    refine ⟨hsystem, ?_⟩
    have hY : vecNorm2Sq y ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
    have hdot :
        (∑ i : Fin (m + 1), u i * (b i + Deltab i)) = a + t * U := by
      dsimp [Deltab, higham21Thm21_3ApproxDeltab, a, db0, U]
      calc
        (∑ i : Fin (m + 1),
            u i * (b i +
              (higham21Thm21_3ResidualDeltab theta A b y i + t * u i))) =
            ∑ i : Fin (m + 1),
              (u i * (b i + higham21Thm21_3ResidualDeltab theta A b y i) +
                t * (u i ^ 2)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i : Fin (m + 1),
              u i * (b i + higham21Thm21_3ResidualDeltab theta A b y i)) +
              t * ∑ i : Fin (m + 1), u i ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (∑ i : Fin (m + 1),
              u i * (b i + higham21Thm21_3ResidualDeltab theta A b y i)) +
              t * vecNorm2Sq u := by rfl
    have hdot_ne :
        (∑ i : Fin (m + 1), u i * (b i + Deltab i)) ≠ 0 := by
      rw [hdot]
      exact ht
    let q :=
      (∑ i : Fin (m + 1), u i * (b i + Deltab i)) / vecNorm2Sq y
    have hq : q ≠ 0 := div_ne_zero hdot_ne hY
    have htrans :
        rectTransposeMulVec (fun i j => A i j + DeltaA i j) u =
          fun j => q * y j := by
      simpa [DeltaA, Deltab, q] using
        higham21Thm21_3Approx_transpose_action theta A b y u t hy hu
    refine ⟨(fun i => (1 / q) * u i), ?_⟩
    ext j
    have htransj :
        (∑ i : Fin (m + 1), (A i j + DeltaA i j) * u i) = q * y j := by
      simpa [rectTransposeMulVec] using congrFun htrans j
    unfold rectTransposeMulVec
    calc
      (∑ i : Fin (m + 1),
          (A i j + DeltaA i j) * ((1 / q) * u i)) =
          (1 / q) *
            (∑ i : Fin (m + 1), (A i j + DeltaA i j) * u i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (1 / q) * (q * y j) := by rw [htransj]
      _ = y j := by field_simp [hq]
  · have hcost :=
      higham21Thm21_3Approx_cost_le_formulaRHS_add
        htheta A b y u t hy hu (by simpa [M] using hattain)
    exact hcost.trans (by
      have htcost' : |t| * K ≤ eps := htcost
      nlinarith)

/-- Infimum consequence of the epsilon-feasible upper construction. -/
theorem higham21_thm21_3_etaF_le_nonzeroFormulaRHS
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real) (b : Fin (m + 1) -> Real)
    (y : Fin n -> Real) (hy : y ≠ 0) :
    undetNormwiseBackwardErrorEtaF theta A b y <=
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
        (higham21SigmaMinRow (undetNormwiseBackwardErrorFormulaMatrix A y)) := by
  refine le_of_forall_pos_le_add ?_
  intro eps heps
  obtain ⟨DeltaA, Deltab, hfeas, hcost⟩ :=
    higham21_thm21_3_nonzero_upper_epsilon
      htheta A b y hy eps heps
  exact
    (undetNormwiseBackwardErrorEtaF_le_costF_of_feasible
      theta A b y DeltaA Deltab hfeas).trans hcost

/-- Higham, 2nd ed., Chapter 21, Theorem 21.3, nonzero branch: the normwise
    backward-error infimum is exactly the displayed Sun--Sun formula with the
    smallest row singular value of `A(I - y y^+)`. -/
theorem higham21_theorem21_3_nonzero_normwise_backward_error_formula
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real) (b : Fin (m + 1) -> Real)
    (y : Fin n -> Real) (hy : y ≠ 0) :
    undetNormwiseBackwardErrorEtaF theta A b y =
      undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
        (higham21SigmaMinRow
          (undetNormwiseBackwardErrorFormulaMatrix A y)) := by
  apply le_antisymm
  · exact higham21_thm21_3_etaF_le_nonzeroFormulaRHS
      htheta A b y hy
  · apply
      undetNormwiseBackwardErrorNonzeroFormulaRHS_le_etaF_of_forall_feasible_cost_ge
    · obtain ⟨DeltaA, Deltab, hfeas, _hcost⟩ :=
        higham21_thm21_3_nonzero_upper_epsilon
          htheta A b y hy 1 zero_lt_one
      exact
        ⟨lsNormwiseBackwardErrorCostF theta DeltaA Deltab,
          DeltaA, Deltab, hfeas, rfl⟩
    · intro DeltaA Deltab hfeas
      exact
        higham21_thm21_3_nonzeroFormulaRHS_le_costF_of_feasible
          theta A b hy DeltaA Deltab hfeas

/-- Higham, 2nd ed., Chapter 21, Theorem 21.3: complete case-split formula
    for the normwise Frobenius backward error of an approximate minimum-norm
    solution. -/
theorem higham21_theorem21_3_normwise_backward_error_formula
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real) (b : Fin (m + 1) -> Real)
    (y : Fin n -> Real) :
    undetNormwiseBackwardErrorEtaF theta A b y =
      if y = 0 then theta * vecNorm2 b
      else
        undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
          (higham21SigmaMinRow
            (undetNormwiseBackwardErrorFormulaMatrix A y)) := by
  by_cases hy : y = 0
  · subst y
    simpa using higham21_thm21_3_etaF_zero theta htheta A b
  · simpa [hy] using
      higham21_theorem21_3_nonzero_normwise_backward_error_formula
        htheta A b y hy

-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    a columnwise Householder QR perturbation bound for `Aᵀ` is exactly a
    row-wise perturbation bound for the transposed perturbation of `A`. -/
theorem higham21_rectRowNorm2_eq_columnFrob_finiteTranspose {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    rectRowNorm2 A i = columnFrob (finiteTranspose A) i := by
  simp [rectRowNorm2, columnFrob_eq_vecNorm2, finiteTranspose]

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    transposing a Chapter 19 columnwise QR perturbation certificate turns its
    column bounds into the row-wise bounds used by the underdetermined-system
    backward-error definition. -/
theorem higham21_row_bounds_of_transposed_qr_column_bounds {m n : ℕ}
    (AT DeltaAT : Fin n → Fin m → ℝ) {eta : ℝ}
    (hcol : ∀ i : Fin m,
      columnFrob DeltaAT i ≤ eta * columnFrob AT i) :
    ∀ i : Fin m,
      rectRowNorm2 (finiteTranspose DeltaAT) i ≤
        eta * rectRowNorm2 (finiteTranspose AT) i := by
  intro i
  simpa [higham21_rectRowNorm2_eq_columnFrob_finiteTranspose] using hcol i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    source-facing QR dependency for the Q method.  Applying Chapter 19,
    Theorem 19.4 to `Aᵀ` gives a perturbation `DeltaA0` of the original
    underdetermined matrix whose rows satisfy the printed row-wise QR bound.

    This is only the QR factorization perturbation used in the proof of
    Theorem 21.4; the triangular-solve and final `Q`-application perturbations
    remain separate obligations before the full Q-method theorem closes. -/
theorem higham21_theorem21_4_qr_transpose_row_perturbation_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ)
    (R_hat : Fin n → Fin m → ℝ)
    (eta : ℝ)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError n m
      (finiteTranspose A) Q R_hat eta) :
    ∃ DeltaA0 : Fin m → Fin n → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect n n m Q R_hat j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤ eta * rectRowNorm2 A i) := by
  rcases hqr.result with ⟨DeltaAT, hrep, hcol⟩
  refine ⟨finiteTranspose DeltaAT, ?_, ?_⟩
  · intro i j
    simpa [finiteTranspose] using hrep j i
  · intro i
    have hrow :=
      higham21_row_bounds_of_transposed_qr_column_bounds
        (finiteTranspose A) DeltaAT hcol i
    simpa [finiteTranspose_finiteTranspose] using hrow

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete Householder QR instantiation of the transposed row-perturbation
    dependency for `Aᵀ`.  The dimension hypotheses are the Chapter 19 tall-panel
    side conditions for the matrix `Aᵀ : ℝ^(n×m)`. -/
theorem higham21_theorem21_4_householder_qr_transpose_row_perturbation_bound
    {m n : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hmn : m ≤ n)
    (hvalid :
      gammaValid fp (m * householderConstructApplyGammaIndex n)) :
    ∃ DeltaA0 : Fin m → Fin n → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect n n m
          (fl_householderQRPanel_Q fp n m (finiteTranspose A))
          (fl_householderQRPanel_R fp n m (finiteTranspose A)) j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤
          H19.Theorem19_4.gamma_tilde fp n m * rectRowNorm2 A i) := by
  exact
    higham21_theorem21_4_qr_transpose_row_perturbation_bound A
      (fl_householderQRPanel_Q fp n m (finiteTranspose A))
      (fl_householderQRPanel_R fp n m (finiteTranspose A))
      (H19.Theorem19_4.gamma_tilde fp n m)
      (H19.Theorem19_4.householder_qr_backward_error
        fp n m (finiteTranspose A) hm hmn hvalid)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular-solve dependency for the Q-method proof.  Applying the existing
    forward-substitution backward-error theorem to `R_hatᵀ` gives the printed
    perturbation form `(R_hat + DeltaR)ᵀ y_hat1 = b` with a componentwise
    `gamma_m` bound on `DeltaR`. -/
theorem higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
    (fp : FPModel) (m : ℕ)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      ∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i := by
  let L : Fin m → Fin m → ℝ := matTranspose R_hat
  have hLdiag : ∀ i : Fin m, L i i ≠ 0 := by
    intro i
    simpa [L, matTranspose] using hdiag i
  have hlower : ∀ i j : Fin m, i.val < j.val → L i j = 0 := by
    intro i j hij
    simpa [L, matTranspose] using hupper j i hij
  obtain ⟨DeltaL, hDeltaL, hsolve⟩ :=
    forwardSub_backward_error fp m L b hLdiag hlower hvalid
  let DeltaR : Fin m → Fin m → ℝ := matTranspose DeltaL
  refine ⟨DeltaR, ?_, ?_⟩
  · intro i j
    simpa [DeltaR, L, matTranspose] using hDeltaL j i
  · intro i
    simpa [DeltaR, L, matTranspose, matMulVec] using hsolve i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular perturbation nonsingularity for the rounded `R_hat^T` solve.
    If an upper-triangular factor has nonzero diagonal and the perturbation is
    entrywise relatively bounded by a factor below one, then the perturbed
    transpose factor remains nonsingular. -/
theorem higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
    {m : ℕ}
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    {eta : ℝ} (heta_lt : eta < 1)
    (hDelta : ∀ i j, |DeltaR i j| ≤ eta * |R_hat i j|) :
    Matrix.det
        (matTranspose (fun a b => R_hat a b + DeltaR a b) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let Tpert : Fin m → Fin m → ℝ :=
    matTranspose (fun a b => R_hat a b + DeltaR a b)
  have hlowerPert : ∀ i j : Fin m, i.val < j.val → Tpert i j = 0 := by
    intro i j hij
    have hR : R_hat j i = 0 := hupper j i hij
    have hbound : |DeltaR j i| ≤ 0 := by
      simpa [hR] using hDelta j i
    have hDeltaZero : DeltaR j i = 0 := by
      exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg (DeltaR j i)))
    simp [Tpert, matTranspose, hR, hDeltaZero]
  have hdiagPert : ∀ i : Fin m, Tpert i i ≠ 0 := by
    intro i hzero
    have hsum : R_hat i i + DeltaR i i = 0 := by
      simpa [Tpert, matTranspose] using hzero
    have hDelta_eq : DeltaR i i = -R_hat i i := by
      linarith
    have habs_eq : |DeltaR i i| = |R_hat i i| := by
      rw [hDelta_eq, abs_neg]
    have hle : |R_hat i i| ≤ eta * |R_hat i i| := by
      simpa [habs_eq] using hDelta i i
    have hpos : 0 < |R_hat i i| := abs_pos.mpr (hdiag i)
    nlinarith
  have hdet :
      Matrix.det (Tpert : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    det_ne_zero_of_lower_triangular_diag_ne_zero m
      Tpert
      hlowerPert hdiagPert
  simpa [Tpert] using hdet

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular-solve handoff into the exact Q-method minimum-norm theorem.
    The rounded solve of `R_hat^T y = b` supplies a perturbation `DeltaR`;
    if the perturbed transpose factor is nonsingular, then the formed
    Q-method vector is the exact minimum-norm solution for the corresponding
    perturbed QR-coordinate system.

    This is not the full row-wise backward-stability theorem: it isolates the
    remaining nonsingularity and row-wise perturbation obligations from the
    already proved triangular-solve backward-error certificate. -/
theorem higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
    {m k : ℕ} (fp : FPModel)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      (Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 →
        RectMinNormSolution m (m + k)
          (finiteTranspose
            (matMulRectLeft Q
              (lsQRTallBlock (k := k) (fun a b => R_hat a b + DeltaR a b))))
          b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))) := by
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag hupper hvalid
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hdetT
  let Rpert : Fin m → Fin m → ℝ := fun a b => R_hat a b + DeltaR a b
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  have hy1 : (fun j : Fin m => ∑ i : Fin m, Rpert i j * y1 i) = b := by
    ext j
    simpa [Rpert, y1, matMulVec, matTranspose] using hsolve j
  exact
    higham21_eq21_3_q_method_min_norm_of_qr_det_ne_zero
      Q hQ Rpert b y1 hdetT hy1

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free triangular-solve handoff for the Q-method minimum-norm
    theorem.  The stronger guard `gammaValid fp (2*m)` makes `gamma_m < 1`,
    so the componentwise triangular perturbation preserves nonsingularity of
    the perturbed transpose factor. -/
theorem higham21_theorem21_4_forwardSub_q_method_min_norm_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      RectMinNormSolution m (m + k)
        (finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k) (fun a b => R_hat a b + DeltaR a b))))
        b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ))) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hminCond⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
      fp Q hQ R_hat b hdiag hupper hvalid
  have hdet :
      Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
      R_hat DeltaR hdiag hupper (gamma_lt_one fp m hvalid2) hDeltaR
  exact ⟨DeltaR, hDeltaR, hsolve, hminCond hdet⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    row-wise backward-error handoff after the triangular solve.  The theorem
    combines the forward-substitution perturbation certificate with the
    existing Lemma 21.2 row-wise witness surface.  The remaining source work is
    exactly the Q-method row-wise assembly: identify the single Lemma 21.2
    perturbation with the perturbed QR-coordinate system and prove the two
    source row bounds. -/
theorem higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (DeltaA1 DeltaA2 : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      (Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 →
        (fun i j =>
            A i j +
              undetLemma21_2SinglePerturbation
                (matMulVec (m + k) Q
                  (Fin.append
                    (fl_forwardSub fp m (matTranspose R_hat) b)
                    (0 : Fin k → ℝ)))
                DeltaA1 DeltaA2 i j) =
          finiteTranspose
            (matMulRectLeft Q
              (lsQRTallBlock (k := k)
                (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hminCond⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
      fp Q hQ R_hat b hdiag hupper hvalid
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hdet hsingle
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q
      (Fin.append
        (fl_forwardSub fp m (matTranspose R_hat) b)
        (0 : Fin k → ℝ))
  let A_qr : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose
      (matMulRectLeft Q
        (lsQRTallBlock (k := k)
          (fun a b => R_hat a b + DeltaR a b)))
  have hminQR : RectMinNormSolution m (m + k) A_qr b x_hat := by
    simpa [A_qr, x_hat] using hminCond hdet
  have hsingle' :
      (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        = A_qr := by
    simpa [A_qr, x_hat] using hsingle
  have hminSingle :
      RectMinNormSolution m (m + k)
        (fun i j =>
          A i j + undetLemma21_2SinglePerturbation x_hat DeltaA1 DeltaA2 i j)
        b x_hat := by
    rw [hsingle']
    exact hminQR
  simpa [x_hat] using
    higham21_lemma21_2_rowwise_backward_error_bound_of_common_row_bound
      A DeltaA1 DeltaA2 b x_hat heta hminSingle
      hDeltaA1Row hDeltaA2Row

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free row-wise backward-error handoff after the triangular
    solve.  Compared with
    `higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff`, the
    stronger `gammaValid fp (2*m)` guard discharges the perturbed transpose
    factor nonsingularity side condition. -/
theorem higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    (DeltaA1 DeltaA2 : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaA1Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i)
    (hDeltaA2Row : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      ((fun i j =>
          A i j +
            undetLemma21_2SinglePerturbation
              (matMulVec (m + k) Q
                (Fin.append
                  (fl_forwardSub fp m (matTranspose R_hat) b)
                  (0 : Fin k → ℝ)))
              DeltaA1 DeltaA2 i j) =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hrowCond⟩ :=
    higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff
      fp A Q hQ R_hat b hdiag hupper hvalid DeltaA1 DeltaA2
      heta hDeltaA1Row hDeltaA2Row
  have hdet :
      Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
      R_hat DeltaR hdiag hupper (gamma_lt_one fp m hvalid2) hDeltaR
  exact ⟨DeltaR, hDeltaR, hsolve, fun hsingle => hrowCond hdet hsingle⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    common-perturbation specialization of the row-wise Q-method handoff.
    Taking `DeltaA1 = DeltaA2 = DeltaA` reduces the Lemma 21.2 single
    perturbation equality to the ordinary QR assembly equality
    `A + DeltaA = (Q [R_hat + DeltaR; 0])^T`. -/
theorem higham21_theorem21_4_forwardSub_single_perturbation_rowwise_backward_error_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    (DeltaA : Fin m → Fin (m + k) → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaARow : ∀ i : Fin m,
      rectRowNorm2 DeltaA i ≤ eta * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      ((fun i j => A i j + DeltaA i j) =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun a b => R_hat a b + DeltaR a b))) →
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))
          (Real.sqrt 2 * eta)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hrowCond⟩ :=
    higham21_theorem21_4_forwardSub_rowwise_backward_error_handoff_of_gammaValid2
      fp A Q hQ R_hat b hdiag hupper hvalid hvalid2
      DeltaA DeltaA heta hDeltaARow hDeltaARow
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hqr
  apply hrowCond
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q
      (Fin.append
        (fl_forwardSub fp m (matTranspose R_hat) b)
        (0 : Fin k → ℝ))
  calc
    (fun i j =>
        A i j +
          undetLemma21_2SinglePerturbation x_hat DeltaA DeltaA i j)
        = (fun i j => A i j + DeltaA i j) := by
          have hsame :=
            higham21_lemma21_2_single_perturbation_same x_hat DeltaA
          ext i j
          rw [congrFun (congrFun hsame i) j]
    _ =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun a b => R_hat a b + DeltaR a b))) := hqr

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    QR assembly equality for adding the triangular-solve perturbation to an
    existing QR perturbation.  If `A + DeltaA0` is represented by
    `(Q [R_hat;0])^T`, then adding the lifted block
    `(Q [DeltaR;0])^T` gives the represented system
    `(Q [R_hat + DeltaR;0])^T`. -/
theorem higham21_theorem21_4_qr_deltaR_assembly_eq
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat))) :
    (fun i j =>
        A i j +
          (DeltaA0 i j +
            finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) i j)) =
      finiteTranspose
        (matMulRectLeft Q
          (lsQRTallBlock (k := k)
            (fun i j => R_hat i j + DeltaR i j))) := by
  have hblock :
      (fun i j =>
          lsQRTallBlock (k := k) R_hat i j +
            lsQRTallBlock (k := k) DeltaR i j) =
        lsQRTallBlock (k := k)
          (fun i j => R_hat i j + DeltaR i j) :=
    lsQRTallBlock_add R_hat DeltaR
  have hmul :
      (fun i j =>
          matMulRectLeft Q (lsQRTallBlock (k := k) R_hat) i j +
            matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) i j) =
        matMulRectLeft Q
          (lsQRTallBlock (k := k)
            (fun i j => R_hat i j + DeltaR i j)) := by
    rw [← hblock]
    exact (matMulRectLeft_add_right Q
      (lsQRTallBlock (k := k) R_hat)
      (lsQRTallBlock (k := k) DeltaR)).symm
  ext i j
  have hAij := congrFun (congrFun hA i) j
  have hmulji := congrFun (congrFun hmul j) i
  simp [finiteTranspose] at hAij hmulji ⊢
  calc
    A i j + (DeltaA0 i j + matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) j i)
        = (A i j + DeltaA0 i j) +
            matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) j i := by ring
    _ = matMulRectLeft Q (lsQRTallBlock (k := k) R_hat) j i +
          matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) j i := by
          rw [hAij]
    _ = matMulRectLeft Q
          (lsQRTallBlock (k := k)
            (fun i j => R_hat i j + DeltaR i j)) j i := hmulji

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    row-wise triangle-inequality adapter for assembling two perturbation
    bounds against the same source matrix. -/
theorem higham21_rectRowNorm2_add_le_of_row_bounds
    {m n : ℕ}
    (DeltaA DeltaB A : Fin m → Fin n → ℝ)
    {etaA etaB : ℝ}
    (hDeltaA : ∀ i : Fin m,
      rectRowNorm2 DeltaA i ≤ etaA * rectRowNorm2 A i)
    (hDeltaB : ∀ i : Fin m,
      rectRowNorm2 DeltaB i ≤ etaB * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2 (fun r c => DeltaA r c + DeltaB r c) i ≤
      (etaA + etaB) * rectRowNorm2 A i := by
  calc
    rectRowNorm2 (fun r c => DeltaA r c + DeltaB r c) i
        = vecNorm2 (fun j : Fin n => DeltaA i j + DeltaB i j) := rfl
    _ ≤ vecNorm2 (fun j : Fin n => DeltaA i j) +
          vecNorm2 (fun j : Fin n => DeltaB i j) := by
          exact vecNorm2_add_le
            (fun j : Fin n => DeltaA i j)
            (fun j : Fin n => DeltaB i j)
    _ = rectRowNorm2 DeltaA i + rectRowNorm2 DeltaB i := rfl
    _ ≤ etaA * rectRowNorm2 A i + etaB * rectRowNorm2 A i := by
          exact add_le_add (hDeltaA i) (hDeltaB i)
    _ = (etaA + etaB) * rectRowNorm2 A i := by ring

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    once the QR perturbation and lifted triangular-solve perturbation are
    bounded row-wise against `A`, their assembled common perturbation satisfies
    the summed row-wise bound used by the Q-method proof. -/
theorem higham21_theorem21_4_common_perturbation_row_bound_of_qr_and_lifted_bounds
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR : ℝ}
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i : Fin m,
      rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i ≤
        etaR * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2
        (fun r c =>
          DeltaA0 r c +
            finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) r c) i ≤
      (etaQR + etaR) * rectRowNorm2 A i :=
  higham21_rectRowNorm2_add_le_of_row_bounds
    DeltaA0
    (finiteTranspose
      (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)))
    A hDeltaA0 hDeltaR i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    an orthogonal left factor preserves each column norm of a rectangular
    panel.  This is the per-column form needed for the lifted triangular
    perturbation `(Q [DeltaR;0])^T`. -/
theorem higham21_columnFrob_matMulRectLeft_orthogonal
    {m n : ℕ}
    (Q : Fin m → Fin m → ℝ)
    (B : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (j : Fin n) :
    columnFrob (matMulRectLeft Q B) j = columnFrob B j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  have hcol :
      (fun i : Fin m => matMulRectLeft Q B i j) =
        matMulVec m Q (fun i : Fin m => B i j) := by
    ext i
    rfl
  rw [hcol]
  exact vecNorm2_orthogonal Q (fun i : Fin m => B i j) hQ

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    stacking zero rows below a square triangular perturbation preserves each
    column Frobenius norm. -/
theorem higham21_columnFrob_lsQRTallBlock
    {m k : ℕ}
    (R : Fin m → Fin m → ℝ)
    (j : Fin m) :
    columnFrob (lsQRTallBlock (k := k) R) j = columnFrob R j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  have hcol :
      (fun i : Fin (m + k) => lsQRTallBlock (k := k) R i j) =
        Fin.append (fun i : Fin m => R i j) (0 : Fin k → ℝ) := by
    ext i
    refine Fin.addCases
      (motive := fun i : Fin (m + k) =>
        lsQRTallBlock (k := k) R i j =
          Fin.append (fun i : Fin m => R i j) (0 : Fin k → ℝ) i)
      ?left ?right i
    · intro i
      simp [lsQRTallBlock, Fin.append_left]
    · intro i
      simp [lsQRTallBlock, Fin.append_right]
  rw [hcol]
  unfold vecNorm2
  rw [lsVecNorm2Sq_append]
  simp [vecNorm2Sq]

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the lifted triangular block has row norm equal to the corresponding column
    norm of the triangular perturbation when the QR factor is orthogonal. -/
theorem higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
    {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (DeltaR : Fin m → Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (j : Fin m) :
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) j =
      columnFrob DeltaR j := by
  calc
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) j
        = columnFrob
            (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) j := by
          simp [rectRowNorm2, columnFrob_eq_vecNorm2, finiteTranspose]
    _ = columnFrob (lsQRTallBlock (k := k) DeltaR) j := by
          exact higham21_columnFrob_matMulRectLeft_orthogonal
            Q (lsQRTallBlock (k := k) DeltaR) hQ j
    _ = columnFrob DeltaR j := higham21_columnFrob_lsQRTallBlock DeltaR j

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    columnwise control of the triangular perturbation gives the row-wise bound
    for its lifted original-coordinate perturbation. -/
theorem higham21_theorem21_4_lifted_deltaR_row_bound_of_column_bound
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (DeltaR : Fin m → Fin m → ℝ)
    {etaR : ℝ}
    (hQ : IsOrthogonal (m + k) Q)
    (hDeltaRCol : ∀ i : Fin m,
      columnFrob DeltaR i ≤ etaR * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i ≤
      etaR * rectRowNorm2 A i := by
  rw [higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
    Q DeltaR hQ i]
  exact hDeltaRCol i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    entrywise relative bounds on the triangular perturbation imply the
    corresponding columnwise Euclidean bound. -/
theorem higham21_columnFrob_le_of_entrywise_relative_bound
    {m : ℕ}
    (R DeltaR : Fin m → Fin m → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ eta * |R i j|)
    (j : Fin m) :
    columnFrob DeltaR j ≤ eta * columnFrob R j := by
  calc
    columnFrob DeltaR j
        = vecNorm2 (fun i : Fin m => DeltaR i j) := by
          rw [columnFrob_eq_vecNorm2]
    _ ≤ vecNorm2 (fun i : Fin m => eta * |R i j|) := by
          exact
            vecNorm2_le_of_abs_le
              (fun i : Fin m => DeltaR i j)
              (fun i : Fin m => eta * |R i j|)
              (fun i => hDeltaR i j)
    _ = eta * columnFrob R j := by
          rw [vecNorm2_smul, abs_of_nonneg heta, vecNorm2_abs,
            columnFrob_eq_vecNorm2]

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    if `A + DeltaA0 = (Q [R_hat;0])^T`, then the row norm of the assembled
    QR side is the corresponding column norm of `R_hat`. -/
theorem higham21_theorem21_4_assembled_qr_row_norm_eq_R_columnFrob
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (j : Fin m) :
    rectRowNorm2 (fun i j => A i j + DeltaA0 i j) j =
      columnFrob R_hat j := by
  rw [hA]
  exact higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
    Q R_hat hQ j

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    componentwise triangular-solve backward error, together with the QR
    assembly and QR row perturbation bound, gives a row-wise bound for the
    lifted triangular perturbation `(Q [DeltaR;0])^T` relative to the original
    underdetermined matrix `A`. -/
theorem higham21_theorem21_4_lifted_deltaR_row_bound_of_entrywise_relative
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR : ℝ} (hetaR : 0 ≤ etaR)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (i : Fin m) :
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i ≤
      etaR * (1 + etaQR) * rectRowNorm2 A i := by
  have hcol :
      columnFrob DeltaR i ≤ etaR * columnFrob R_hat i :=
    higham21_columnFrob_le_of_entrywise_relative_bound
      R_hat DeltaR hetaR hDeltaR i
  have hassembled_eq :
      rectRowNorm2 (fun r c => A r c + DeltaA0 r c) i =
        columnFrob R_hat i :=
    higham21_theorem21_4_assembled_qr_row_norm_eq_R_columnFrob
      A DeltaA0 Q R_hat hQ hA i
  have hAself : ∀ r : Fin m,
      rectRowNorm2 A r ≤ (1 : ℝ) * rectRowNorm2 A r := by
    intro r
    rw [one_mul]
  have hassembled_bound :
      rectRowNorm2 (fun r c => A r c + DeltaA0 r c) i ≤
        (1 + etaQR) * rectRowNorm2 A i :=
    higham21_rectRowNorm2_add_le_of_row_bounds
      A DeltaA0 A hAself hDeltaA0 i
  calc
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i
        = columnFrob DeltaR i := by
          exact higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
            Q DeltaR hQ i
    _ ≤ etaR * columnFrob R_hat i := hcol
    _ = etaR * rectRowNorm2 (fun r c => A r c + DeltaA0 r c) i := by
          rw [← hassembled_eq]
    _ ≤ etaR * ((1 + etaQR) * rectRowNorm2 A i) :=
          mul_le_mul_of_nonneg_left hassembled_bound hetaR
    _ = etaR * (1 + etaQR) * rectRowNorm2 A i := by ring

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    combines the QR row perturbation and the componentwise triangular-solve
    perturbation into the row-wise bound for the common perturbation assembled
    as `DeltaA0 + (Q [DeltaR;0])^T`. -/
theorem higham21_theorem21_4_common_perturbation_row_bound_of_entrywise_deltaR
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR : ℝ} (hetaR : 0 ≤ etaR)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (i : Fin m) :
    rectRowNorm2
        (fun r c =>
          DeltaA0 r c +
            finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) r c) i ≤
      (etaQR + etaR * (1 + etaQR)) * rectRowNorm2 A i :=
  higham21_theorem21_4_common_perturbation_row_bound_of_qr_and_lifted_bounds
    A DeltaA0 Q DeltaR hDeltaA0
    (fun r =>
      higham21_theorem21_4_lifted_deltaR_row_bound_of_entrywise_relative
        A DeltaA0 Q R_hat DeltaR hetaR hQ hA hDeltaA0 hDeltaR r)
    i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free row-wise Q-method handoff after QR assembly.  Given the
    QR perturbation for `A`, the componentwise triangular-solve perturbation,
    and the orthogonal QR factor, the assembled perturbation
    `DeltaA0 + (Q [DeltaR;0])^T` is a row-wise backward-error witness. -/
theorem higham21_theorem21_4_rowwise_backward_error_of_qr_assembly_and_entrywise_deltaR
    {m k : ℕ} (fp : FPModel)
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    {etaQR : ℝ} (hetaQR : 0 ≤ etaQR)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      UndetRowwiseBackwardErrorBounded m (m + k) A b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ)))
        (etaQR + gamma fp m * (1 + etaQR)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hmin⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff_of_gammaValid2
      fp Q hQ R_hat b hdiag hupper hvalid hvalid2
  let DeltaA : Fin m → Fin (m + k) → ℝ :=
    fun i j =>
      DeltaA0 i j +
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) i j
  have hqr :
      (fun i j => A i j + DeltaA i j) =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun i j => R_hat i j + DeltaR i j))) := by
    simpa [DeltaA] using
      higham21_theorem21_4_qr_deltaR_assembly_eq
        A DeltaA0 Q R_hat DeltaR hA
  have hminA :
      RectMinNormSolution m (m + k)
        (fun i j => A i j + DeltaA i j) b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ))) := by
    rw [hqr]
    exact hmin
  have hgamma_nonneg : 0 ≤ gamma fp m := gamma_nonneg fp hvalid
  have heta : 0 ≤ etaQR + gamma fp m * (1 + etaQR) := by
    have hone_eta : 0 ≤ 1 + etaQR := by linarith
    exact add_nonneg hetaQR (mul_nonneg hgamma_nonneg hone_eta)
  have hrow : ∀ i : Fin m,
      rectRowNorm2 DeltaA i ≤
        (etaQR + gamma fp m * (1 + etaQR)) * rectRowNorm2 A i := by
    intro i
    simpa [DeltaA] using
      higham21_theorem21_4_common_perturbation_row_bound_of_entrywise_deltaR
        A DeltaA0 Q R_hat DeltaR hgamma_nonneg hQ hA hDeltaA0 hDeltaR i
  exact
    ⟨DeltaR, hDeltaR, hsolve,
      higham21_rowwise_backward_error_bound_witness
        m (m + k) A DeltaA b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ)))
        (etaQR + gamma fp m * (1 + etaQR))
        heta hminA hrow⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    row-wise Q-method handoff from a Chapter 19 QR certificate for `A^T`.
    The tall QR factor is reduced to its top square block using its
    upper-trapezoidal shape, then fed to the assembled row-wise handoff. -/
theorem higham21_theorem21_4_rowwise_backward_error_of_qr_transpose_certificate
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (b : Fin m → ℝ)
    {etaQR : ℝ} (hetaQR : 0 ≤ etaQR)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError (m + k) m
      (finiteTranspose A) Q R_tall etaQR)
    (hdiag : ∀ i : Fin m, R_tall (Fin.castAdd k i) i ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    ∃ DeltaA0 : Fin m → Fin (m + k) → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect (m + k) (m + k) m Q R_tall j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i) ∧
      ∃ DeltaR : Fin m → Fin m → ℝ,
        (∀ i j, |DeltaR i j| ≤
          gamma fp m * |R_tall (Fin.castAdd k i) j|) ∧
        (∀ i,
          matMulVec m
            (matTranspose
              (fun a b => R_tall (Fin.castAdd k a) b + DeltaR a b))
            (fl_forwardSub fp m
              (matTranspose (fun a b => R_tall (Fin.castAdd k a) b)) b) i =
            b i) ∧
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m
                (matTranspose (fun a b => R_tall (Fin.castAdd k a) b)) b)
              (0 : Fin k → ℝ)))
          (etaQR + gamma fp m * (1 + etaQR)) := by
  let R_top : Fin m → Fin m → ℝ :=
    fun i j => R_tall (Fin.castAdd k i) j
  obtain ⟨DeltaA0, hDeltaA0Rep, hDeltaA0Row⟩ :=
    higham21_theorem21_4_qr_transpose_row_perturbation_bound
      A Q R_tall etaQR hqr
  have hRblock :
      R_tall = lsQRTallBlock (k := k) R_top :=
    lsQRTallBlock_of_upper_trapezoidal R_tall hqr.upper
  have hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_top)) := by
    ext i j
    calc
      A i j + DeltaA0 i j =
          matMulRect (m + k) (m + k) m Q R_tall j i := hDeltaA0Rep i j
      _ =
          finiteTranspose
            (matMulRectLeft Q (lsQRTallBlock (k := k) R_top)) i j := by
            simp [finiteTranspose, matMulRect, matMulRectLeft, hRblock]
  have hupperTop : IsUpperTrapezoidal m m R_top :=
    lsQRTallBlock_top_upper_of_upper_trapezoidal R_tall hqr.upper
  obtain ⟨DeltaR, hDeltaR, hsolve, hcert⟩ :=
    higham21_theorem21_4_rowwise_backward_error_of_qr_assembly_and_entrywise_deltaR
      fp A DeltaA0 Q hqr.orth R_top b hdiag hupperTop
      hvalid hvalid2 hetaQR hA hDeltaA0Row
  exact ⟨DeltaA0, hDeltaA0Rep, hDeltaA0Row, DeltaR,
    by simpa [R_top] using hDeltaR,
    by simpa [R_top] using hsolve,
    by simpa [R_top] using hcert⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete Householder-QR specialization of the row-wise Q-method handoff
    for `A^T`.  The remaining diagonal hypothesis is the local nonbreakdown
    condition for the computed top square triangular block. -/
theorem higham21_theorem21_4_rowwise_backward_error_of_householder_qr_transpose
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : ∀ i : Fin m,
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) i ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    ∃ DeltaA0 : Fin m → Fin (m + k) → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect (m + k) (m + k) m
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
          j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤
          H19.Theorem19_4.gamma_tilde fp (m + k) m * rectRowNorm2 A i) ∧
      ∃ DeltaR : Fin m → Fin m → ℝ,
        (∀ i j, |DeltaR i j| ≤
          gamma fp m *
            |fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
              (Fin.castAdd k i) j|) ∧
        (∀ i,
          matMulVec m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b + DeltaR a b))
            (fl_forwardSub fp m
              (matTranspose
                (fun a b =>
                  fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                    (Fin.castAdd k a) b)) b) i =
            b i) ∧
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k)
            (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
            (Fin.append
              (fl_forwardSub fp m
                (matTranspose
                  (fun a b =>
                    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                      (Fin.castAdd k a) b)) b)
              (0 : Fin k → ℝ)))
          (H19.Theorem19_4.gamma_tilde fp (m + k) m +
            gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) := by
  exact
    higham21_theorem21_4_rowwise_backward_error_of_qr_transpose_certificate
      fp A
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
      b
      (H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR)
      (H19.Theorem19_4.householder_qr_backward_error
        fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR)
      hdiag hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    named side condition that the computed top square block of the tall
    Householder QR factor for `A^T` has no zero diagonal pivots.  The printed
    theorem assumes the Q-method triangular solve does not break down; this
    predicate records exactly the local formal obligation still exposed by
    the concrete QR path. -/
def Higham21QMethodTopBlockNonbreakdown
    (m k : ℕ) (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) : Prop :=
  lsTheorem20_4ComputedQRNonbreakdown fp (finiteTranspose A)

theorem Higham21QMethodTopBlockNonbreakdown.of_topBlock_det_ne_zero
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hdet :
      Matrix.det
        ((fun i j =>
          fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
            (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    Higham21QMethodTopBlockNonbreakdown m k fp A := by
  let R_top : Fin m → Fin m → ℝ :=
    fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal fp (m + k) m
      (finiteTranspose A)
  have hupperTop : ∀ i j : Fin m, j.val < i.val → R_top i j = 0 := by
    simpa [R_top] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, R_top i i ≠ 0 :=
    diag_ne_zero_of_upper_triangular_det_ne_zero m R_top hupperTop (by
      simpa [R_top] using hdet)
  simpa [Higham21QMethodTopBlockNonbreakdown,
    lsTheorem20_4ComputedQRNonbreakdown, R_top] using hdiag

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    source-facing concrete domain for the Q-method Householder path.  The
    printed full-row-rank condition for `A` is represented as full column rank
    of `A^T`; the current verified QR API still also exposes the computed
    top-block nonbreakdown condition needed by the triangular solve. -/
def Higham21QMethodFullRowRankComputedQRDomain
    (m k : ℕ) (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) : Prop :=
  lsTheorem20_4FullRankComputedQRDomain fp (finiteTranspose A)

theorem Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown
    {m k : ℕ} {fp : FPModel}
    {A : Fin m → Fin (m + k) → ℝ}
    (h : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    Higham21QMethodTopBlockNonbreakdown m k fp A :=
  lsTheorem20_4FullRankComputedQRDomain.computedQRNonbreakdown fp h

/-- Full row rank of the Q-method source matrix makes its Gram matrix
    A A^T nonsingular. -/
theorem higham21_qmethod_full_row_rank_gram_det_ne_zero
    {m k : ℕ} {fp : FPModel}
    {A : Fin m → Fin (m + k) → ℝ}
    (h : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  have hfull : lsRealRectColRank (finiteTranspose A) = m :=
    lsTheorem20_4FullRankComputedQRDomain.fullRank fp h
  have hinj : Function.Injective (rectMatMulVec (finiteTranspose A)) :=
    lsRealRectColRank_rectMatMulVec_injective_of_colRank_eq_card
      (finiteTranspose A) hfull
  have hdet :
      Matrix.det
        (rectLSGram (finiteTranspose A) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    rectLSGram_det_ne_zero_of_rectMatMulVec_injective
      (finiteTranspose A) hinj
  simpa [rectLSGram, rectGram, finiteTranspose] using hdet

/-- The canonical table A^T(AA^T)^{-1} is a right inverse throughout the
    source-facing full-row-rank Q-method domain. -/
theorem higham21_qmethod_full_row_rank_canonical_right_inverse
    {m k : ℕ} {fp : FPModel}
    {A : Fin m → Fin (m + k) → ℝ}
    (h : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    rectMatMul A (undetAplusOfGramNonsingInv A) = idMatrix m := by
  exact
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero A
      (higham21_qmethod_full_row_rank_gram_det_ne_zero h)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the concrete row-wise coefficient currently proved for the Householder
    Q-method path: the Chapter 19 QR perturbation factor plus the triangular
    solve factor and their first-order product. -/
noncomputable def Higham21QMethodRowwiseCoefficient
    (fp : FPModel) (m k : ℕ) : ℝ :=
  H19.Theorem19_4.gamma_tilde fp (m + k) m +
    gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)

theorem Higham21QMethodRowwiseCoefficient_nonneg
    (fp : FPModel) (m k : ℕ)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hvalid : gammaValid fp m) :
    0 ≤ Higham21QMethodRowwiseCoefficient fp m k := by
  have hqr_nonneg :
      0 ≤ H19.Theorem19_4.gamma_tilde fp (m + k) m :=
    H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hgamma_nonneg : 0 ≤ gamma fp m := gamma_nonneg fp hvalid
  have hone : 0 ≤ 1 + H19.Theorem19_4.gamma_tilde fp (m + k) m := by
    linarith
  simpa [Higham21QMethodRowwiseCoefficient] using
    add_nonneg hqr_nonneg (mul_nonneg hgamma_nonneg hone)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    conservative single-gamma index for the proved row-wise Q-method
    coefficient.  It combines the Chapter 19 QR-on-`A^T` operation index with
    the triangular-solve index from the final back substitution. -/
def Higham21QMethodRowwiseGammaIndex (m k : ℕ) : ℕ :=
  m * householderConstructApplyGammaIndex (m + k) + m

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the proved Q-method row-wise coefficient is absorbed by one larger gamma
    term.  This is the concrete repository analogue of the printed
    dimension-dependent gamma factor in the row perturbation bound. -/
theorem Higham21QMethodRowwiseCoefficient_le_gamma_index
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    Higham21QMethodRowwiseCoefficient fp m k ≤
      gamma fp (Higham21QMethodRowwiseGammaIndex m k) := by
  let q : ℕ := m * householderConstructApplyGammaIndex (m + k)
  have hsum :
      gamma fp q + gamma fp m + gamma fp q * gamma fp m ≤
        gamma fp (q + m) :=
    gamma_sum_le fp q m (by
      simpa [Higham21QMethodRowwiseGammaIndex, q] using hvalid)
  have hcoeff :
      Higham21QMethodRowwiseCoefficient fp m k =
        gamma fp q + gamma fp m + gamma fp q * gamma fp m := by
    simp [Higham21QMethodRowwiseCoefficient, H19.Theorem19_4.gamma_tilde, q]
    ring
  calc
    Higham21QMethodRowwiseCoefficient fp m k =
        gamma fp q + gamma fp m + gamma fp q * gamma fp m := hcoeff
    _ ≤ gamma fp (q + m) := hsum
    _ = gamma fp (Higham21QMethodRowwiseGammaIndex m k) := by
      simp [Higham21QMethodRowwiseGammaIndex, q]

/-- The combined Chapter 21 Q-method gamma index validates the Chapter 19
    Householder QR operation index used in Theorem 21.4. -/
theorem Higham21QMethodRowwiseGammaIndex.validQR
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    gammaValid fp (m * householderConstructApplyGammaIndex (m + k)) :=
  gammaValid_mono fp (by
    dsimp [Higham21QMethodRowwiseGammaIndex]
    exact Nat.le_add_right _ _) hvalid

/-- The combined Chapter 21 Q-method gamma index validates the triangular
    solve index `m` used in Theorem 21.4. -/
theorem Higham21QMethodRowwiseGammaIndex.validM
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    gammaValid fp m :=
  gammaValid_mono fp (by
    dsimp [Higham21QMethodRowwiseGammaIndex]
    exact Nat.le_add_left _ _) hvalid

/-- The combined Chapter 21 Q-method gamma index validates the doubled
    triangular-solve index needed for the nonbreakdown argument. -/
theorem Higham21QMethodRowwiseGammaIndex.valid2M
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    gammaValid fp (2 * m) :=
  gammaValid_mono fp (by
    dsimp [Higham21QMethodRowwiseGammaIndex]
    have hK_ge_one : 1 ≤ householderConstructApplyGammaIndex (m + k) := by
      dsimp [householderConstructApplyGammaIndex]
      omega
    have hm_le_mK :
        m ≤ m * householderConstructApplyGammaIndex (m + k) := by
      simpa using Nat.mul_le_mul_left m hK_ge_one
    calc
      2 * m = m + m := by omega
      _ ≤ m * householderConstructApplyGammaIndex (m + k) + m :=
        Nat.add_le_add_right hm_le_mK m) hvalid

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    source-facing row-wise backward-stability wrapper for any Chapter 19 QR
    certificate of `A^T`.  This projects the detailed `DeltaA0`/`DeltaR`
    witness into the row-wise backward-error predicate used by the theorem. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_qr_transpose_certificate
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (b : Fin m → ℝ)
    {etaQR : ℝ} (hetaQR : 0 ≤ etaQR)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError (m + k) m
      (finiteTranspose A) Q R_tall etaQR)
    (hdiag : ∀ i : Fin m, R_tall (Fin.castAdd k i) i ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k) Q
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose (fun a b => R_tall (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (etaQR + gamma fp m * (1 + etaQR)) := by
  obtain ⟨_, _, _, _, _, _, hcert⟩ :=
    higham21_theorem21_4_rowwise_backward_error_of_qr_transpose_certificate
      fp A Q R_tall b hetaQR hqr hdiag hvalid hvalid2
  exact hcert

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete source-facing row-wise backward-stability theorem for the
    Householder QR panel applied to `A^T`, with the remaining nonbreakdown
    condition named explicitly by `Higham21QMethodTopBlockNonbreakdown`. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_householder_qr_transpose
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : Higham21QMethodTopBlockNonbreakdown m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (H19.Theorem19_4.gamma_tilde fp (m + k) m +
        gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_qr_transpose_certificate
      fp A
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
      b
      (H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR)
      (H19.Theorem19_4.householder_qr_backward_error
        fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR)
      hdiag hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-facing nonbreakdown variant.  A nonzero determinant of the
    computed top square `R` block implies the diagonal nonbreakdown field
    consumed by the concrete Q-method row-wise theorem. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_topBlock_det_ne_zero
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdet :
      Matrix.det
        ((fun i j =>
          fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
            (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (Higham21QMethodRowwiseCoefficient fp m k) := by
  simpa [Higham21QMethodRowwiseCoefficient] using
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_householder_qr_transpose
      fp A b hm hvalidQR
      (Higham21QMethodTopBlockNonbreakdown.of_topBlock_det_ne_zero fp A hdet)
      hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete row-wise backward-stability wrapper under the source-facing
    full-row-rank/computed-QR domain for the Householder QR of `A^T`. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (H19.Theorem19_4.gamma_tilde fp (m + k) m +
        gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_householder_qr_transpose
      fp A b hm hvalidQR
      (Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain)
      hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    same concrete Q-method row-wise theorem with the proved coefficient named
    explicitly for later comparison with the printed asymptotic coefficient. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_coefficient
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (Higham21QMethodRowwiseCoefficient fp m k) := by
  simpa [Higham21QMethodRowwiseCoefficient] using
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain
      fp A b hm hvalidQR hdomain hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    conservative-coefficient handoff.  Any nonnegative source coefficient
    that dominates `Higham21QMethodRowwiseCoefficient` inherits the concrete
    row-wise backward-stability certificate. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_of_coefficient_le
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    {eta : ℝ} (heta : 0 ≤ eta)
    (hcoeff : Higham21QMethodRowwiseCoefficient fp m k ≤ eta) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      eta := by
  exact
    higham21_rowwise_backward_error_bound_mono
      (higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_coefficient
        fp A b hm hvalidQR hdomain hvalid hvalid2)
      heta hcoeff

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    single-gamma row-wise Q-method stability wrapper under the source-facing
    full-row-rank/computed-QR domain. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    (hvalidCoeff : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (gamma fp (Higham21QMethodRowwiseGammaIndex m k)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_of_coefficient_le
      fp A b hm hvalidQR hdomain hvalid hvalid2
      (gamma_nonneg fp hvalidCoeff)
      (Higham21QMethodRowwiseCoefficient_le_gamma_index fp m k hvalidCoeff)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    single-gamma row-wise Q-method stability under the source-facing
    full-row-rank/computed-QR domain.  Validity of the displayed combined
    gamma index discharges every smaller QR and triangular-solve validity
    condition. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma_single_valid
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (gamma fp (Higham21QMethodRowwiseGammaIndex m k)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma
      fp A b hm
      (Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalid)
      hdomain
      (Higham21QMethodRowwiseGammaIndex.validM fp m k hvalid)
      (Higham21QMethodRowwiseGammaIndex.valid2M fp m k hvalid)
      hvalid

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-facing single-gamma Q-method stability theorem.  A single
    validity assumption at the combined index supplies all validity conditions
    used by the QR and triangular-solve certificates. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_topBlock_det_ne_zero_gamma_single_valid
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdet :
      Matrix.det
        ((fun i j =>
          fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
            (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (gamma fp (Higham21QMethodRowwiseGammaIndex m k)) := by
  have hcert :=
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_topBlock_det_ne_zero
      fp A b hm
      (Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalid)
      hdet
      (Higham21QMethodRowwiseGammaIndex.validM fp m k hvalid)
      (Higham21QMethodRowwiseGammaIndex.valid2M fp m k hvalid)
  exact
    higham21_rowwise_backward_error_bound_mono hcert
      (gamma_nonneg fp hvalid)
      (Higham21QMethodRowwiseCoefficient_le_gamma_index fp m k hvalid)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    concrete repository coefficient for the rounded final `Q_hat` action.
    This names the growth radius currently supplied by the Householder QR panel
    accumulated-`Q` theorem, so later source comparisons need only prove a
    scalar domination inequality. -/
noncomputable def Higham21QActionGrowthCoefficient
    (fp : FPModel) (n : ℕ) : ℝ :=
  (n : ℝ) * householderConstructApplyBound fp n *
    (1 + householderConstructApplyBound fp n) ^ n *
    Real.sqrt (n : ℝ)

theorem higham21_eq21_10_q_action_closed_form_coefficient_le_gamma
    (fp : FPModel) (n : ℕ)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex n)) :
    householderQR_QhatClosedFormBound fp n n ≤
      gamma fp (n * householderConstructApplyGammaIndex n) *
        Real.sqrt (n : ℝ) := by
  let K : ℕ := householderConstructApplyGammaIndex n
  have hKvalid : gammaValid fp K := by
    exact gammaValid_mono fp (Nat.le_mul_of_pos_left K hn) hvalid
  have hbase_valid : gammaValid fp (11 * n + 23) := by
    exact gammaValid_mono fp (by
      dsimp [K, householderConstructApplyGammaIndex]
      omega) hKvalid
  have hc0 : 0 ≤ householderConstructApplyBound fp n :=
    householderConstructApplyBound_nonneg fp n hbase_valid
  have hc :
      householderConstructApplyBound fp n ≤ gamma fp K := by
    simpa [K] using householderConstructApplyBound_le_gamma fp n hKvalid
  have hpow :
      (1 + householderConstructApplyBound fp n) ^ n - 1 ≤
        gamma fp (n * K) :=
    one_add_pow_sub_one_le_gamma_mul_of_le_gamma fp n K hc0 hc (by
      simpa [K] using hvalid)
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hmul :=
    mul_le_mul_of_nonneg_right hpow hsqrt
  simpa [householderQR_QhatClosedFormBound, K, mul_assoc] using hmul

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    algebraic difference form of the computed final `Q` action.  If
    `x_hat = (Q + DeltaQ)[y1;0]`, then its difference from the exact
    `Q[y1;0]` action is precisely `DeltaQ [y1;0]`. -/
theorem higham21_eq21_10_q_action_difference_eq_deltaQ
    {m k : ℕ}
    (Q DeltaQ : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hx :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ))) :
    (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) =
      matMulVec (m + k) DeltaQ (Fin.append y1 (0 : Fin k → ℝ)) := by
  ext i
  rw [hx]
  unfold matMulVec
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    the Frobenius perturbation bound for the computed final `Q` action implies
    a Euclidean vector-error bound for the formed solution. -/
theorem higham21_eq21_10_q_action_vec_error_bound
    {m k : ℕ}
    (Q DeltaQ : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (eta : ℝ)
    (hx :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ)))
    (hDeltaQ : frobNorm DeltaQ ≤ eta) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) := by
  let z : Fin (m + k) → ℝ := Fin.append y1 (0 : Fin k → ℝ)
  have hdiff :
      (fun i : Fin (m + k) =>
        x_hat i - matMulVec (m + k) Q z i) =
        matMulVec (m + k) DeltaQ z := by
    simpa [z] using
      higham21_eq21_10_q_action_difference_eq_deltaQ
        Q DeltaQ y1 x_hat hx
  calc
    vecNorm2 (fun i : Fin (m + k) =>
        x_hat i -
          matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i)
        = vecNorm2 (matMulVec (m + k) DeltaQ z) := by
            simpa [z] using congrArg vecNorm2 hdiff
    _ ≤ frobNorm DeltaQ * vecNorm2 z :=
        vecNorm2_matMulVec_le_frobNorm_mul DeltaQ z
    _ ≤ eta * vecNorm2 z :=
        mul_le_mul_of_nonneg_right hDeltaQ (vecNorm2_nonneg z)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    source-shaped final `Q` action bound with the zero-padded coordinate vector
    reduced to the active block norm `‖y1‖₂`. -/
theorem higham21_eq21_10_q_action_vec_error_bound_left_block
    {m k : ℕ}
    (Q DeltaQ : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (eta : ℝ)
    (hx :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ)))
    (hDeltaQ : frobNorm DeltaQ ≤ eta) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 y1 := by
  have hbase :=
    higham21_eq21_10_q_action_vec_error_bound
      Q DeltaQ y1 x_hat eta hx hDeltaQ
  have hzero :
      vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := by
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  rwa [hzero] at hbase

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    consume the QR accumulated-`Q` perturbation certificate directly.  If the
    computed final action uses a rounded `Q_hat` that is certified as
    `Q + DeltaQ` with Frobenius radius `eta`, then the formed-solution error is
    bounded by `eta * ‖y1‖₂`. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_fixed_q_accum_error
    {m k : ℕ}
    (Q Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (eta : ℝ)
    (hQerr :
      HouseholderQRPanelQhatFixedAccumError (m + k) Q Q_hat eta)
    (hx :
      x_hat =
        matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 y1 := by
  rcases hQerr.result with ⟨DeltaQ, hQhat_rep, hDeltaQ⟩
  have hQhat :
      Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhat_rep i j
  have hx' :
      x_hat =
        matMulVec (m + k) (fun i j => Q i j + DeltaQ i j)
          (Fin.append y1 (0 : Fin k → ℝ)) := by
    simpa [hQhat] using hx
  exact
    higham21_eq21_10_q_action_vec_error_bound_left_block
      Q DeltaQ y1 x_hat eta hx' hDeltaQ

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    concrete Householder QR panel specialization of the final `Q` action
    perturbation bridge.  Applied to the QR factorization of `Aᵀ`, the rounded
    accumulated panel `Q_hat` gives the source-shaped `‖y1‖₂` error bound with
    the existing Householder QR growth radius. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat
    {m k : ℕ}
    (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hvalid : gammaValid fp (11 * (m + k) + 23))
    (hx :
      x_hat =
        matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ))) :
    let eta : ℝ :=
      (((m + k : ℕ) : ℝ) * householderConstructApplyBound fp (m + k) *
        (1 + householderConstructApplyBound fp (m + k)) ^ (m + k) *
        Real.sqrt (((m + k : ℕ) : ℝ)))
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 y1 := by
  let eta : ℝ :=
    (((m + k : ℕ) : ℝ) * householderConstructApplyBound fp (m + k) *
      (1 + householderConstructApplyBound fp (m + k)) ^ (m + k) *
      Real.sqrt (((m + k : ℕ) : ℝ)))
  have hQerr :
      HouseholderQRPanelQhatFixedAccumError (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
        eta := by
    simpa [eta] using
      fl_householderQRPanel_Qhat_fixed_Q_growth_accum_error
        fp (m + k) m (m + k) (finiteTranspose A) (le_refl (m + k)) hvalid
  exact
    higham21_eq21_10_q_action_vec_error_bound_of_fixed_q_accum_error
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      y1 x_hat eta hQerr hx

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    sharper closed-form coefficient for the concrete Householder panel
    `Q_hat` action error.  This keeps the repository's closed accumulated
    `Q_hat` recurrence before it is enlarged to the simple growth bound. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_closed_form
    {m k : ℕ}
    (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hvalid : gammaValid fp (11 * (m + k) + 23))
    (hx :
      x_hat =
        matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ))) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      householderQR_QhatClosedFormBound fp (m + k) (m + k) *
        vecNorm2 y1 := by
  have hQerr :
      HouseholderQRPanelQhatFixedAccumError (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
        (householderQR_QhatClosedFormBound fp (m + k) (m + k)) := by
    have hUniform :
        HouseholderQRPanelQhatFixedAccumError (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (householderQR_QhatUniformClosedBound fp (m + k) (m + k)) :=
      fl_householderQRPanel_Qhat_fixed_Q_uniform_accum_error
        fp (m + k) m (m + k) (finiteTranspose A) (le_refl (m + k)) hvalid
    simpa [householderQR_QhatUniformClosedBound_eq_closedForm] using hUniform
  exact
    higham21_eq21_10_q_action_vec_error_bound_of_fixed_q_accum_error
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      y1 x_hat (householderQR_QhatClosedFormBound fp (m + k) (m + k))
      hQerr hx

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    gamma-shaped consequence of the closed-form accumulated `Q_hat` radius.
    This is closer to the printed Lemma 19.3 style, while still using the
    repository's concrete Householder operation-count index. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_gamma
    {m k : ℕ}
    (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hNpos : 0 < m + k)
    (hvalid :
      gammaValid fp
        ((m + k) * householderConstructApplyGammaIndex (m + k)))
    (hx :
      x_hat =
        matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ))) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      (gamma fp ((m + k) * householderConstructApplyGammaIndex (m + k)) *
        Real.sqrt ((m + k : ℕ) : ℝ)) * vecNorm2 y1 := by
  have hKvalid :
      gammaValid fp (householderConstructApplyGammaIndex (m + k)) :=
    gammaValid_mono fp
      (Nat.le_mul_of_pos_left (householderConstructApplyGammaIndex (m + k))
        hNpos) hvalid
  have hQvalid : gammaValid fp (11 * (m + k) + 23) :=
    gammaValid_mono fp (by
      dsimp [householderConstructApplyGammaIndex]
      omega) hKvalid
  have hclosed :=
    higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_closed_form
      fp A y1 x_hat hQvalid hx
  have hcoeff :=
    higham21_eq21_10_q_action_closed_form_coefficient_le_gamma
      fp (m + k) hNpos hvalid
  exact le_trans hclosed
    (mul_le_mul_of_nonneg_right hcoeff (vecNorm2_nonneg y1))

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4 and equation
    (21.10): one operation-count index covering QR of `A^T`, the triangular
    solve, and the rounded accumulated-`Q` action. -/
def Higham21QMethodComputedGammaIndex (m k : ℕ) : ℕ :=
  Higham21QMethodRowwiseGammaIndex m k +
    (m + k) * householderConstructApplyGammaIndex (m + k)

/-- Validity at the full computed Q-method index implies validity at the
    row-wise QR-plus-triangular-solve index. -/
theorem Higham21QMethodComputedGammaIndex.validRowwise
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    gammaValid fp (Higham21QMethodRowwiseGammaIndex m k) :=
  gammaValid_mono fp (by
    dsimp [Higham21QMethodComputedGammaIndex]
    exact Nat.le_add_right _ _) hvalid

/-- Validity at the full computed Q-method index implies validity at the
    rounded accumulated-`Q` action index from equation (21.10). -/
theorem Higham21QMethodComputedGammaIndex.validQAction
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    gammaValid fp
      ((m + k) * householderConstructApplyGammaIndex (m + k)) :=
  gammaValid_mono fp (by
    dsimp [Higham21QMethodComputedGammaIndex]
    exact Nat.le_add_left _ _) hvalid

/-- The row-wise Q-method gamma is dominated by the gamma at the full
    computed operation-count index. -/
theorem Higham21QMethodComputedGammaIndex.rowwiseGamma_le
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    gamma fp (Higham21QMethodRowwiseGammaIndex m k) ≤
      gamma fp (Higham21QMethodComputedGammaIndex m k) :=
  gamma_mono fp (by
    dsimp [Higham21QMethodComputedGammaIndex]
    exact Nat.le_add_right _ _) hvalid

/-- The equation (21.10) accumulated-`Q` gamma is dominated by the gamma at
    the full computed operation-count index. -/
theorem Higham21QMethodComputedGammaIndex.qActionGamma_le
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    gamma fp ((m + k) * householderConstructApplyGammaIndex (m + k)) ≤
      gamma fp (Higham21QMethodComputedGammaIndex m k) :=
  gamma_mono fp (by
    dsimp [Higham21QMethodComputedGammaIndex]
    exact Nat.le_add_left _ _) hvalid

/-- The matrix-level equation-(21.10) radius at the single combined
    operation-count index used by the computed Q method. -/
noncomputable def Higham21QMethodQhatRadius
    (fp : FPModel) (m k : ℕ) : ℝ :=
  gamma fp (Higham21QMethodComputedGammaIndex m k) *
    Real.sqrt ((m + k : ℕ) : ℝ)

/-- Equation (21.10) as a matrix perturbation certificate at the single
    combined Q-method gamma index. -/
theorem higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    HouseholderQRPanelQhatFixedAccumError (m + k)
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      (Higham21QMethodQhatRadius fp m k) := by
  have hNpos : 0 < m + k := by omega
  have hQactionValid :=
    Higham21QMethodComputedGammaIndex.validQAction fp m k hvalid
  have hKvalid :
      gammaValid fp (householderConstructApplyGammaIndex (m + k)) :=
    gammaValid_mono fp
      (Nat.le_mul_of_pos_left
        (householderConstructApplyGammaIndex (m + k)) hNpos)
      hQactionValid
  have hBaseValid : gammaValid fp (11 * (m + k) + 23) :=
    gammaValid_mono fp (by
      dsimp [householderConstructApplyGammaIndex]
      omega) hKvalid
  have hClosed :
      HouseholderQRPanelQhatFixedAccumError (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
        (householderQR_QhatClosedFormBound fp (m + k) (m + k)) := by
    have hUniform :
        HouseholderQRPanelQhatFixedAccumError (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (householderQR_QhatUniformClosedBound fp (m + k) (m + k)) :=
      fl_householderQRPanel_Qhat_fixed_Q_uniform_accum_error
        fp (m + k) m (m + k) (finiteTranspose A) (le_refl (m + k))
        hBaseValid
    simpa [householderQR_QhatUniformClosedBound_eq_closedForm] using hUniform
  have hClosedToAction :
      householderQR_QhatClosedFormBound fp (m + k) (m + k) ≤
        gamma fp
            ((m + k) * householderConstructApplyGammaIndex (m + k)) *
          Real.sqrt ((m + k : ℕ) : ℝ) :=
    higham21_eq21_10_q_action_closed_form_coefficient_le_gamma
      fp (m + k) hNpos hQactionValid
  have hActionToTotal :
      gamma fp
            ((m + k) * householderConstructApplyGammaIndex (m + k)) *
          Real.sqrt ((m + k : ℕ) : ℝ) ≤
        Higham21QMethodQhatRadius fp m k := by
    exact mul_le_mul_of_nonneg_right
      (Higham21QMethodComputedGammaIndex.qActionGamma_le fp m k hvalid)
      (Real.sqrt_nonneg _)
  exact hClosed.mono (le_trans hClosedToAction hActionToTotal)

/-- An orthogonal reference factor turns a Frobenius perturbation radius into
    the conservative infinity-norm smallness bound used by the Chapter 7
    Neumann inverse construction. -/
theorem higham21_infNormBound_abs_orthogonal_transpose_mul
    {n : ℕ}
    (Q DeltaQ : Fin n → Fin n → ℝ) (eta : ℝ)
    (hn : 0 < n)
    (hQ : IsOrthogonal n Q)
    (hDeltaQ : frobNorm DeltaQ ≤ eta) :
    infNormBound n
      (absMatrix n (matMul n (matTranspose Q) DeltaQ))
      ((n : ℝ) * eta) := by
  have heta : 0 ≤ eta := le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hProduct :
      frobNorm (matMul n (matTranspose Q) DeltaQ) ≤ eta := by
    rw [frobNorm_orthogonal_left (matTranspose Q) DeltaQ hQ.transpose]
    exact hDeltaQ
  unfold infNormBound
  rw [infNorm_absMatrix hn (matMul n (matTranspose Q) DeltaQ)]
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |matMul n (matTranspose Q) DeltaQ i j| ≤
          ∑ _j : Fin n, frobNorm (matMul n (matTranspose Q) DeltaQ) :=
        Finset.sum_le_sum (fun j _ =>
          abs_entry_le_frobNorm
            (matMul n (matTranspose Q) DeltaQ) i j)
      _ = (n : ℝ) * frobNorm (matMul n (matTranspose Q) DeltaQ) := by
        simp [Finset.card_univ]
      _ ≤ (n : ℝ) * eta :=
        mul_le_mul_of_nonneg_left hProduct (Nat.cast_nonneg n)
  · exact mul_nonneg (Nat.cast_nonneg n) heta

/-- A sufficiently small accumulated `Q_hat` perturbation has a concrete
    left inverse.  The witness is the Chapter 7 Neumann inverse candidate;
    its infinity-norm bound is retained for the later perturbation estimate. -/
theorem higham21_qhat_left_inverse_of_fixed_accum_error
    {n : ℕ}
    (Q Q_hat : Fin n → Fin n → ℝ) (eta : ℝ)
    (hn : 0 < n)
    (hQerr : HouseholderQRPanelQhatFixedAccumError n Q Q_hat eta)
    (hsmall : (n : ℝ) * eta < 1) :
    ∃ Q_inv : Fin n → Fin n → ℝ,
      matMul n Q_inv Q_hat = idMatrix n ∧
      infNorm Q_inv ≤
        ((n : ℝ) * (1 / (1 - (n : ℝ) * eta))) *
          infNorm (matTranspose Q) := by
  obtain ⟨DeltaQ, hQhat, hDeltaQ⟩ := hQerr.result
  have heta : 0 ≤ eta := le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hscale : 0 ≤ (n : ℝ) * eta :=
    mul_nonneg (Nat.cast_nonneg n) heta
  have hbound :
      infNormBound n
        (absMatrix n (matMul n (matTranspose Q) DeltaQ))
        ((n : ℝ) * eta) :=
    higham21_infNormBound_abs_orthogonal_transpose_mul
      Q DeltaQ eta hn hQerr.orth hDeltaQ
  let Q_inv : Fin n → Fin n → ℝ :=
    ch7Problem711PerturbedInverseCandidate n (matTranspose Q) DeltaQ
  have hRightRaw :
      IsRightInverse n (fun i j => Q i j + DeltaQ i j) Q_inv := by
    dsimp [Q_inv]
    exact
      problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
        n hn Q (matTranspose Q) DeltaQ ((n : ℝ) * eta)
        hscale hsmall hQerr.orth.left_inv hbound
  have hQhatEq : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhat i j
  have hRight : IsRightInverse n Q_hat Q_inv := by
    rw [hQhatEq]
    exact hRightRaw
  have hLeft : IsLeftInverse n Q_hat Q_inv :=
    isLeftInverse_of_isRightInverse Q_hat Q_inv hRight
  have hmul : matMul n Q_inv Q_hat = idMatrix n := by
    ext i j
    exact hLeft i j
  have hInvBound :
      infNorm Q_inv ≤
        ((n : ℝ) * (1 / (1 - (n : ℝ) * eta))) *
          infNorm (matTranspose Q) := by
    dsimp [Q_inv]
    exact
      problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound
        n hn (matTranspose Q) DeltaQ ((n : ℝ) * eta)
        hscale hsmall hbound
  exact ⟨Q_inv, hmul, hInvBound⟩

/-- The source-shaped invertibility consequence of equation (21.10): an
    accumulated factor within Frobenius distance less than one of an
    orthogonal matrix has a left inverse. -/
theorem higham21_qhat_exists_left_inverse_of_fixed_accum_error_lt_one
    {n : ℕ}
    {Q Q_hat : Fin n → Fin n → ℝ}
    {eta : ℝ}
    (hQerr : HouseholderQRPanelQhatFixedAccumError n Q Q_hat eta)
    (heta : eta < 1) :
    ∃ Q_inv : Fin n → Fin n → ℝ,
      matMul n Q_inv Q_hat = idMatrix n := by
  rcases hQerr.result with ⟨DeltaQ, hQhatRep, hDeltaQ⟩
  have hDeltaOp : rectOpNorm2Le DeltaQ eta := by
    apply rectOpNorm2Le_of_frobNormRect_le
    rwa [frobNormRect_eq_frobNorm]
  have hLower : ∀ x : Fin n → ℝ,
      (1 : ℝ) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec Q x) := by
    intro x
    rw [one_mul]
    change vecNorm2 x ≤ vecNorm2 (matMulVec n Q x)
    exact le_of_eq (vecNorm2_orthogonal Q x hQerr.orth).symm
  have hQhatEq : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhatRep i j
  have hInjective : Function.Injective (rectMatMulVec Q_hat) := by
    rw [hQhatEq]
    exact
      rectMatMulVec_injective_of_lower_bound_and_rectOpNorm2Le_lt
        (M := Q) (Delta := DeltaQ) (mu := (1 : ℝ)) (eta := eta)
        hLower hDeltaOp heta
  obtain ⟨Q_inv, hLeft⟩ :=
    ch7_exists_rect_left_inverse_of_rectMatMulVec_injective Q_hat hInjective
  exact ⟨Q_inv, ch7_matMul_of_IsLeftInverse n Q_hat Q_inv hLeft⟩

/-- A matrix within Frobenius distance `eta < 1` of an orthogonal matrix has
    every left inverse bounded by the sharp Neumann radius `1 / (1 - eta)` in
    operator 2-norm. -/
theorem higham21_qhat_inverse_opNorm2Le_of_frobNorm_lt_one
    {n : ℕ}
    (Q Q_hat Q_inv DeltaQ : Fin n → Fin n → ℝ)
    (eta : ℝ)
    (hQ : IsOrthogonal n Q)
    (hQhat : Q_hat = fun i j => Q i j + DeltaQ i j)
    (hDeltaQ : frobNorm DeltaQ ≤ eta)
    (heta : eta < 1)
    (hLeft : IsLeftInverse n Q_hat Q_inv) :
    opNorm2Le Q_inv (1 / (1 - eta)) := by
  have hDeltaOp : opNorm2Le DeltaQ eta :=
    opNorm2Le_of_frobNorm_le DeltaQ hDeltaQ
  have hLower : ∀ x : Fin n → ℝ,
      (1 - eta) * vecNorm2 x ≤ vecNorm2 (matMulVec n Q_hat x) := by
    intro x
    have hQhatAction :
        matMulVec n Q_hat x =
          fun i => matMulVec n Q x i + matMulVec n DeltaQ x i := by
      rw [hQhat]
      exact matMulVec_add_left n Q DeltaQ x
    have hcancel :
        (fun i => matMulVec n Q_hat x i + -matMulVec n DeltaQ x i) =
          matMulVec n Q x := by
      ext i
      rw [congrFun hQhatAction i]
      ring
    have htri :=
      vecNorm2_add_le
        (matMulVec n Q_hat x)
        (fun i => -matMulVec n DeltaQ x i)
    rw [hcancel, vecNorm2_neg] at htri
    have htri' :
        vecNorm2 x ≤
          vecNorm2 (matMulVec n Q_hat x) +
            vecNorm2 (matMulVec n DeltaQ x) := by
      simpa only [vecNorm2_orthogonal Q x hQ] using htri
    calc
      (1 - eta) * vecNorm2 x =
          vecNorm2 x - eta * vecNorm2 x := by ring
      _ ≤ vecNorm2 x - vecNorm2 (matMulVec n DeltaQ x) :=
        sub_le_sub_left (hDeltaOp x) _
      _ ≤ vecNorm2 (matMulVec n Q_hat x) :=
        (sub_le_iff_le_add).2 htri'
  have hRight : IsRightInverse n Q_hat Q_inv :=
    ch7_isRightInverse_of_isLeftInverse hLeft
  intro y
  have hbound := hLower (matMulVec n Q_inv y)
  rw [matMulVec_of_isRightInverse Q_hat Q_inv hRight y] at hbound
  have hden : 0 < 1 - eta := sub_pos.mpr heta
  calc
    vecNorm2 (matMulVec n Q_inv y) =
        ((1 - eta) * vecNorm2 (matMulVec n Q_inv y)) / (1 - eta) := by
          field_simp [ne_of_gt hden]
    _ ≤ vecNorm2 y / (1 - eta) :=
      (div_le_div_iff_of_pos_right hden).2 hbound
    _ = (1 / (1 - eta)) * vecNorm2 y := by
      simp only [div_eq_mul_inv, one_mul, mul_comm]

/-- The equation-(21.10) fixed-accumulation certificate supplies the sharp
    operator bound for any certified left inverse. -/
theorem higham21_qhat_inverse_opNorm2Le_of_fixed_accum_error_lt_one
    {n : ℕ}
    {Q Q_hat Q_inv : Fin n → Fin n → ℝ}
    {eta : ℝ}
    (hQerr : HouseholderQRPanelQhatFixedAccumError n Q Q_hat eta)
    (heta : eta < 1)
    (hleft : matMul n Q_inv Q_hat = idMatrix n) :
    opNorm2Le Q_inv (1 / (1 - eta)) := by
  rcases hQerr.result with ⟨DeltaQ, hQhat, hDeltaQ⟩
  have hQhat' : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhat i j
  have hLeft : IsLeftInverse n Q_hat Q_inv := by
    intro i j
    have hij := congrFun (congrFun hleft i) j
    simpa only [matMul, idMatrix] using hij
  exact
    higham21_qhat_inverse_opNorm2Le_of_frobNorm_lt_one
      Q Q_hat Q_inv DeltaQ eta hQerr.orth hQhat' hDeltaQ heta hLeft

/-- Source-shaped invertibility package for equation (21.10), including the
    operator bound needed to control the inverse-induced perturbation. -/
theorem higham21_qhat_exists_left_inverse_with_opNorm2Le_of_fixed_accum_error_lt_one
    {n : ℕ}
    {Q Q_hat : Fin n → Fin n → ℝ}
    {eta : ℝ}
    (hQerr : HouseholderQRPanelQhatFixedAccumError n Q Q_hat eta)
    (heta : eta < 1) :
    ∃ Q_inv : Fin n → Fin n → ℝ,
      matMul n Q_inv Q_hat = idMatrix n ∧
      opNorm2Le Q_inv (1 / (1 - eta)) := by
  obtain ⟨Q_inv, hleft⟩ :=
    higham21_qhat_exists_left_inverse_of_fixed_accum_error_lt_one hQerr heta
  exact
    ⟨Q_inv, hleft,
      higham21_qhat_inverse_opNorm2Le_of_fixed_accum_error_lt_one
        hQerr heta hleft⟩

/-- The concrete rounded Householder factor in the computed Q method has a
    left inverse whenever its combined-index equation-(21.10) radius is less
    than one. -/
theorem higham21_theorem21_4_qhat_exists_left_inverse_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) := by
  dsimp only
  exact
    higham21_qhat_exists_left_inverse_of_fixed_accum_error_lt_one
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)
      hsmall

/-- The concrete rounded Householder factor has a left inverse with the sharp
    operator bound associated with its combined equation-(21.10) radius. -/
theorem higham21_theorem21_4_qhat_exists_left_inverse_with_opNorm2Le_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) ∧
      opNorm2Le Q_inv
        (1 / (1 - Higham21QMethodQhatRadius fp m k)) := by
  dsimp only
  exact
    higham21_qhat_exists_left_inverse_with_opNorm2Le_of_fixed_accum_error_lt_one
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)
      hsmall

/-- The concrete accumulated Householder factor used by the Q method has a
    certified left inverse under the displayed combined-index smallness
    condition. -/
theorem higham21_theorem21_4_qhat_left_inverse_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall :
      ((m + k : ℕ) : ℝ) * Higham21QMethodQhatRadius fp m k < 1) :
    let Q := fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) ∧
      infNorm Q_inv ≤
        (((m + k : ℕ) : ℝ) *
          (1 / (1 - ((m + k : ℕ) : ℝ) *
            Higham21QMethodQhatRadius fp m k))) *
          infNorm (matTranspose Q) := by
  dsimp only
  exact
    higham21_qhat_left_inverse_of_fixed_accum_error
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      (Higham21QMethodQhatRadius fp m k)
      (by omega)
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)
      hsmall

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4 and equation
    (21.10): computed-Q-method package under one validity condition.  The
    ideal action by the computed orthogonal `Q` has the proved row-wise
    certificate, while the rounded accumulated `Q_hat` action is within the
    displayed equation-(21.10) vector radius.  This keeps the remaining
    row-wise transfer to `Q_hat` explicit rather than assuming it. -/
theorem higham21_theorem21_4_q_method_rowwise_and_qhat_action_of_full_row_rank_computed_qr_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    let Q := fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let y1 :=
      fl_forwardSub fp m
        (matTranspose
          (fun a b =>
            fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
              (Fin.castAdd k a) b)) b
    let z := Fin.append y1 (0 : Fin k → ℝ)
    let x := matMulVec (m + k) Q z
    let x_hat := matMulVec (m + k) Q_hat z
    UndetRowwiseBackwardErrorBounded m (m + k) A b x
        (gamma fp (Higham21QMethodComputedGammaIndex m k)) ∧
      vecNorm2 (fun i : Fin (m + k) => x_hat i - x i) ≤
        (gamma fp (Higham21QMethodComputedGammaIndex m k) *
          Real.sqrt ((m + k : ℕ) : ℝ)) * vecNorm2 y1 := by
  dsimp only
  constructor
  · have hrow :=
      higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma_single_valid
        fp A b hm hdomain
        (Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid)
    exact
      higham21_rowwise_backward_error_bound_mono hrow
        (gamma_nonneg fp hvalid)
        (Higham21QMethodComputedGammaIndex.rowwiseGamma_le fp m k hvalid)
  · have hNpos : 0 < m + k := by omega
    have haction :=
      higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_gamma
        fp A
        (fl_forwardSub fp m
          (matTranspose
            (fun a b =>
              fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                (Fin.castAdd k a) b)) b)
        (matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append
            (fl_forwardSub fp m
              (matTranspose
                (fun a b =>
                  fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                    (Fin.castAdd k a) b)) b)
            (0 : Fin k → ℝ)))
        hNpos
        (Higham21QMethodComputedGammaIndex.validQAction fp m k hvalid)
        rfl
    have hcoeff :
        gamma fp ((m + k) * householderConstructApplyGammaIndex (m + k)) *
            Real.sqrt ((m + k : ℕ) : ℝ) ≤
          gamma fp (Higham21QMethodComputedGammaIndex m k) *
            Real.sqrt ((m + k : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Higham21QMethodComputedGammaIndex.qActionGamma_le fp m k hvalid)
        (Real.sqrt_nonneg _)
    exact le_trans haction
      (mul_le_mul_of_nonneg_right hcoeff
        (vecNorm2_nonneg
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)))

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    transpose action through a not-necessarily-orthogonal factor with a
    supplied left inverse.  This is the exact algebra behind the first
    perturbed system in the proof. -/
theorem higham21_matMulRectLeft_transpose_action_of_left_inverse
    {m n : ℕ}
    (Q_inv Q_hat : Fin m → Fin m → ℝ)
    (B : Fin m → Fin n → ℝ)
    (z : Fin m → ℝ)
    (hleft : matMul m Q_inv Q_hat = idMatrix m) :
    rectMatMulVec
        (finiteTranspose (matMulRectLeft (matTranspose Q_inv) B))
        (matMulVec m Q_hat z) =
      fun j : Fin n => ∑ i : Fin m, B i j * z i := by
  ext j
  unfold rectMatMulVec finiteTranspose matMulRectLeft matTranspose matMulVec
  calc
    ∑ i : Fin m, (∑ k : Fin m, Q_inv k i * B k j) *
        (∑ l : Fin m, Q_hat i l * z l)
        = ∑ i : Fin m, ∑ k : Fin m, ∑ l : Fin m,
            (Q_inv k i * B k j) * (Q_hat i l * z l) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin m, ∑ l : Fin m, ∑ i : Fin m,
          (Q_inv k i * B k j) * (Q_hat i l * z l) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (∑ i : Fin m, Q_inv k i * Q_hat i l) * (B k j * z l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (if k = l then 1 else 0) * (B k j * z l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            have hkl := congrFun (congrFun hleft k) l
            have hkl' :
                (∑ i : Fin m, Q_inv k i * Q_hat i l) =
                  if k = l then 1 else 0 := by
              simpa [matMul, idMatrix] using hkl
            rw [hkl']
    _ = ∑ k : Fin m, B k j * z k := by
            simp [Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    block-coordinate specialization of the left-inverse transpose action.
    It reduces the first perturbed system to the triangular equation
    `(R_plus)^T y1 = b`. -/
theorem higham21_theorem21_4_qhat_first_system_block_action
    {m k : ℕ}
    (Q_inv Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ)
    (y1 : Fin m → ℝ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k)) :
    rectMatMulVec
        (finiteTranspose
          (matMulRectLeft (matTranspose Q_inv)
            (lsQRTallBlock (k := k) R_plus)))
        (matMulVec (m + k) Q_hat
          (Fin.append y1 (0 : Fin k → ℝ))) =
      fun j : Fin m => ∑ i : Fin m, R_plus i j * y1 i := by
  calc
    rectMatMulVec
        (finiteTranspose
          (matMulRectLeft (matTranspose Q_inv)
            (lsQRTallBlock (k := k) R_plus)))
        (matMulVec (m + k) Q_hat
          (Fin.append y1 (0 : Fin k → ℝ))) =
      (fun j : Fin m =>
        ∑ i : Fin (m + k),
          lsQRTallBlock (k := k) R_plus i j *
            Fin.append y1 (0 : Fin k → ℝ) i) :=
      higham21_matMulRectLeft_transpose_action_of_left_inverse
        Q_inv Q_hat (lsQRTallBlock (k := k) R_plus)
        (Fin.append y1 (0 : Fin k → ℝ)) hleft
    _ = fun j : Fin m => ∑ i : Fin m, R_plus i j * y1 i :=
      higham21_eq21_2_qr_block_transpose_coordinates
        R_plus y1 (0 : Fin k → ℝ)

/-- The first source perturbation in Higham's Theorem 21.4 proof.  Its
    perturbed matrix is `[R_plus^T,0] Q_hat^{-1}`, represented by transposing
    `(Q_hat^{-1})^T [R_plus;0]`. -/
noncomputable def Higham21QMethodDeltaA1
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ) :
    Fin m → Fin (m + k) → ℝ :=
  fun i j =>
    finiteTranspose
        (matMulRectLeft (matTranspose Q_inv)
          (lsQRTallBlock (k := k) R_plus)) i j - A i j

theorem Higham21QMethodDeltaA1.add_eq
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ) :
    (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j) =
      finiteTranspose
        (matMulRectLeft (matTranspose Q_inv)
          (lsQRTallBlock (k := k) R_plus)) := by
  ext i j
  simp [Higham21QMethodDeltaA1]

/-- The constructed `DeltaA1` makes the rounded `Q_hat` action solve the
    first perturbed system whenever `Q_inv` is a left inverse and the
    perturbed triangular equation holds. -/
theorem Higham21QMethodDeltaA1.system_eq
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k))
    (htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j)
    (hx : x_hat = matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))) :
    rectMatMulVec
        (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
        x_hat = b := by
  rw [Higham21QMethodDeltaA1.add_eq A Q_inv R_plus, hx]
  exact
    (higham21_theorem21_4_qhat_first_system_block_action
      Q_inv Q_hat R_plus y1 hleft).trans (funext htri)

set_option maxHeartbeats 800000
/-- The first perturbation in Higham's rounded-`Q` proof is bounded by the
    ideal QR-plus-triangular perturbation and the defect between
    `(Q_hat^{-1})^T` and the exact orthogonal factor. -/
theorem Higham21QMethodDeltaA1.row_bound_of_inverse_defect
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR etaInv : ℝ}
    (hetaR : 0 ≤ etaR)
    (hetaInv : 0 ≤ etaInv)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (hDefect :
      opNorm2Le (fun a b => Q_inv b a - Q a b) etaInv) :
    ∀ i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA1 A Q_inv
            (fun a b => R_hat a b + DeltaR a b)) i ≤
        ((etaQR + etaR * (1 + etaQR)) +
          etaInv * (1 + (etaQR + etaR * (1 + etaQR)))) *
          rectRowNorm2 A i := by
  let etaBase : ℝ := etaQR + etaR * (1 + etaQR)
  let R_plus : Fin m → Fin m → ℝ :=
    fun i j => R_hat i j + DeltaR i j
  let DeltaBase : Fin m → Fin (m + k) → ℝ :=
    fun i j =>
      DeltaA0 i j +
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) i j
  let Defect : Fin (m + k) → Fin (m + k) → ℝ :=
    fun a b => Q_inv b a - Q a b
  let Correction : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose
      (matMulRectLeft Defect (lsQRTallBlock (k := k) R_plus))
  have hBase : ∀ i : Fin m,
      rectRowNorm2 DeltaBase i ≤ etaBase * rectRowNorm2 A i := by
    intro i
    simpa [DeltaBase, etaBase] using
      higham21_theorem21_4_common_perturbation_row_bound_of_entrywise_deltaR
        A DeltaA0 Q R_hat DeltaR hetaR hQ hA hDeltaA0 hDeltaR i
  have hAssembly :
      (fun i j => A i j + DeltaBase i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_plus)) := by
    simpa [DeltaBase, R_plus] using
      higham21_theorem21_4_qr_deltaR_assembly_eq
        A DeltaA0 Q R_hat DeltaR hA
  have hAself : ∀ i : Fin m,
      rectRowNorm2 A i ≤ (1 : ℝ) * rectRowNorm2 A i := by
    intro i
    rw [one_mul]
  have hAssembledBound : ∀ i : Fin m,
      rectRowNorm2 (fun r c => A r c + DeltaBase r c) i ≤
        (1 + etaBase) * rectRowNorm2 A i := by
    intro i
    exact higham21_rectRowNorm2_add_le_of_row_bounds
      A DeltaBase A hAself hBase i
  have hRplusColumn : ∀ i : Fin m,
      columnFrob R_plus i ≤ (1 + etaBase) * rectRowNorm2 A i := by
    intro i
    have hnorm :=
      higham21_theorem21_4_assembled_qr_row_norm_eq_R_columnFrob
        A DeltaBase Q R_plus hQ hAssembly i
    rw [← hnorm]
    exact hAssembledBound i
  have hDefect' : opNorm2Le Defect etaInv := by
    simpa [Defect] using hDefect
  have hDefectRect : rectOpNorm2Le Defect etaInv :=
    rectOpNorm2Le_of_opNorm2Le_square Defect hDefect'
  have hCorrectionTranspose :
      finiteTranspose Correction =
        matMulRectLeft Defect (lsQRTallBlock (k := k) R_plus) := by
    ext i j
    rfl
  have hCorrection : ∀ i : Fin m,
      rectRowNorm2 Correction i ≤
        (etaInv * (1 + etaBase)) * rectRowNorm2 A i := by
    intro i
    calc
      rectRowNorm2 Correction i = columnFrob (finiteTranspose Correction) i :=
        higham21_rectRowNorm2_eq_columnFrob_finiteTranspose Correction i
      _ = columnFrob
          (matMulRectLeft Defect (lsQRTallBlock (k := k) R_plus)) i := by
        rw [hCorrectionTranspose]
      _ ≤ etaInv * columnFrob (lsQRTallBlock (k := k) R_plus) i := by
        exact
          columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
            Defect (lsQRTallBlock (k := k) R_plus) hDefectRect i
      _ = etaInv * columnFrob R_plus i := by
        rw [higham21_columnFrob_lsQRTallBlock]
      _ ≤ etaInv * ((1 + etaBase) * rectRowNorm2 A i) :=
        mul_le_mul_of_nonneg_left (hRplusColumn i) hetaInv
      _ = (etaInv * (1 + etaBase)) * rectRowNorm2 A i := by ring
  have hTransposeQinv :
      matTranspose Q_inv = fun a b => Q a b + Defect a b := by
    ext a b
    dsimp [Defect, matTranspose]
    ring
  have hDeltaA1Rep :
      Higham21QMethodDeltaA1 A Q_inv R_plus =
        fun i j => DeltaBase i j + Correction i j := by
    ext i j
    change
      finiteTranspose
          (matMulRectLeft (matTranspose Q_inv)
            (lsQRTallBlock (k := k) R_plus)) i j - A i j =
        DeltaBase i j + Correction i j
    rw [hTransposeQinv, matMulRectLeft_add_left]
    have hAssemblyEntry := congrFun (congrFun hAssembly i) j
    dsimp [Correction, finiteTranspose] at hAssemblyEntry ⊢
    linarith
  intro i
  rw [hDeltaA1Rep]
  simpa [etaBase] using
    higham21_rectRowNorm2_add_le_of_row_bounds
      DeltaBase Correction A hBase hCorrection i

/-- The inverse-transpose defect in Higham's first perturbed system is the
    product of the exact inverse, the accumulated `Q_hat` perturbation, and
    the orthogonal reference factor. -/
theorem higham21_qhat_inverse_transpose_defect_opNorm2Le_of_inverse_bound
    {n : ℕ}
    (Q Q_hat Q_inv DeltaQ : Fin n → Fin n → ℝ)
    (etaQ qinv : ℝ)
    (hQ : IsOrthogonal n Q)
    (hQhat : Q_hat = fun i j => Q i j + DeltaQ i j)
    (hDeltaQ : frobNorm DeltaQ ≤ etaQ)
    (hleft : matMul n Q_inv Q_hat = idMatrix n)
    (hqinv : 0 ≤ qinv)
    (hQinvOp : opNorm2Le Q_inv qinv) :
    opNorm2Le (fun a b => Q_inv b a - Q a b) (qinv * etaQ) := by
  have hetaQ : 0 ≤ etaQ :=
    le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hPertLeft :
      IsLeftInverse n (fun i j => Q i j + DeltaQ i j) Q_inv := by
    intro i j
    have hij := congrFun (congrFun hleft i) j
    rw [hQhat] at hij
    simpa only [matMul, idMatrix] using hij
  have hPertRight :
      IsRightInverse n (fun i j => Q i j + DeltaQ i j) Q_inv :=
    ch7_isRightInverse_of_isLeftInverse hPertLeft
  have hDefectEq :
      (fun a b => Q_inv a b - Q b a) =
        (fun a b =>
          -matMul n (matMul n (matTranspose Q) DeltaQ) Q_inv a b) := by
    ext a b
    have hab :=
      ch7_inversePerturbation_decomposition
        n Q (matTranspose Q) DeltaQ Q_inv
        hQ.left_inv hPertRight a b
    change
      Q_inv a b +
          matMul n (matMul n (matTranspose Q) DeltaQ) Q_inv a b =
        Q b a at hab
    linarith
  have hDeltaQOp : opNorm2Le DeltaQ etaQ :=
    opNorm2Le_of_frobNorm_le DeltaQ hDeltaQ
  have hQtDeltaQProduct :
      opNorm2Le (matMul n (matTranspose Q) DeltaQ) ((1 : ℝ) * etaQ) :=
    opNorm2Le_matMul_square_of_bounds
      (matTranspose Q) DeltaQ (by norm_num)
      hQ.transpose_opNorm2Le_one hDeltaQOp
  have hQtDeltaQ :
      opNorm2Le (matMul n (matTranspose Q) DeltaQ) etaQ := by
    simpa only [one_mul] using hQtDeltaQProduct
  have hProduct :
      opNorm2Le
        (matMul n (matMul n (matTranspose Q) DeltaQ) Q_inv)
        (etaQ * qinv) :=
    opNorm2Le_matMul_square_of_bounds
      (matMul n (matTranspose Q) DeltaQ) Q_inv
      hetaQ hQtDeltaQ hQinvOp
  have hRaw :
      opNorm2Le (fun a b => Q_inv a b - Q b a) (qinv * etaQ) := by
    rw [hDefectEq]
    simpa only [mul_comm] using (opNorm2Le_neg hProduct)
  have hRawTranspose :
      opNorm2Le
        (matTranspose (fun a b => Q_inv a b - Q b a))
        (qinv * etaQ) :=
    opNorm2Le_transpose
      (fun a b => Q_inv a b - Q b a)
      (mul_nonneg hqinv hetaQ) hRaw
  simpa only [matTranspose] using hRawTranspose

/-- Frobenius-norm specialization of the inverse-transpose defect bound. -/
theorem higham21_qhat_inverse_transpose_defect_opNorm2Le
    {n : ℕ}
    (Q Q_hat Q_inv DeltaQ : Fin n → Fin n → ℝ)
    (etaQ qinv : ℝ)
    (hQ : IsOrthogonal n Q)
    (hQhat : Q_hat = fun i j => Q i j + DeltaQ i j)
    (hDeltaQ : frobNorm DeltaQ ≤ etaQ)
    (hleft : matMul n Q_inv Q_hat = idMatrix n)
    (hQinv : frobNorm Q_inv ≤ qinv) :
    opNorm2Le (fun a b => Q_inv b a - Q a b) (qinv * etaQ) :=
  higham21_qhat_inverse_transpose_defect_opNorm2Le_of_inverse_bound
    Q Q_hat Q_inv DeltaQ etaQ qinv hQ hQhat hDeltaQ hleft
    (le_trans (frobNorm_nonneg Q_inv) hQinv)
    (opNorm2Le_of_frobNorm_le Q_inv hQinv)

/-- QR, triangular-solve, accumulated-`Q`, and inverse certificates combine
    into the row-relative bound for Higham's first perturbed system. -/
theorem Higham21QMethodDeltaA1.row_bound_of_qr_transpose_certificate
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q Q_hat Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR etaQ qinv : ℝ}
    (hRblock : R_tall = lsQRTallBlock (k := k) R_hat)
    (hetaR : 0 ≤ etaR)
    (hqinv : 0 ≤ qinv)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A) Q R_tall etaQR)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (hQerr : HouseholderQRPanelQhatFixedAccumError
      (m + k) Q Q_hat etaQ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k))
    (hQinvOp : opNorm2Le Q_inv qinv) :
    ∀ i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA1 A Q_inv
            (fun a b => R_hat a b + DeltaR a b)) i ≤
        ((etaQR + etaR * (1 + etaQR)) +
          (qinv * etaQ) *
            (1 + (etaQR + etaR * (1 + etaQR)))) *
          rectRowNorm2 A i := by
  subst R_tall
  obtain ⟨DeltaA0, hA0, hDeltaA0⟩ :=
    higham21_theorem21_4_qr_transpose_row_perturbation_bound
      A Q (lsQRTallBlock (k := k) R_hat) etaQR hqr
  have hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)) := by
    ext i j
    simpa [finiteTranspose, matMulRectLeft, matMulRect] using hA0 i j
  rcases hQerr.result with ⟨DeltaQ, hQhatRep, hDeltaQ⟩
  have hQhatEq : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhatRep i j
  have hetaQ : 0 ≤ etaQ :=
    le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hDefect :
      opNorm2Le (fun a b => Q_inv b a - Q a b) (qinv * etaQ) :=
    higham21_qhat_inverse_transpose_defect_opNorm2Le_of_inverse_bound
      Q Q_hat Q_inv DeltaQ etaQ qinv hqr.orth hQhatEq hDeltaQ hleft
      hqinv hQinvOp
  exact
    Higham21QMethodDeltaA1.row_bound_of_inverse_defect
      A DeltaA0 Q Q_inv R_hat DeltaR hetaR
      (mul_nonneg hqinv hetaQ) hqr.orth hA hDeltaA0 hDeltaR hDefect

/-- Transposing a rectangular product and applying it to a vector is the
    same as applying the square left factor after the rectangular action. -/
theorem higham21_rectTransposeMulVec_finiteTranspose_matMulRectLeft
    {m n : ℕ}
    (Q : Fin n → Fin n → ℝ)
    (B : Fin n → Fin m → ℝ)
    (y : Fin m → ℝ) :
    rectTransposeMulVec (finiteTranspose (matMulRectLeft Q B)) y =
      matMulVec n Q (rectMatMulVec B y) := by
  ext j
  have h := congrFun (rectMatMulVec_matMulRectLeft Q B y) j
  simpa [rectTransposeMulVec, finiteTranspose] using h

/-- Block specialization of the transpose-range identity for the concrete
    rounded `Q_hat` factor. -/
theorem higham21_theorem21_4_qhat_tall_block_transpose_action
    {m k : ℕ}
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (y : Fin m → ℝ) :
    rectTransposeMulVec
        (finiteTranspose
          (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat))) y =
      matMulVec (m + k) Q_hat
        (Fin.append (rectMatMulVec R_hat y) (0 : Fin k → ℝ)) := by
  rw [higham21_rectTransposeMulVec_finiteTranspose_matMulRectLeft]
  rw [higham21_eq21_1_qr_transpose_block_mulVec]

/-- The second source perturbation in Higham's Theorem 21.4 proof, defined
    by the concrete rounded product `Q_hat [R_hat;0]`. -/
noncomputable def Higham21QMethodDeltaA2
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ) :
    Fin m → Fin (m + k) → ℝ :=
  fun i j =>
    finiteTranspose
        (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat)) i j - A i j

theorem Higham21QMethodDeltaA2.add_eq
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ) :
    (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) =
      finiteTranspose
        (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat)) := by
  ext i j
  simp [Higham21QMethodDeltaA2]

/-- If `R_hat y = y1`, the concrete rounded action `Q_hat [y1;0]` lies in
    the transpose range of `A + DeltaA2`, exactly as required by the second
    perturbed system in Higham's proof. -/
theorem Higham21QMethodDeltaA2.transpose_representation
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (y y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hRy : rectMatMulVec R_hat y = y1)
    (hx : x_hat = matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))) :
    x_hat =
      rectTransposeMulVec
        (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) y := by
  rw [Higham21QMethodDeltaA2.add_eq A Q_hat R_hat]
  calc
    x_hat = matMulVec (m + k) Q_hat
        (Fin.append y1 (0 : Fin k → ℝ)) := hx
    _ = matMulVec (m + k) Q_hat
        (Fin.append (rectMatMulVec R_hat y) (0 : Fin k → ℝ)) := by rw [hRy]
    _ = rectTransposeMulVec
        (finiteTranspose
          (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat))) y :=
      (higham21_theorem21_4_qhat_tall_block_transpose_action
        Q_hat R_hat y).symm

set_option maxHeartbeats 800000
/-- The second perturbation in Higham's rounded-`Q` proof inherits a
    row-relative bound from the QR residual and the accumulated `Q_hat`
    perturbation. -/
theorem Higham21QMethodDeltaA2.row_bound_of_qr_transpose_certificate
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    {etaQR etaQ : ℝ}
    (hRblock : R_tall = lsQRTallBlock (k := k) R_hat)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A) Q R_tall etaQR)
    (hQerr : HouseholderQRPanelQhatFixedAccumError
      (m + k) Q Q_hat etaQ) :
    ∀ i : Fin m,
      rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
        (etaQR + etaQ * (1 + etaQR)) * rectRowNorm2 A i := by
  subst R_tall
  rcases hqr.result with ⟨DeltaAT, hQR, hDeltaAT⟩
  rcases hQerr.result with ⟨DeltaQ, hQhatRep, hDeltaQ⟩
  let B : Fin (m + k) → Fin m → ℝ := lsQRTallBlock (k := k) R_hat
  let E : Fin (m + k) → Fin m → ℝ := matMulRectLeft DeltaQ B
  have hQhatEq : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhatRep i j
  have hQRfun :
      (fun i j => finiteTranspose A i j + DeltaAT i j) =
        matMulRectLeft Q B := by
    ext i j
    simpa [B, matMulRectLeft, matMulRect] using hQR i j
  have hetaQ : 0 ≤ etaQ :=
    le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hRcol : ∀ i : Fin m,
      columnFrob B i ≤
        (1 + etaQR) * columnFrob (finiteTranspose A) i := by
    intro i
    calc
      columnFrob B i = columnFrob (matMulRectLeft Q B) i :=
        (higham21_columnFrob_matMulRectLeft_orthogonal
          Q B hqr.orth i).symm
      _ ≤ columnFrob (finiteTranspose A) i + columnFrob DeltaAT i := by
        rw [← hQRfun]
        exact columnFrob_add_le _ _ i
      _ ≤ columnFrob (finiteTranspose A) i +
          etaQR * columnFrob (finiteTranspose A) i :=
        add_le_add (le_refl (columnFrob (finiteTranspose A) i))
          (hDeltaAT i)
      _ = (1 + etaQR) * columnFrob (finiteTranspose A) i := by ring
  have hEcol : ∀ i : Fin m,
      columnFrob E i ≤
        etaQ * (1 + etaQR) * columnFrob (finiteTranspose A) i := by
    intro i
    calc
      columnFrob E i ≤ frobNorm DeltaQ * columnFrob B i :=
        columnFrob_matMulVec_le_frobNorm_mul_columnFrob
          E B DeltaQ i (fun _ => rfl)
      _ ≤ etaQ * columnFrob B i :=
        mul_le_mul_of_nonneg_right hDeltaQ (columnFrob_nonneg B i)
      _ ≤ etaQ * ((1 + etaQR) *
          columnFrob (finiteTranspose A) i) :=
        mul_le_mul_of_nonneg_left (hRcol i) hetaQ
      _ = etaQ * (1 + etaQR) *
          columnFrob (finiteTranspose A) i := by ring
  have hResidual :
      finiteTranspose (Higham21QMethodDeltaA2 A Q_hat R_hat) =
        fun i j => DeltaAT i j + E i j := by
    ext i j
    change matMulRectLeft Q_hat B i j - finiteTranspose A i j =
      DeltaAT i j + E i j
    rw [hQhatEq, matMulRectLeft_add_left]
    have hQRentry := congrFun (congrFun hQRfun i) j
    dsimp [E]
    linarith
  intro i
  calc
    rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i =
        columnFrob
          (finiteTranspose (Higham21QMethodDeltaA2 A Q_hat R_hat)) i :=
      higham21_rectRowNorm2_eq_columnFrob_finiteTranspose _ i
    _ ≤ columnFrob DeltaAT i + columnFrob E i := by
      rw [hResidual]
      exact columnFrob_add_le _ _ i
    _ ≤ etaQR * columnFrob (finiteTranspose A) i +
        etaQ * (1 + etaQR) * columnFrob (finiteTranspose A) i :=
      add_le_add (hDeltaAT i) (hEcol i)
    _ = (etaQR + etaQ * (1 + etaQR)) * rectRowNorm2 A i := by
      rw [higham21_rectRowNorm2_eq_columnFrob_finiteTranspose A i]
      ring

/-- Concrete Householder specialization of the second rounded-`Q`
    perturbation bound under the single computed Q-method gamma validity
    condition. -/
theorem Higham21QMethodDeltaA2.row_bound_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    ∀ i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA2 A
            (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
            (fun a b =>
              fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                (Fin.castAdd k a) b)) i ≤
        (H19.Theorem19_4.gamma_tilde fp (m + k) m +
          Higham21QMethodQhatRadius fp m k *
            (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) *
          rectRowNorm2 A i := by
  have hvalidQR :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k
      (Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid)
  have hqr :=
    H19.Theorem19_4.householder_qr_backward_error
      fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR
  have hRblock :=
    lsQRTallBlock_of_upper_trapezoidal
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) hqr.upper
  exact
    Higham21QMethodDeltaA2.row_bound_of_qr_transpose_certificate
      A
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
      (fun a b =>
        fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
          (Fin.castAdd k a) b)
      hRblock hqr
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the two exact perturbed-system equations for the rounded `Q_hat` output.
    This is the algebraic input to Lemma 21.2; perturbation-size and
    smallness bounds remain separate obligations. -/
theorem higham21_theorem21_4_qhat_two_perturbed_systems
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus R_hat : Fin m → Fin m → ℝ)
    (b y1 y : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k))
    (htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j)
    (hRy : rectMatMulVec R_hat y = y1)
    (hx : x_hat = matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))) :
    rectMatMulVec
        (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
        x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) y := by
  constructor
  · exact Higham21QMethodDeltaA1.system_eq
      A Q_inv Q_hat R_plus b y1 x_hat hleft htri hx
  · exact Higham21QMethodDeltaA2.transpose_representation
      A Q_hat R_hat y y1 x_hat hRy hx

/-- Theorem 21.4's two perturbed systems for the concrete rounded
    Householder `Q_hat`.  Equation (21.10) and the single combined gamma
    condition now construct the inverse internally. -/
theorem higham21_theorem21_4_computed_qhat_two_perturbed_systems
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (R_plus R_hat : Fin m → Fin m → ℝ)
    (b y1 y : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1)
    (htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j)
    (hRy : rectMatMulVec R_hat y = y1)
    (hx : x_hat = matMulVec (m + k)
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      (Fin.append y1 (0 : Fin k → ℝ))) :
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      rectMatMulVec
          (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
          x_hat = b ∧
        x_hat =
          rectTransposeMulVec
            (fun i j => A i j +
              Higham21QMethodDeltaA2 A
                (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
                R_hat i j) y := by
  obtain ⟨Q_inv, hleft⟩ :=
    higham21_theorem21_4_qhat_exists_left_inverse_of_computed_gamma
      fp A hm hvalid hsmall
  exact ⟨Q_inv,
    higham21_theorem21_4_qhat_two_perturbed_systems
      A Q_inv
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      R_plus R_hat b y1 y x_hat hleft htri hRy hx⟩

/-- Full-row-rank computed-QR data makes the computed top `R` block
    surjective.  This supplies the exact coordinate used in the second
    perturbed system of Theorem 21.4. -/
theorem higham21_computed_top_block_exists_exact_preimage
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (y1 : Fin m → ℝ) :
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    ∃ y : Fin m → ℝ, rectMatMulVec R_hat y = y1 := by
  dsimp only
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal
      fp (m + k) m (finiteTranspose A)
  have hupper : IsUpperTrapezoidal m m R_hat := by
    simpa [R_hat] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, R_hat i i ≠ 0 := by
    simpa [R_hat, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  have hdet : Matrix.det (R_hat : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero m R_hat hupper hdiag
  have hInverse : IsInverse m R_hat (nonsingInv m R_hat) :=
    isInverse_nonsingInv_of_det_ne_zero m R_hat hdet
  refine ⟨matMulVec m (nonsingInv m R_hat) y1, ?_⟩
  change matMulVec m R_hat (matMulVec m (nonsingInv m R_hat) y1) = y1
  exact matMulVec_of_isRightInverse R_hat (nonsingInv m R_hat) hInverse.2 y1

/-- The concrete rounded Q-method output satisfies both perturbed systems in
    Higham's Theorem 21.4 with every algebraic witness constructed from the
    implementation-backed QR domain and the single combined gamma validity
    condition. -/
theorem higham21_theorem21_4_computed_qhat_two_perturbed_systems_of_full_row_rank_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    ∃ (DeltaR : Fin m → Fin m → ℝ)
        (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
        (y : Fin m → ℝ),
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y := by
  dsimp only
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal
      fp (m + k) m (finiteTranspose A)
  have hupper : IsUpperTrapezoidal m m R_hat := by
    simpa [R_hat] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, R_hat i i ≠ 0 := by
    simpa [R_hat, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  have hvalidRowwise :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid
  have hvalidM :=
    Higham21QMethodRowwiseGammaIndex.validM fp m k hvalidRowwise
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag hupper hvalidM
  let R_plus : Fin m → Fin m → ℝ :=
    fun i j => R_hat i j + DeltaR i j
  have htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j := by
    intro j
    simpa [R_plus, y1, matMulVec, matTranspose] using hsolve j
  obtain ⟨y, hRyRaw⟩ :=
    higham21_computed_top_block_exists_exact_preimage fp A hdomain y1
  have hRy : rectMatMulVec R_hat y = y1 := by
    simpa [R_hat] using hRyRaw
  obtain ⟨Q_inv, hfirst, hsecond⟩ :=
    higham21_theorem21_4_computed_qhat_two_perturbed_systems
      fp A R_plus R_hat b y1 y x_hat hm hvalid hsmall htri hRy (by
        rfl)
  refine ⟨DeltaR, Q_inv, y, ?_, ?_, ?_⟩
  · simpa [R_hat] using hDeltaR
  · simpa [R_hat, R_plus, Q_hat, y1, x_hat] using hfirst
  · simpa [R_hat, Q_hat, y1, x_hat] using hsecond

/-- Implementation-backed rounded-Q witness package with a supplied inverse
    operator bound.  The same `DeltaR`, inverse, and range coordinate satisfy
    both exact systems and both row-relative perturbation estimates. -/
theorem higham21_theorem21_4_computed_qhat_perturbations_of_inverse_bound
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (qinv : ℝ) (hqinv : 0 ≤ qinv)
    (hleft :
      matMul (m + k) Q_inv
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)) =
        idMatrix (m + k))
    (hQinvOp : opNorm2Le Q_inv qinv) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let etaR := gamma fp m
    let etaQ := Higham21QMethodQhatRadius fp m k
    ∃ (DeltaR : Fin m → Fin m → ℝ) (y : Fin m → ℝ),
      (∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y ∧
      (∀ i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i ≤
          ((etaQR + etaR * (1 + etaQR)) +
            (qinv * etaQ) *
              (1 + (etaQR + etaR * (1 + etaQR)))) *
            rectRowNorm2 A i) ∧
      (∀ i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
          (etaQR + etaQ * (1 + etaQR)) * rectRowNorm2 A i) := by
  dsimp only
  let Q : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_tall : Fin (m + k) → Fin m → ℝ :=
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    R_tall (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let etaQR : ℝ := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaR : ℝ := gamma fp m
  let etaQ : ℝ := Higham21QMethodQhatRadius fp m k
  have hvalidRowwise :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid
  have hvalidQR :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalidRowwise
  have hvalidM :=
    Higham21QMethodRowwiseGammaIndex.validM fp m k hvalidRowwise
  have hqr :
      H19.Theorem19_4.HouseholderQRBackwardError
        (m + k) m (finiteTranspose A) Q R_tall etaQR := by
    simpa [Q, R_tall, etaQR] using
      H19.Theorem19_4.householder_qr_backward_error
        fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR
  have hRblock : R_tall = lsQRTallBlock (k := k) R_hat := by
    simpa [R_hat] using
      lsQRTallBlock_of_upper_trapezoidal R_tall hqr.upper
  have hupper : IsUpperTrapezoidal m m R_hat :=
    lsQRTallBlock_top_upper_of_upper_trapezoidal R_tall hqr.upper
  have hdiag : ∀ i : Fin m, R_hat i i ≠ 0 := by
    simpa [R_hat, R_tall, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag hupper hvalidM
  let R_plus : Fin m → Fin m → ℝ :=
    fun i j => R_hat i j + DeltaR i j
  have htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j := by
    intro j
    simpa [R_plus, y1, matMulVec, matTranspose] using hsolve j
  obtain ⟨y, hRyRaw⟩ :=
    higham21_computed_top_block_exists_exact_preimage fp A hdomain y1
  have hRy : rectMatMulVec R_hat y = y1 := by
    simpa [R_hat, R_tall] using hRyRaw
  have hleft' : matMul (m + k) Q_inv Q_hat = idMatrix (m + k) := by
    simpa [Q_hat] using hleft
  have hQerr :
      HouseholderQRPanelQhatFixedAccumError (m + k) Q Q_hat etaQ := by
    simpa [Q, Q_hat, etaQ] using
      higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid
  have hfirst :
      rectMatMulVec
          (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
          x_hat = b :=
    Higham21QMethodDeltaA1.system_eq
      A Q_inv Q_hat R_plus b y1 x_hat hleft' htri rfl
  have hsecond :
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) y :=
    Higham21QMethodDeltaA2.transpose_representation
      A Q_hat R_hat y y1 x_hat hRy rfl
  have hrow1 :=
    Higham21QMethodDeltaA1.row_bound_of_qr_transpose_certificate
      A Q Q_hat Q_inv R_tall R_hat DeltaR hRblock
      (gamma_nonneg fp hvalidM) hqinv hqr hDeltaR hQerr hleft' hQinvOp
  have hrow2 :=
    Higham21QMethodDeltaA2.row_bound_of_qr_transpose_certificate
      A Q Q_hat R_tall R_hat hRblock hqr hQerr
  refine ⟨DeltaR, y, ?_, hfirst, hsecond, hrow1, hrow2⟩
  simpa [etaR] using hDeltaR

/-- A common row-wise radius for the two rounded-`Q_hat` perturbations when
    an operator bound on the supplied inverse is available. -/
noncomputable def Higham21QMethodRoundedRowwiseCoefficientOfInverseBound
    (fp : FPModel) (m k : ℕ) (qinv : ℝ) : ℝ :=
  let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaR := gamma fp m
  let etaQ := Higham21QMethodQhatRadius fp m k
  max
    ((etaQR + etaR * (1 + etaQR)) +
      (qinv * etaQ) * (1 + (etaQR + etaR * (1 + etaQR))))
    (etaQR + etaQ * (1 + etaQR))

/-- The source-shaped rounded-`Q_hat` row radius, using the inverse estimate
    `||Q_hat^{-1}||_2 <= 1 / (1 - etaQ)`. -/
noncomputable def Higham21QMethodRoundedRowwiseCoefficient
    (fp : FPModel) (m k : ℕ) : ℝ :=
  Higham21QMethodRoundedRowwiseCoefficientOfInverseBound fp m k
    (1 / (1 - Higham21QMethodQhatRadius fp m k))

theorem Higham21QMethodQhatRadius_nonneg
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    0 ≤ Higham21QMethodQhatRadius fp m k := by
  exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)

theorem Higham21QMethodRoundedRowwiseCoefficientOfInverseBound_nonneg
    (fp : FPModel) (m k : ℕ) (qinv : ℝ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    0 ≤ Higham21QMethodRoundedRowwiseCoefficientOfInverseBound fp m k qinv := by
  have hvalidRowwise :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid
  have hvalidQR :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalidRowwise
  have hetaQR : 0 ≤ H19.Theorem19_4.gamma_tilde fp (m + k) m :=
    H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hetaQ : 0 ≤ Higham21QMethodQhatRadius fp m k :=
    Higham21QMethodQhatRadius_nonneg fp m k hvalid
  have heta2 :
      0 ≤ H19.Theorem19_4.gamma_tilde fp (m + k) m +
        Higham21QMethodQhatRadius fp m k *
          (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m) := by
    exact add_nonneg hetaQR (mul_nonneg hetaQ (by linarith))
  exact heta2.trans (by
    unfold Higham21QMethodRoundedRowwiseCoefficientOfInverseBound
    exact le_max_right _ _)

theorem Higham21QMethodRoundedRowwiseCoefficient_nonneg
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    0 ≤ Higham21QMethodRoundedRowwiseCoefficient fp m k := by
  exact
    Higham21QMethodRoundedRowwiseCoefficientOfInverseBound_nonneg
      fp m k _ hvalid

/-- The base operation-count index used to absorb the rounded-`Q_hat`
    inverse, QR, and triangular-solve radii into one gamma term. -/
def Higham21QMethodRoundedGammaBaseIndex (m k : ℕ) : ℕ :=
  Higham21QMethodComputedGammaIndex m k +
    2 * ((m + k) * Higham21QMethodComputedGammaIndex m k)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: a concrete realization of
    the printed `gamma_tilde_{mn}`.  The leading `3 * n` also absorbs the
    Lemma 21.2 smallness factor and the row-to-operator `sqrt n` estimate. -/
def Higham21QMethodRoundedGammaIndex (m k : ℕ) : ℕ :=
  (3 * (m + k)) * Higham21QMethodRoundedGammaBaseIndex m k

theorem Higham21QMethodRoundedGammaBaseIndex_le_index
    (m k : ℕ) (hm : 0 < m) :
    Higham21QMethodRoundedGammaBaseIndex m k ≤
      Higham21QMethodRoundedGammaIndex m k := by
  have hfactor : 0 < 3 * (m + k) := by omega
  exact Nat.le_mul_of_pos_left _ hfactor

theorem Higham21QMethodComputedGammaIndex_le_roundedGammaIndex
    (m k : ℕ) (hm : 0 < m) :
    Higham21QMethodComputedGammaIndex m k ≤
      Higham21QMethodRoundedGammaIndex m k := by
  calc
    Higham21QMethodComputedGammaIndex m k ≤
        Higham21QMethodRoundedGammaBaseIndex m k := by
      dsimp [Higham21QMethodRoundedGammaBaseIndex]
      exact Nat.le_add_right _ _
    _ ≤ Higham21QMethodRoundedGammaIndex m k :=
      Higham21QMethodRoundedGammaBaseIndex_le_index m k hm

theorem Higham21QMethodRoundedGammaIndex.validComputed
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    gammaValid fp (Higham21QMethodComputedGammaIndex m k) :=
  gammaValid_mono fp
    (Higham21QMethodComputedGammaIndex_le_roundedGammaIndex m k hm) hvalid

theorem Higham21QMethodQhatRadius_le_gamma_n_mul_computed
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Higham21QMethodQhatRadius fp m k ≤
      gamma fp ((m + k) * Higham21QMethodComputedGammaIndex m k) := by
  let N := m + k
  let G := Higham21QMethodComputedGammaIndex m k
  have hN : 1 ≤ N := by simp [N]; omega
  have hGvalid : gammaValid fp G := by
    simpa [G] using
      Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hNG_le_base : N * G ≤ Higham21QMethodRoundedGammaBaseIndex m k := by
    have hK2 : N * G ≤ 2 * (N * G) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    exact hK2.trans (by
      dsimp [Higham21QMethodRoundedGammaBaseIndex, N, G]
      exact Nat.le_add_left _ _)
  have hNGvalid : gammaValid fp (N * G) :=
    gammaValid_mono fp
      (hNG_le_base.trans
        (Higham21QMethodRoundedGammaBaseIndex_le_index m k hm)) hvalid
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
    higham21_sqrt_nat_le_nat N
  calc
    Higham21QMethodQhatRadius fp m k =
        gamma fp G * Real.sqrt (N : ℝ) := by
      simp [Higham21QMethodQhatRadius, N, G]
    _ ≤ gamma fp G * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (gamma_nonneg fp hGvalid)
    _ = (N : ℝ) * gamma fp G := by ring
    _ ≤ gamma fp (N * G) :=
      gamma_nsmul_le fp N G hN hNGvalid
    _ = gamma fp ((m + k) * Higham21QMethodComputedGammaIndex m k) := by
      simp [N, G]

theorem Higham21QMethodQhatRadius_lt_one_of_roundedGamma_valid
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Higham21QMethodQhatRadius fp m k < 1 := by
  let N := m + k
  let G := Higham21QMethodComputedGammaIndex m k
  let K := N * G
  have h2K_le_base : 2 * K ≤ Higham21QMethodRoundedGammaBaseIndex m k := by
    dsimp [Higham21QMethodRoundedGammaBaseIndex, K, N, G]
    exact Nat.le_add_left _ _
  have h2Kvalid : gammaValid fp (2 * K) :=
    gammaValid_mono fp
      (h2K_le_base.trans
        (Higham21QMethodRoundedGammaBaseIndex_le_index m k hm)) hvalid
  have hq : Higham21QMethodQhatRadius fp m k ≤ gamma fp K := by
    simpa [K, N, G] using
      Higham21QMethodQhatRadius_le_gamma_n_mul_computed fp m k hm hvalid
  exact hq.trans_lt (gamma_lt_one fp K h2Kvalid)

/-- The exact rounded-Q coefficient is bounded by one gamma term before the
    final Lemma 21.2 dimension factor is absorbed. -/
theorem Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Higham21QMethodRoundedRowwiseCoefficient fp m k ≤
      gamma fp (Higham21QMethodRoundedGammaBaseIndex m k) := by
  let N := m + k
  let G := Higham21QMethodComputedGammaIndex m k
  let K := N * G
  let H := G + 2 * K
  let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaQ := Higham21QMethodQhatRadius fp m k
  let eta0 := Higham21QMethodRowwiseCoefficient fp m k
  let invQ := (1 / (1 - etaQ)) * etaQ
  have hH_eq : H = Higham21QMethodRoundedGammaBaseIndex m k := by
    simp [H, K, N, G, Higham21QMethodRoundedGammaBaseIndex]
  have hHvalid : gammaValid fp H := by
    apply gammaValid_mono fp
      (show H ≤ Higham21QMethodRoundedGammaIndex m k from ?_) hvalid
    rw [hH_eq]
    exact Higham21QMethodRoundedGammaBaseIndex_le_index m k hm
  have hGvalid : gammaValid fp G := by
    simpa [G] using
      Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hRowValid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k) :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k (by simpa [G] using hGvalid)
  have hQRValid :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hRowValid
  have hMValid :=
    Higham21QMethodRowwiseGammaIndex.validM fp m k hRowValid
  have hetaQR0 : 0 ≤ etaQR := by
    exact H19.Theorem19_4.gamma_tilde_nonneg fp hQRValid
  have heta00 : 0 ≤ eta0 := by
    exact Higham21QMethodRowwiseCoefficient_nonneg fp m k hQRValid hMValid
  have hetaQ0 : 0 ≤ etaQ := by
    exact Higham21QMethodQhatRadius_nonneg fp m k (by simpa [G] using hGvalid)
  have hetaQ_lt : etaQ < 1 := by
    exact Higham21QMethodQhatRadius_lt_one_of_roundedGamma_valid fp m k hm hvalid
  have hK_le_base : K ≤ H := by
    have hK2 : K ≤ 2 * K := Nat.le_mul_of_pos_left _ (by norm_num)
    exact hK2.trans (Nat.le_add_left _ _)
  have h2K_le_base : 2 * K ≤ H := Nat.le_add_left _ _
  have hKvalid : gammaValid fp K := gammaValid_mono fp hK_le_base hHvalid
  have h2Kvalid : gammaValid fp (2 * K) :=
    gammaValid_mono fp h2K_le_base hHvalid
  have hetaQ_le : etaQ ≤ gamma fp K := by
    simpa [etaQ, K, N, G] using
      Higham21QMethodQhatRadius_le_gamma_n_mul_computed fp m k hm hvalid
  have hgammaK0 : 0 ≤ gamma fp K := gamma_nonneg fp hKvalid
  have hgammaK_lt : gamma fp K < 1 := gamma_lt_one fp K h2Kvalid
  have hinvQ0 : 0 ≤ invQ := by
    exact mul_nonneg (one_div_pos.mpr (sub_pos.mpr hetaQ_lt)).le hetaQ0
  have hinvQ_le : invQ ≤ gamma fp (2 * K) := by
    have hfrac : etaQ / (1 - etaQ) ≤ gamma fp K / (1 - gamma fp K) :=
      div_le_div₀ hgammaK0 hetaQ_le (sub_pos.mpr hgammaK_lt) (by linarith)
    have hdouble :
        gamma fp K / (1 - gamma fp K) ≤
          (gamma fp K + gamma fp K) / (1 - gamma fp K) := by
      rw [div_le_div_iff₀ (sub_pos.mpr hgammaK_lt) (sub_pos.mpr hgammaK_lt)]
      nlinarith
    have habsorb :=
      gamma_add_div_one_sub_gamma_le_of_le fp K K (le_refl K) (by
        simpa [two_mul] using h2Kvalid)
    calc
      invQ = etaQ / (1 - etaQ) := by
        simp [invQ, div_eq_mul_inv, mul_comm]
      _ ≤ gamma fp K / (1 - gamma fp K) := hfrac
      _ ≤ (gamma fp K + gamma fp K) / (1 - gamma fp K) := hdouble
      _ ≤ gamma fp (2 * K) := by simpa [two_mul] using habsorb
  have heta0_le_G : eta0 ≤ gamma fp G := by
    calc
      eta0 ≤ gamma fp (Higham21QMethodRowwiseGammaIndex m k) := by
        exact Higham21QMethodRowwiseCoefficient_le_gamma_index fp m k hRowValid
      _ ≤ gamma fp G := by
        simpa [G] using
          Higham21QMethodComputedGammaIndex.rowwiseGamma_le fp m k
            (by simpa [G] using hGvalid)
  have hetaQR_le_eta0 : etaQR ≤ eta0 := by
    have hterm :
        0 ≤ gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m) :=
      mul_nonneg (gamma_nonneg fp hMValid) (by linarith)
    change H19.Theorem19_4.gamma_tilde fp (m + k) m ≤
      H19.Theorem19_4.gamma_tilde fp (m + k) m +
        gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)
    exact le_add_of_nonneg_right hterm
  have hetaQR_le_G : etaQR ≤ gamma fp G := hetaQR_le_eta0.trans heta0_le_G
  have hgammaG0 : 0 ≤ gamma fp G := gamma_nonneg fp hGvalid
  have hgamma2K0 : 0 ≤ gamma fp (2 * K) := gamma_nonneg fp h2Kvalid
  have hsum1 :
      gamma fp G + gamma fp (2 * K) +
          gamma fp G * gamma fp (2 * K) ≤ gamma fp H := by
    simpa [H] using gamma_sum_le fp G (2 * K) hHvalid
  have hmul1 :
      invQ * (1 + eta0) ≤
        gamma fp (2 * K) * (1 + gamma fp G) := by
    calc
      invQ * (1 + eta0) ≤ gamma fp (2 * K) * (1 + eta0) :=
        mul_le_mul_of_nonneg_right hinvQ_le (by linarith)
      _ ≤ gamma fp (2 * K) * (1 + gamma fp G) :=
        mul_le_mul_of_nonneg_left (by linarith) hgamma2K0
  have heta1 : eta0 + invQ * (1 + eta0) ≤ gamma fp H := by
    calc
      eta0 + invQ * (1 + eta0) ≤
          gamma fp G + gamma fp (2 * K) * (1 + gamma fp G) :=
        add_le_add heta0_le_G hmul1
      _ = gamma fp G + gamma fp (2 * K) +
          gamma fp G * gamma fp (2 * K) := by ring
      _ ≤ gamma fp H := hsum1
  have hGK_le_H : G + K ≤ H := by
    dsimp [H]
    exact Nat.add_le_add_left
      (Nat.le_mul_of_pos_left K (by norm_num)) G
  have hGKvalid : gammaValid fp (G + K) := gammaValid_mono fp hGK_le_H hHvalid
  have hsum2 :
      gamma fp G + gamma fp K + gamma fp G * gamma fp K ≤
        gamma fp (G + K) := gamma_sum_le fp G K hGKvalid
  have hmul2 :
      etaQ * (1 + etaQR) ≤ gamma fp K * (1 + gamma fp G) := by
    calc
      etaQ * (1 + etaQR) ≤ gamma fp K * (1 + etaQR) :=
        mul_le_mul_of_nonneg_right hetaQ_le (by linarith)
      _ ≤ gamma fp K * (1 + gamma fp G) :=
        mul_le_mul_of_nonneg_left (by linarith) hgammaK0
  have heta2 : etaQR + etaQ * (1 + etaQR) ≤ gamma fp H := by
    calc
      etaQR + etaQ * (1 + etaQR) ≤
          gamma fp G + gamma fp K * (1 + gamma fp G) :=
        add_le_add hetaQR_le_G hmul2
      _ = gamma fp G + gamma fp K + gamma fp G * gamma fp K := by ring
      _ ≤ gamma fp (G + K) := hsum2
      _ ≤ gamma fp H := gamma_mono fp hGK_le_H hHvalid
  have hmax :
      max (eta0 + invQ * (1 + eta0))
          (etaQR + etaQ * (1 + etaQR)) ≤ gamma fp H :=
    max_le heta1 heta2
  simpa [Higham21QMethodRoundedRowwiseCoefficient,
    Higham21QMethodRoundedRowwiseCoefficientOfInverseBound,
    Higham21QMethodRowwiseCoefficient, eta0, invQ, etaQR, etaQ,
    Higham21QMethodQhatRadius, hH_eq] using hmax

/-- The actual row-relative factor returned after Lemma 21.2 is bounded by
    the concrete `gamma_tilde_{mn}` used in the source-facing theorem. -/
theorem Higham21QMethodRoundedOutputCoefficient_le_gamma_index
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Real.sqrt 2 * Higham21QMethodRoundedRowwiseCoefficient fp m k ≤
      gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
  let H := Higham21QMethodRoundedGammaBaseIndex m k
  have hComputed :=
    Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have heta0 :=
    Higham21QMethodRoundedRowwiseCoefficient_nonneg fp m k hComputed
  have heta :=
    Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base fp m k hm hvalid
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have h2H_le : 2 * H ≤ Higham21QMethodRoundedGammaIndex m k := by
    have hN : 2 ≤ 3 * (m + k) := by omega
    simpa [Higham21QMethodRoundedGammaIndex, H] using
      Nat.mul_le_mul_right H hN
  have h2Hvalid : gammaValid fp (2 * H) :=
    gammaValid_mono fp h2H_le hvalid
  calc
    Real.sqrt 2 * Higham21QMethodRoundedRowwiseCoefficient fp m k ≤
        2 * Higham21QMethodRoundedRowwiseCoefficient fp m k :=
      mul_le_mul_of_nonneg_right hsqrt2 heta0
    _ ≤ 2 * gamma fp H :=
      mul_le_mul_of_nonneg_left (by simpa [H] using heta) (by norm_num)
    _ ≤ gamma fp (2 * H) :=
      gamma_nsmul_le fp 2 H (by norm_num) h2Hvalid
    _ ≤ gamma fp (Higham21QMethodRoundedGammaIndex m k) :=
      gamma_mono fp h2H_le hvalid

/-- The same inverse, triangular perturbation, and range coordinate satisfy
    both exact systems with one common row-wise perturbation radius. -/
theorem higham21_theorem21_4_computed_qhat_perturbations_common_row_bound_of_inverse_bound
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (qinv : ℝ) (hqinv : 0 ≤ qinv)
    (hleft :
      matMul (m + k) Q_inv
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)) =
        idMatrix (m + k))
    (hQinvOp : opNorm2Le Q_inv qinv) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    let etaR := gamma fp m
    let eta :=
      Higham21QMethodRoundedRowwiseCoefficientOfInverseBound fp m k qinv
    ∃ (DeltaR : Fin m → Fin m → ℝ) (y : Fin m → ℝ),
      (∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y ∧
      (∀ i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i ≤
          eta * rectRowNorm2 A i) ∧
      (∀ i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
          eta * rectRowNorm2 A i) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let etaQR : ℝ := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaR : ℝ := gamma fp m
  let etaQ : ℝ := Higham21QMethodQhatRadius fp m k
  let eta1 : ℝ :=
    (etaQR + etaR * (1 + etaQR)) +
      (qinv * etaQ) * (1 + (etaQR + etaR * (1 + etaQR)))
  let eta2 : ℝ := etaQR + etaQ * (1 + etaQR)
  let eta : ℝ := max eta1 eta2
  obtain ⟨DeltaR, y, hDeltaR, hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_theorem21_4_computed_qhat_perturbations_of_inverse_bound
      fp A b hm hdomain hvalid Q_inv qinv hqinv hleft hQinvOp
  refine ⟨DeltaR, y, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [etaR] using hDeltaR
  · simpa [Q_hat, R_hat, y1, x_hat] using hfirst
  · simpa [Q_hat, R_hat, y1, x_hat] using hsecond
  · intro i
    have hle : eta1 ≤ eta := le_max_left _ _
    exact (hrow1 i).trans (by
      apply mul_le_mul_of_nonneg_right hle
      exact rectRowNorm2_nonneg A i)
  · intro i
    have hle : eta2 ≤ eta := le_max_right _ _
    exact (hrow2 i).trans (by
      apply mul_le_mul_of_nonneg_right hle
      exact rectRowNorm2_nonneg A i)

/-- Concrete rounded-Q-method perturbation package.  Under the single
    combined gamma validity condition and `etaQ < 1`, it constructs one
    inverse, one triangular perturbation, and one range coordinate satisfying
    both exact systems and the common row-relative bound used by Lemma 21.2. -/
theorem higham21_theorem21_4_computed_qhat_perturbations_common_row_bound
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    let etaR := gamma fp m
    let eta := Higham21QMethodRoundedRowwiseCoefficient fp m k
    ∃ (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
        (DeltaR : Fin m → Fin m → ℝ) (y : Fin m → ℝ),
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) ∧
      (∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y ∧
      (∀ i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i ≤
          eta * rectRowNorm2 A i) ∧
      (∀ i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
          eta * rectRowNorm2 A i) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let etaR : ℝ := gamma fp m
  let etaQ : ℝ := Higham21QMethodQhatRadius fp m k
  let qinv : ℝ := 1 / (1 - etaQ)
  obtain ⟨Q_inv, hleft, hQinvOp⟩ :=
    higham21_theorem21_4_qhat_exists_left_inverse_with_opNorm2Le_of_computed_gamma
      fp A hm hvalid hsmall
  have hqinv : 0 ≤ qinv := by
    exact (one_div_pos.mpr (sub_pos.mpr hsmall)).le
  obtain ⟨DeltaR, y, hDeltaR, hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_theorem21_4_computed_qhat_perturbations_common_row_bound_of_inverse_bound
      fp A b hm hdomain hvalid Q_inv qinv hqinv hleft hQinvOp
  refine ⟨Q_inv, DeltaR, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Q_hat] using hleft
  · simpa [R_hat, etaR] using hDeltaR
  · simpa [Q_hat, R_hat, y1, x_hat] using hfirst
  · simpa [Q_hat, R_hat, y1, x_hat] using hsecond
  · simpa [Higham21QMethodRoundedRowwiseCoefficient, qinv, etaQ,
      Q_hat, R_hat] using hrow1
  · simpa [Higham21QMethodRoundedRowwiseCoefficient, qinv, etaQ,
      Q_hat, R_hat] using hrow2

/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: the actual rounded Q-method
    output is row-wise backward stable under the exact Lemma 21.2
    condition-number smallness hypothesis. -/
theorem higham21_theorem21_4_computed_qhat_rowwise_backward_stable_of_cond2_smallness
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hQsmall : Higham21QMethodQhatRadius fp m k < 1)
    (hCondSmall :
      3 *
        (Higham21QMethodRoundedRowwiseCoefficient fp m k *
          Real.sqrt ((m + k : ℕ) : ℝ) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A)) < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (Real.sqrt 2 * Higham21QMethodRoundedRowwiseCoefficient fp m k) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let eta : ℝ := Higham21QMethodRoundedRowwiseCoefficient fp m k
  let Aplus : Fin (m + k) → Fin m → ℝ :=
    undetAplusOfGramNonsingInv A
  let rho : ℝ :=
    eta * Real.sqrt ((m + k : ℕ) : ℝ) * higham21Cond2With A Aplus
  have heta : 0 ≤ eta := by
    exact Higham21QMethodRoundedRowwiseCoefficient_nonneg fp m k hvalid
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_qmethod_full_row_rank_canonical_right_inverse hdomain
  obtain ⟨Q_inv, DeltaR, y, hleft, hDeltaR, hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_theorem21_4_computed_qhat_perturbations_common_row_bound
      fp A b hm hdomain hvalid hQsmall
  let DeltaA1 : Fin m → Fin (m + k) → ℝ :=
    Higham21QMethodDeltaA1 A Q_inv
      (fun a b => R_hat a b + DeltaR a b)
  let DeltaA2 : Fin m → Fin (m + k) → ℝ :=
    Higham21QMethodDeltaA2 A Q_hat R_hat
  have hrow1' : ∀ i : Fin m,
      rectRowNorm2 DeltaA1 i ≤ eta * rectRowNorm2 A i := by
    simpa [DeltaA1, eta, R_hat] using hrow1
  have hrow2' : ∀ i : Fin m,
      rectRowNorm2 DeltaA2 i ≤ eta * rectRowNorm2 A i := by
    simpa [DeltaA2, eta, Q_hat, R_hat] using hrow2
  have hProd1 : rectOpNorm2Le (rectMatMul Aplus DeltaA1) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA1 Aplus eta heta hrow1'
  have hProd2 : rectOpNorm2Le (rectMatMul Aplus DeltaA2) rho := by
    simpa [rho] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA2 Aplus eta heta hrow2'
  have hsmall : 3 * max rho rho < 1 := by
    simpa [rho, eta, Aplus] using hCondSmall
  exact
    higham21_lemma21_2_rowwise_backward_error_bound_of_pseudoinverse_products
      A Aplus DeltaA1 DeltaA2 b x_hat y rho rho eta hRight
      (by simpa [DeltaA1, x_hat, Q_hat, R_hat, y1] using hfirst)
      (by simpa [DeltaA2, x_hat, Q_hat, R_hat, y1] using hsecond)
      hProd1 hProd2 hsmall heta hrow1' hrow2'

/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: source-facing rounded Q-method
    stability.  The concrete index realizes the printed
    `gamma_tilde_{mn}`, and `gamma * cond2(A) < 1` is the explicit repository
    form of Higham's stated condition `cond2(A) m n gamma_n < 1`. -/
theorem higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
      (gamma fp (Higham21QMethodRoundedGammaIndex m k)) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let eta := Higham21QMethodRoundedRowwiseCoefficient fp m k
  let N := m + k
  let H := Higham21QMethodRoundedGammaBaseIndex m k
  let cond := higham21Cond2With A (undetAplusOfGramNonsingInv A)
  have hComputed : gammaValid fp (Higham21QMethodComputedGammaIndex m k) :=
    Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hQsmall : Higham21QMethodQhatRadius fp m k < 1 :=
    Higham21QMethodQhatRadius_lt_one_of_roundedGamma_valid fp m k hm hvalid
  have heta0 : 0 ≤ eta := by
    exact Higham21QMethodRoundedRowwiseCoefficient_nonneg fp m k hComputed
  have hetaBase : eta ≤ gamma fp H := by
    simpa [eta, H] using
      Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base fp m k hm hvalid
  have hBaseValid : gammaValid fp H :=
    gammaValid_mono fp (by
      simpa [H] using Higham21QMethodRoundedGammaBaseIndex_le_index m k hm) hvalid
  have hN : 1 ≤ N := by simp [N]; omega
  have hfactor : 1 ≤ 3 * N := by omega
  have hscaled :
      ((3 * N : ℕ) : ℝ) * gamma fp H ≤
        gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
    simpa [Higham21QMethodRoundedGammaIndex, N, H] using
      gamma_nsmul_le fp (3 * N) H hfactor hvalid
  have hscalar :
      3 * eta * Real.sqrt (N : ℝ) ≤
        gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
    calc
      3 * eta * Real.sqrt (N : ℝ) ≤
          3 * gamma fp H * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hetaBase (by norm_num))
          (Real.sqrt_nonneg _)
      _ ≤ 3 * gamma fp H * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (higham21_sqrt_nat_le_nat N)
          (mul_nonneg (by norm_num) (gamma_nonneg fp hBaseValid))
      _ = ((3 * N : ℕ) : ℝ) * gamma fp H := by
        push_cast
        ring
      _ ≤ gamma fp (Higham21QMethodRoundedGammaIndex m k) := hscaled
  have hcond0 : 0 ≤ cond := by
    exact higham21Cond2With_nonneg A (undetAplusOfGramNonsingInv A)
  have hCondActual :
      3 * (eta * Real.sqrt (N : ℝ) * cond) < 1 := by
    have hle :
        3 * (eta * Real.sqrt (N : ℝ) * cond) ≤
          gamma fp (Higham21QMethodRoundedGammaIndex m k) * cond := by
      calc
        3 * (eta * Real.sqrt (N : ℝ) * cond) =
            (3 * eta * Real.sqrt (N : ℝ)) * cond := by ring
        _ ≤ gamma fp (Higham21QMethodRoundedGammaIndex m k) * cond :=
          mul_le_mul_of_nonneg_right hscalar hcond0
    exact hle.trans_lt (by simpa [cond] using hCondSmall)
  have hraw :
      UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat
        (Real.sqrt 2 * eta) := by
    simpa [Q_hat, R_hat, y1, x_hat, eta, N, cond] using
      higham21_theorem21_4_computed_qhat_rowwise_backward_stable_of_cond2_smallness
        fp A b hm hdomain hComputed hQsmall hCondActual
  have hcoeff :
      Real.sqrt 2 * eta ≤
        gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
    simpa [eta] using
      Higham21QMethodRoundedOutputCoefficient_le_gamma_index fp m k hm hvalid
  exact higham21_rowwise_backward_error_bound_mono hraw
    (gamma_nonneg fp hvalid) hcoeff

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    named-coefficient form of the concrete Householder panel `Q_hat` action
    error bound. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_coefficient
    {m k : ℕ}
    (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hvalid : gammaValid fp (11 * (m + k) + 23))
    (hx :
      x_hat =
        matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ))) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      Higham21QActionGrowthCoefficient fp (m + k) * vecNorm2 y1 := by
  simpa [Higham21QActionGrowthCoefficient] using
    higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat
      fp A y1 x_hat hvalid hx

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.10):
    conservative-coefficient form of the concrete Householder panel `Q_hat`
    action error bound.  Any source radius dominating
    `Higham21QActionGrowthCoefficient` inherits the vector-error certificate. -/
theorem higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_of_coefficient_le
    {m k : ℕ}
    (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hvalid : gammaValid fp (11 * (m + k) + 23))
    (hx :
      x_hat =
        matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ)))
    {eta : ℝ}
    (hcoeff : Higham21QActionGrowthCoefficient fp (m + k) ≤ eta) :
    vecNorm2 (fun i : Fin (m + k) =>
      x_hat i -
        matMulVec (m + k)
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (Fin.append y1 (0 : Fin k → ℝ)) i) ≤
      eta * vecNorm2 y1 := by
  exact le_trans
    (higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_coefficient
      fp A y1 x_hat hvalid hx)
    (mul_le_mul_of_nonneg_right hcoeff (vecNorm2_nonneg y1))

/-- **Theorem 21.4** (Higham): The Q method for underdetermined systems
    is row-wise backward stable.

    The Q method solves Rᵀy₁ = b and forms x = Q[y₁; 0]ᵀ using
    the QR factorization Aᵀ = Q[R; 0]. The computed x̂ is the
    minimum 2-norm solution to (A + ΔA)x = b, where:

    ‖ΔA‖_F ≤ mγ_{cn}‖A‖_F  (normwise)
    |ΔA| ≤ mnγ_{cn}|A|G, ‖G‖_F = 1  (componentwise)

    Note: b is not perturbed (unlike the least-squares QR result in
    Theorem 20.3).

    This legacy Gram-system summary is retained for compatibility.  The
    concrete rounded-output source theorem is
    `higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma`. -/
structure QMethodBackwardStable (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b y_hat : Fin m → ℝ)
    (c_bound : ℝ) : Prop where
  /-- c_bound is nonneg. -/
  bound_nonneg : 0 ≤ c_bound
  /-- The computed ŷ satisfies perturbed normal equations
      (AAᵀ + ΔG)ŷ = b with bounded ΔG.
      This captures the Q method's backward stability projected
      to the m×m Gram system AAᵀ. -/
  result : ∃ (ΔG : Fin m → Fin m → ℝ),
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) y_hat i = b i) ∧
    frobNorm ΔG ≤ c_bound

-- ============================================================
-- §21.3  SNE method backward error
-- ============================================================

/-- **SNE method backward error for underdetermined systems** (Higham §21.3).

    The SNE method solves RᵀRy = b where Aᵀ = Q[R; 0], then forms
    x = Aᵀy. The solve RᵀRy = b is equivalent to Cholesky-solving
    the m×m system AAᵀy = b (since AAᵀ = RᵀR for the exact R).

    The backward error of the Cholesky solve gives:
    (RᵀR + ΔC)ŷ = b where |ΔC| ≤ (γ(m+1) + 2γ(m) + γ(m)²)·|R̂ᵀ||R̂|

    This is a direct application of `cholesky_solve_backward_error_expanded`
    from CholeskySolve.lean with n := m (the Gram matrix is m×m). -/
theorem sne_backward_error (fp : FPModel) (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1)) :
    let R_hatT := fun i j : Fin m => R_hat j i
    let y_hat := fl_forwardSub fp m R_hatT b
    let x_hat := fl_backSub fp m R_hat y_hat
    ∃ ΔC : Fin m → Fin m → ℝ,
      (∀ i j, |ΔC i j| ≤
        (gamma fp (m + 1) + 2 * gamma fp m + gamma fp m ^ 2) *
          ∑ k : Fin m, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * x_hat j = b i) :=
  cholesky_solve_backward_error_expanded fp m AAT R_hat b hR_diag hChol hm1

-- ============================================================
-- §21.3  Forward error bound (eq. 21.11)
-- ============================================================

/-- **Forward error for underdetermined system solve** (Higham §21.3, eq. 21.11).

    For both the Q method and SNE method, the forward error satisfies:
    ‖x̂ − x‖₂/‖x‖₂ ≤ mnγ'_{cn} · cond₂(A) + O(u²)

    where cond₂(A) = ‖|A⁺||A|‖₂. Note this bound is independent
    of the row scaling of A.

    We prove the componentwise form: given backward error in the
    m×m Gram system, the forward error is bounded by
    |ŷ − y| ≤ |(AAᵀ)⁻¹| · |ΔG · ŷ|.

    This reuses `normwise_perturbation_bound` (Theorem 7.2) from
    PerturbationTheory.lean, noting that Δb = 0 for the Q method
    (the right-hand side b is not perturbed). -/
theorem underdetermined_forward_error (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| := by
  -- Since Δb = 0, the bound from Theorem 7.2 simplifies to
  -- |ŷ − y| ≤ |(AAᵀ)⁻¹| · (|ΔG|·|ŷ| + 0)
  -- We apply normwise_perturbation_bound with Δb := 0.
  let Δb : Fin m → ℝ := fun _ => 0
  have hPerturbed' : ∀ i, ∑ j, (AAT i j + ΔG i j) * y_hat j = b i + Δb i := by
    intro i; simp [Δb]; exact hPerturbed i
  have hExact' : ∀ i, ∑ j, AAT i j * y j = b i := fun i => hExact i
  have hBound := normwise_perturbation_bound m AAT AAT_inv y y_hat b ΔG Δb
    hInv.1 hExact' hPerturbed'
  intro i
  rw [abs_sub_comm]
  have h := hBound i
  -- Simplify: |Δb_j| = 0, so ∑|ΔG|·|ŷ| + |Δb| = ∑|ΔG|·|ŷ| + 0
  calc |y i - y_hat i|
      ≤ ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + |Δb j|) := h
    _ = ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + 0) := by
        simp [Δb]
    _ = ∑ j, |AAT_inv i j| * ∑ k, |ΔG j k| * |y_hat k| := by
        apply Finset.sum_congr rfl; intro j _; ring_nf

/-- Legacy Gram-system perturbation bound used in the SNE development.

    Despite its historical name, this theorem proves only the exact
    componentwise consequence for a supplied Gram perturbation. It is not
    the source-facing equation (21.11) closure and makes no SNE
    backward-stability claim. -/
theorem sne_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| := by
  -- Same proof as underdetermined_forward_error: apply Theorem 7.2 with Δb = 0
  have hPert' : ∀ i, matMulVec m (fun a c => AAT a c + ΔC a c) y_hat i = b i :=
    fun i => hPerturbed i
  exact underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔC hPert'

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.11):
    source-facing wrapper for the currently formalized Gram-system forward
    perturbation consequence.  This is not the full printed asymptotic
    `mn * gamma * cond_2(A) + O(u^2)` bound; it is the exact componentwise
    perturbation inequality used as a dependency for that row. -/
theorem higham21_eq21_11_gram_forward_error
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed :
      ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| :=
  underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔG hPerturbed

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    source-facing wrapper for the proved statement that the SNE Gram-system
    perturbation route has the same componentwise forward-error consequence as
    the Q-method Gram-system route.  The full source statement still requires
    instantiating the QR/SNE computed-object bounds. -/
theorem higham21_sne_gram_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| :=
  sne_forward_error_matches_q_method m AAT AAT_inv hInv b y y_hat hExact ΔC
    hPerturbed

/-- The linear term in Higham's equation (21.11), specialized to the Q method,
    where the right-hand side is unperturbed.  Written with
    `z = Aplus^T x`, it is the source form from equation (21.7):

    `(I - Aplus*A) DeltaA^T z - Aplus*DeltaA*x`. -/
noncomputable def higham21Eq21_11FirstOrder
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin n → ℝ :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let w := rectTransposeMulVec DeltaA z
  fun j =>
    w j - rectMatMulVec Aplus (rectMatMulVec A w) j -
      rectMatMulVec Aplus (rectMatMulVec DeltaA x) j

/-- Exact finite remainder accompanying `higham21Eq21_11FirstOrder`.
    Every summand contains `DeltaA` multiplied by a response difference:
    either the dual-coordinate change `z_hat - Aplus^T*x` or the forward
    change `x_hat - x`.  Thus this is the explicit finite term represented by
    `O(u^2)` in (21.11), before a separate quadratic norm estimate is applied. -/
noncomputable def higham21Eq21_11FiniteRemainder
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ) (z_hat : Fin m → ℝ) : Fin n → ℝ :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let dualChange := fun i => z_hat i - z i
  let forwardChange := fun j => x_hat j - x j
  let dualTerm := rectTransposeMulVec DeltaA dualChange
  fun j =>
    dualTerm j -
        rectMatMulVec Aplus (rectMatMulVec A dualTerm) j -
      rectMatMulVec Aplus (rectMatMulVec DeltaA forwardChange) j

/-- The equation-(21.11) source first-order term is exactly the already-proved
    equation-(21.7) first-order perturbation with `Deltab = 0`. -/
theorem higham21_eq21_11_firstOrder_eq_eq21_7_firstOrder
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    higham21Eq21_11FirstOrder A DeltaA b =
      higham21Eq21_7FirstOrder A DeltaA b (0 : Fin m → ℝ)
        (undetGramNonsingInv A) := by
  let G_inv : Fin m → Fin m → ℝ := undetGramNonsingInv A
  let Aplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv A
  let x : Fin n → ℝ := rectMatMulVec Aplus b
  let y : Fin m → ℝ := matMulVec m G_inv b
  let z : Fin m → ℝ := rectTransposeMulVec Aplus x
  let w : Fin n → ℝ := rectTransposeMulVec DeltaA z
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hRightEntry : ∀ r i : Fin m,
      (∑ k : Fin n, A r k * Aplus k i) =
        if r = i then 1 else 0 := by
    intro r i
    have hri := congrFun (congrFun hRight r) i
    simpa [rectMatMul, idMatrix] using hri
  have hx : x = rectTransposeMulVec A y := by
    simpa [x, Aplus, y, G_inv, undetAplusOfGramNonsingInv] using
      (rectMatMulVec_undetAplusOfGramInv A G_inv b)
  have hyz : y = z := by
    ext i
    symm
    rw [show z = rectTransposeMulVec Aplus x by rfl, hx]
    unfold rectTransposeMulVec
    calc
      ∑ j : Fin n, Aplus j i * (∑ r : Fin m, A r j * y r) =
          ∑ j : Fin n, ∑ r : Fin m,
            Aplus j i * (A r j * y r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ r : Fin m, ∑ j : Fin n,
            Aplus j i * (A r j * y r) := by
            rw [Finset.sum_comm]
      _ = ∑ r : Fin m,
            (∑ j : Fin n, A r j * Aplus j i) * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ r : Fin m, (if r = i then 1 else 0) * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [hRightEntry r i]
      _ = y i := by simp
  have hneg :
      rectMatMulVec Aplus
          (fun i => (0 : ℝ) - rectMatMulVec DeltaA x i) =
        fun j => -rectMatMulVec Aplus (rectMatMulVec DeltaA x) j := by
    simpa using
      (rectMatMulVec_smul Aplus (-1 : ℝ) (rectMatMulVec DeltaA x))
  ext j
  change
    w j - rectMatMulVec Aplus (rectMatMulVec A w) j -
          rectMatMulVec Aplus (rectMatMulVec DeltaA x) j =
      rectTransposeMulVec DeltaA y j -
          rectMatMulVec Aplus
            (rectMatMulVec A (rectTransposeMulVec DeltaA y)) j +
        rectMatMulVec Aplus
          (fun i => (0 : ℝ) - rectMatMulVec DeltaA x i) j
  rw [hyz, congrFun hneg j]
  rfl

/-- Exact finite equation-(21.11) expansion for any rowwise backward-error
    witness.  No perturbed-Gram inverse is assumed: the transpose witness is
    supplied by minimum-norm feasibility, and the remainder is the explicit
    bilinear term above. -/
theorem higham21_eq21_11_exact_finite_forward_expansion
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ) (z_hat : Fin m → ℝ)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hsystem :
      rectMatMulVec (fun i j => A i j + DeltaA i j) x_hat = b)
    (hrange :
      rectTransposeMulVec (fun i j => A i j + DeltaA i j) z_hat = x_hat) :
    (fun j =>
      x_hat j -
        rectMatMulVec (undetAplusOfGramNonsingInv A) b j) =
      fun j =>
        higham21Eq21_11FirstOrder A DeltaA b j +
          higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j := by
  let Aplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv A
  let x : Fin n → ℝ := rectMatMulVec Aplus b
  let z : Fin m → ℝ := rectTransposeMulVec Aplus x
  let w : Fin n → ℝ := rectTransposeMulVec DeltaA z
  let dualChange : Fin m → ℝ := fun i => z_hat i - z i
  let dualTerm : Fin n → ℝ := rectTransposeMulVec DeltaA dualChange
  let forwardChange : Fin n → ℝ := fun j => x_hat j - x j
  have hRangeAdd :
      x_hat = fun j =>
        rectTransposeMulVec A z_hat j +
          rectTransposeMulVec DeltaA z_hat j := by
    calc
      x_hat =
          rectTransposeMulVec (fun i j => A i j + DeltaA i j) z_hat :=
        hrange.symm
      _ = fun j =>
          rectTransposeMulVec A z_hat j +
            rectTransposeMulVec DeltaA z_hat j := by
        ext j
        unfold rectTransposeMulVec
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hAtRange :
      rectTransposeMulVec A z_hat =
        rectMatMulVec Aplus (matMulVec m (rectGram A) z_hat) := by
    simpa [Aplus] using
      higham21_lemma21_2_gram_pseudoinverse_range_of_transpose
        A hdet z_hat
  have hPAt :
      rectMatMulVec Aplus
          (rectMatMulVec A (rectTransposeMulVec A z_hat)) =
        rectTransposeMulVec A z_hat := by
    rw [← rectMatMulVec_rectMatMul]
    rw [hAtRange]
    simpa [Aplus] using
      higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
        A hdet (matMulVec m (rectGram A) z_hat)
  have hnull : ∀ j : Fin n,
      x_hat j - rectMatMulVec Aplus (rectMatMulVec A x_hat) j =
        rectTransposeMulVec DeltaA z_hat j -
          rectMatMulVec Aplus
            (rectMatMulVec A (rectTransposeMulVec DeltaA z_hat)) j := by
    intro j
    rw [hRangeAdd]
    rw [rectMatMulVec_add, rectMatMulVec_add]
    rw [hPAt]
    ring
  have hsystemAdd :
      (fun i =>
        rectMatMulVec A x_hat i + rectMatMulVec DeltaA x_hat i) = b := by
    rw [← rectMatMulVec_mat_add]
    exact hsystem
  have hApplied := congrArg (rectMatMulVec Aplus) hsystemAdd
  rw [rectMatMulVec_add] at hApplied
  have hcore : ∀ j : Fin n,
      x_hat j - x j =
        (x_hat j - rectMatMulVec Aplus (rectMatMulVec A x_hat) j) -
          rectMatMulVec Aplus (rectMatMulVec DeltaA x_hat) j := by
    intro j
    have hj := congrFun hApplied j
    have hj' :
        rectMatMulVec Aplus (rectMatMulVec A x_hat) j +
            rectMatMulVec Aplus (rectMatMulVec DeltaA x_hat) j = x j := by
      simpa [x] using hj
    linarith
  have hzSplit : z_hat = fun i => z i + dualChange i := by
    ext i
    simp [dualChange]
  have hwSplit :
      rectTransposeMulVec DeltaA z_hat = fun j => w j + dualTerm j := by
    rw [hzSplit]
    simpa [w, dualTerm] using
      higham21Eq21_7_rectTransposeMulVec_add DeltaA z dualChange
  have hpSplit :
      rectMatMulVec Aplus
          (rectMatMulVec A (rectTransposeMulVec DeltaA z_hat)) =
        fun j =>
          rectMatMulVec Aplus (rectMatMulVec A w) j +
            rectMatMulVec Aplus (rectMatMulVec A dualTerm) j := by
    rw [hwSplit]
    rw [rectMatMulVec_add, rectMatMulVec_add]
  have hxSplit : x_hat = fun j => x j + forwardChange j := by
    ext j
    simp [forwardChange]
  have hDeltaSplit :
      rectMatMulVec Aplus (rectMatMulVec DeltaA x_hat) =
        fun j =>
          rectMatMulVec Aplus (rectMatMulVec DeltaA x) j +
            rectMatMulVec Aplus (rectMatMulVec DeltaA forwardChange) j := by
    rw [hxSplit]
    rw [rectMatMulVec_add, rectMatMulVec_add]
  ext j
  have hcorej := hcore j
  rw [hnull j] at hcorej
  calc
    x_hat j - x j =
        (rectTransposeMulVec DeltaA z_hat j -
            rectMatMulVec Aplus
              (rectMatMulVec A (rectTransposeMulVec DeltaA z_hat)) j) -
          rectMatMulVec Aplus (rectMatMulVec DeltaA x_hat) j := hcorej
    _ =
        (w j - rectMatMulVec Aplus (rectMatMulVec A w) j -
            rectMatMulVec Aplus (rectMatMulVec DeltaA x) j) +
          (dualTerm j -
              rectMatMulVec Aplus (rectMatMulVec A dualTerm) j -
            rectMatMulVec Aplus
              (rectMatMulVec DeltaA forwardChange) j) := by
        rw [congrFun hwSplit j, congrFun hpSplit j,
          congrFun hDeltaSplit j]
        ring
    _ = higham21Eq21_11FirstOrder A DeltaA b j +
          higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j := by
        rfl

/-- Rowwise perturbations give the printed first-order coefficient in (21.11).
    For a genuinely underdetermined system (`2 <= n`), orthogonality of the two
    equation-(21.7) components improves the two separate
    `eta * sqrt(n) * cond2(A)` bounds to
    `n * eta * cond2(A)`. -/
theorem higham21_eq21_11_firstOrder_norm_le_rowwise_cond2
    {m n : ℕ} (A DeltaA : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    {eta : ℝ} (hn : 2 ≤ n)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (heta : 0 ≤ eta)
    (hrow : ∀ i : Fin m,
      rectRowNorm2 DeltaA i ≤ eta * rectRowNorm2 A i) :
    vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ≤
      (n : ℝ) * eta *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2
            (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  let Aplus : Fin n → Fin m → ℝ := undetAplusOfGramNonsingInv A
  let x : Fin n → ℝ := rectMatMulVec Aplus b
  let z : Fin m → ℝ := rectTransposeMulVec Aplus x
  let w : Fin n → ℝ := rectTransposeMulVec DeltaA z
  let p : Fin n → ℝ := fun j =>
    w j - rectMatMulVec Aplus (rectMatMulVec A w) j
  let v : Fin n → ℝ :=
    rectMatMulVec Aplus (rectMatMulVec DeltaA x)
  let q : Fin n → ℝ :=
    rectMatMulVec Aplus
      (fun i => (0 : ℝ) - rectMatMulVec DeltaA x i)
  let B : Fin n → Fin n → ℝ := rectMatMul Aplus DeltaA
  let cond : ℝ := higham21Cond2With A Aplus
  let rho : ℝ := eta * Real.sqrt (n : ℝ) * cond
  let target : ℝ := (n : ℝ) * eta * cond * vecNorm2 x
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A) := by
    simpa [Aplus] using
      undetAplusOfGramNonsingInv_domain_projection_symmetric A
  have hcond : 0 ≤ cond := by
    simpa [cond] using higham21Cond2With_nonneg A Aplus
  have hrho : 0 ≤ rho := by
    exact mul_nonneg
      (mul_nonneg heta (Real.sqrt_nonneg _)) hcond
  have hB : rectOpNorm2Le B rho := by
    simpa [B, rho, cond] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA Aplus eta heta hrow
  have hBt : rectOpNorm2Le (finiteTranspose B) rho :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le B hrho hB
  have hwEq : w = rectMatMulVec (finiteTranspose B) x := by
    ext j
    unfold w z B rectTransposeMulVec rectMatMulVec rectMatMul finiteTranspose
    calc
      ∑ i : Fin m, DeltaA i j * (∑ l : Fin n, Aplus l i * x l) =
          ∑ i : Fin m, ∑ l : Fin n,
            DeltaA i j * (Aplus l i * x l) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ l : Fin n, ∑ i : Fin m,
            DeltaA i j * (Aplus l i * x l) := by
            rw [Finset.sum_comm]
      _ = ∑ l : Fin n,
            (∑ i : Fin m, Aplus l i * DeltaA i j) * x l := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hw : vecNorm2 w ≤ rho * vecNorm2 x := by
    rw [hwEq]
    exact hBt x
  have hpw : vecNorm2 p ≤ vecNorm2 w := by
    have hproj :=
      rectMatMulVec_domainProjection_residual_norm_le_range_residual_of_symmetric_right_inverse
        A Aplus hRight hSym w (0 : Fin m → ℝ)
    rw [rectMatMulVec_rectMatMul] at hproj
    simpa [p, rectMatMulVec] using hproj
  have hp : vecNorm2 p ≤ rho * vecNorm2 x := hpw.trans hw
  have hv : vecNorm2 v ≤ rho * vecNorm2 x := by
    simpa [v, B, rectMatMulVec_rectMatMul] using hB x
  have hqEq : q = fun j => -v j := by
    ext j
    unfold q v rectMatMulVec
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hq : vecNorm2 q ≤ rho * vecNorm2 x := by
    rw [hqEq, vecNorm2_neg]
    exact hv
  have horth : (∑ j : Fin n, p j * q j) = 0 := by
    simpa [Aplus, x, z, w, p, q] using
      higham21Eq21_7_source_vectors_orthogonal
        A DeltaA b (0 : Fin m → ℝ) hdet
  have hfirst :
      higham21Eq21_11FirstOrder A DeltaA b = fun j => p j + q j := by
    ext j
    rw [hqEq]
    rfl
  have hpyth :
      vecNorm2Sq (higham21Eq21_11FirstOrder A DeltaA b) =
        vecNorm2Sq p + vecNorm2Sq q := by
    rw [hfirst]
    simpa [finiteVecNorm2Sq_fin] using
      finiteVecNorm2Sq_add_of_inner_eq_zero p q horth
  have hbound0 : 0 ≤ rho * vecNorm2 x :=
    mul_nonneg hrho (vecNorm2_nonneg x)
  have hpSq : vecNorm2Sq p ≤ (rho * vecNorm2 x) ^ 2 := by
    rw [← vecNorm2_sq]
    nlinarith [vecNorm2_nonneg p]
  have hqSq : vecNorm2Sq q ≤ (rho * vecNorm2 x) ^ 2 := by
    rw [← vecNorm2_sq]
    nlinarith [vecNorm2_nonneg q]
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hdim : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith
  have hsqrtSq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hn0
  have hrhoEq : rho ^ 2 = (n : ℝ) * (eta * cond) ^ 2 := by
    dsimp [rho]
    calc
      (eta * Real.sqrt (n : ℝ) * cond) ^ 2 =
          (Real.sqrt (n : ℝ)) ^ 2 * (eta * cond) ^ 2 := by ring
      _ = (n : ℝ) * (eta * cond) ^ 2 := by rw [hsqrtSq]
  have hrhoSq :
      2 * rho ^ 2 ≤ ((n : ℝ) * eta * cond) ^ 2 := by
    rw [hrhoEq]
    calc
      2 * ((n : ℝ) * (eta * cond) ^ 2) =
          (2 * (n : ℝ)) * (eta * cond) ^ 2 := by ring
      _ ≤ (n : ℝ) ^ 2 * (eta * cond) ^ 2 :=
        mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
      _ = ((n : ℝ) * eta * cond) ^ 2 := by ring
  have hnormSq :
      vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ^ 2 ≤ target ^ 2 := by
    rw [vecNorm2_sq, hpyth]
    calc
      vecNorm2Sq p + vecNorm2Sq q ≤
          2 * (rho * vecNorm2 x) ^ 2 := by nlinarith
      _ = 2 * rho ^ 2 * vecNorm2 x ^ 2 := by ring
      _ ≤ ((n : ℝ) * eta * cond) ^ 2 * vecNorm2 x ^ 2 :=
        mul_le_mul_of_nonneg_right hrhoSq (sq_nonneg _)
      _ = target ^ 2 := by
        simp [target]
        ring
  have htarget : 0 ≤ target := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hn0 heta) hcond) (vecNorm2_nonneg x)
  simpa [target, cond, x, Aplus] using
    (sq_le_sq₀
      (vecNorm2_nonneg (higham21Eq21_11FirstOrder A DeltaA b)) htarget).mp
      hnormSq

/-- The concrete rounded Q-method output used in equation (21.11). -/
noncomputable def higham21Eq21_11ComputedQhat
    (fp : FPModel) (m k : ℕ)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ) :
    Fin (m + k) → ℝ :=
  let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 := fl_forwardSub fp m (matTranspose R_hat) b
  matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))

/-- Higham, 2nd ed., Chapter 21, equation (21.11), concrete Q-method
    composition theorem.

    Theorem 21.4 supplies the actual rounded `Q_hat` output and a rowwise
    perturbation with radius `gamma_tilde_mn`.  Theorem 21.1 supplies the
    orthogonal first-order decomposition.  The result is the exact finite
    relative inequality

    `||x_hat-x||/||x|| <= n*gamma_tilde_mn*cond2(A) + ||R||/||x||`,

    where `R` is the explicit bilinear remainder above.  Consequently a
    quadratic estimate for `R` gives the printed `+ O(u^2)` form without any
    further algorithmic or certificate assumption. -/
theorem higham21_eq21_11_computed_qhat_relative_forward_error_with_remainder
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m) (hk : 0 < k) (hb : b ≠ 0)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let x_hat := higham21Eq21_11ComputedQhat fp m k A b
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let eta := gamma fp (Higham21QMethodRoundedGammaIndex m k)
    ∃ (DeltaA : Fin m → Fin (m + k) → ℝ) (z_hat : Fin m → ℝ),
      UndetRowwiseBackwardErrorFeasible m (m + k)
        A DeltaA b x_hat eta ∧
      rectTransposeMulVec (fun i j => A i j + DeltaA i j) z_hat = x_hat ∧
      higham21Eq21_11FirstOrder A DeltaA b =
        higham21Eq21_7FirstOrder A DeltaA b (0 : Fin m → ℝ)
          (undetGramNonsingInv A) ∧
      ((fun j => x_hat j - x j) =
        fun j =>
          higham21Eq21_11FirstOrder A DeltaA b j +
            higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j) ∧
      vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ≤
        ((m + k : ℕ) : ℝ) * eta *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x ∧
      vecNorm2 (fun j => x_hat j - x j) ≤
        ((m + k : ℕ) : ℝ) * eta *
            higham21Cond2With A (undetAplusOfGramNonsingInv A) * vecNorm2 x +
          vecNorm2
            (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) ∧
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
        ((m + k : ℕ) : ℝ) * eta *
            higham21Cond2With A (undetAplusOfGramNonsingInv A) +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x := by
  dsimp only
  let x_hat : Fin (m + k) → ℝ :=
    higham21Eq21_11ComputedQhat fp m k A b
  let Aplus : Fin (m + k) → Fin m → ℝ :=
    undetAplusOfGramNonsingInv A
  let x : Fin (m + k) → ℝ := rectMatMulVec Aplus b
  let eta : ℝ := gamma fp (Higham21QMethodRoundedGammaIndex m k)
  change ∃ (DeltaA : Fin m → Fin (m + k) → ℝ) (z_hat : Fin m → ℝ),
    UndetRowwiseBackwardErrorFeasible m (m + k)
        A DeltaA b x_hat eta ∧
      rectTransposeMulVec (fun i j => A i j + DeltaA i j) z_hat = x_hat ∧
      higham21Eq21_11FirstOrder A DeltaA b =
        higham21Eq21_7FirstOrder A DeltaA b (0 : Fin m → ℝ)
          (undetGramNonsingInv A) ∧
      ((fun j => x_hat j - x j) =
        fun j =>
          higham21Eq21_11FirstOrder A DeltaA b j +
            higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j) ∧
      vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x ∧
      vecNorm2 (fun j => x_hat j - x j) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          vecNorm2
            (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) ∧
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x
  have hcert :
      UndetRowwiseBackwardErrorBounded m (m + k) A b x_hat eta := by
    simpa [x_hat, eta, higham21Eq21_11ComputedQhat] using
      higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma
        fp A b hm hdomain hvalid hCondSmall
  rcases hcert with ⟨DeltaA, hfeas⟩
  obtain ⟨z_hat, hrange⟩ := hfeas.min_norm.exists_transpose_witness
  have hdet :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_qmethod_full_row_rank_gram_det_ne_zero hdomain
  have hfirstEq :=
    higham21_eq21_11_firstOrder_eq_eq21_7_firstOrder
      A DeltaA b hdet
  have hexact :=
    higham21_eq21_11_exact_finite_forward_expansion
      A DeltaA b x_hat z_hat hdet hfeas.min_norm.system_eq hrange
  have hN : 2 ≤ m + k := by omega
  have hfirstBound :
      vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x := by
    simpa [Aplus, x] using
      higham21_eq21_11_firstOrder_norm_le_rowwise_cond2
        A DeltaA b hN hdet hfeas.eta_nonneg hfeas.row_bound
  have habsolute :
      vecNorm2 (fun j => x_hat j - x j) ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus * vecNorm2 x +
          vecNorm2
            (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) := by
    calc
      vecNorm2 (fun j => x_hat j - x j) =
          vecNorm2 (fun j =>
            higham21Eq21_11FirstOrder A DeltaA b j +
              higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat j) :=
        congrArg vecNorm2 hexact
      _ ≤ vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) +
            vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) :=
        vecNorm2_add_le _ _
      _ ≤ ((m + k : ℕ) : ℝ) * eta *
              higham21Cond2With A Aplus * vecNorm2 x +
            vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) :=
        by nlinarith [hfirstBound]
  have hxmin : RectMinNormSolution m (m + k) A b x := by
    simpa [x, Aplus] using
      higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
        A b hdet
  have hxne : x ≠ 0 := by
    intro hx0
    apply hb
    rw [← hxmin.system_eq, hx0]
    ext i
    simp [rectMatMulVec]
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hxnorm
    apply hxne
    ext j
    exact (vecNorm2_eq_zero_iff x).mp hxnorm j
  have hxnorm_pos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  have hrelative :
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
        ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x := by
    calc
      vecNorm2 (fun j => x_hat j - x j) / vecNorm2 x ≤
          (((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus *
                vecNorm2 x +
              vecNorm2
                (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat)) /
            vecNorm2 x :=
        div_le_div_of_nonneg_right habsolute (le_of_lt hxnorm_pos)
      _ = ((m + k : ℕ) : ℝ) * eta * higham21Cond2With A Aplus +
          vecNorm2
              (higham21Eq21_11FiniteRemainder A DeltaA b x_hat z_hat) /
            vecNorm2 x := by
        field_simp [hxnorm_ne]
  exact ⟨DeltaA, z_hat, hfeas, hrange, hfirstEq, hexact,
    hfirstBound, habsolute, hrelative⟩

end NumStability
