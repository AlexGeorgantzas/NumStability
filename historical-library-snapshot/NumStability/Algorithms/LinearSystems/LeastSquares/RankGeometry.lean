import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# RankGeometry

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Higham, 2nd ed., Chapter 20, Section 20.5, transformed QR block
    `[R; 0]` for the system obtained from (20.15) after applying `Q^T` to
    `A = Q [R; 0]`.  The row dimension is `n + k`, with the first `n` rows
    carrying the square triangular block `R`. -/
noncomputable def lsQRTallBlock {n k : ℕ}
    (R : Fin n → Fin n → ℝ) : Fin (n + k) → Fin n → ℝ :=
  Fin.append R (fun _ : Fin k => fun _ : Fin n => 0)
/-- Top-block embedding is linear in the square block. -/
theorem lsQRTallBlock_add {n k : ℕ}
    (R S : Fin n → Fin n → ℝ) :
    (fun i j => lsQRTallBlock (k := k) R i j +
      lsQRTallBlock (k := k) S i j) =
      lsQRTallBlock (k := k) (fun i j => R i j + S i j) := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (n + k) =>
      lsQRTallBlock R i j + lsQRTallBlock S i j =
        lsQRTallBlock (fun i j => R i j + S i j) i j)
    ?left ?right i
  · intro i
    simp [lsQRTallBlock, Fin.append_left]
  · intro i
    simp [lsQRTallBlock, Fin.append_right]
/-- Matrix-vector multiplication by the transformed QR block `[R; 0]`. -/
theorem lsQRTallBlock_mulVec {n k : ℕ}
    (R : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (lsQRTallBlock R) x =
      Fin.append (rectMatMulVec R x) (0 : Fin k → ℝ) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (n + k) =>
      rectMatMulVec (lsQRTallBlock R) x i =
        Fin.append (rectMatMulVec R x) (0 : Fin k → ℝ) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec lsQRTallBlock
    rw [Fin.append_left, Fin.append_left]
  · intro i
    unfold rectMatMulVec lsQRTallBlock
    rw [Fin.append_right, Fin.append_right]
    simp
/-- Transpose action of the transformed QR block `[R; 0]` on `[h; d₂]`:
    `[R^T 0] [h; d₂] = R^T h`. -/
theorem lsQRTallBlock_transpose_mulVec_append {n k : ℕ}
    (R : Fin n → Fin n → ℝ) (h : Fin n → ℝ) (d2 : Fin k → ℝ) :
    (fun j : Fin n =>
      ∑ i : Fin (n + k), lsQRTallBlock R i j * Fin.append h d2 i) =
      fun j : Fin n => ∑ i : Fin n, R i j * h i := by
  ext j
  unfold lsQRTallBlock
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Column-side singular values for a real rectangular least-squares matrix,
    obtained by complexifying the real matrix.  Lean index `0` corresponds to
    the largest source singular value. -/
noncomputable def lsRealRectColSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin n) : ℝ :=
  complexMatrixSingularValue (realRectToCMatrix A) i
/-- Column rank for a real rectangular matrix, measured as the complex rank of
    its complexification. -/
noncomputable def lsRealRectColRank {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℕ :=
  complexMatrixRank (realRectToCMatrix A)
theorem lsRealRectColSingularValue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin n) :
    0 ≤ lsRealRectColSingularValue A i := by
  simpa [lsRealRectColSingularValue] using
    complexMatrixSingularValue_nonneg (realRectToCMatrix A) i
theorem lsRealRectColSingularValue_ne_zero_of_colRank_eq_card
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hrank : lsRealRectColRank A = n) (i : Fin n) :
    lsRealRectColSingularValue A i ≠ 0 := by
  have h := complexMatrixSingularValue_ne_zero_of_rank_eq_card
    (realRectToCMatrix A) (by simpa [lsRealRectColRank] using hrank)
  simpa [lsRealRectColSingularValue] using h i
theorem lsRealRectColSingularValue_pos_of_colRank_eq_card
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hrank : lsRealRectColRank A = n) (i : Fin n) :
    0 < lsRealRectColSingularValue A i := by
  exact lt_of_le_of_ne' (lsRealRectColSingularValue_nonneg A i)
    (lsRealRectColSingularValue_ne_zero_of_colRank_eq_card A hrank i)
/-- Local row-side singular values for a real rectangular matrix.  For a wide
    matrix this indexes the singular values of the row-side Gram operator
    `A A^T`, avoiding the automatic trailing zero singular values of `A^T A`. -/
noncomputable def lsRealRectRowSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  complexMatrixSingularValue (realRectToCMatrix (finiteTranspose A)) i
theorem lsRealRectRowSingularValue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    0 ≤ lsRealRectRowSingularValue A i := by
  simpa [lsRealRectRowSingularValue] using
    complexMatrixSingularValue_nonneg
      (realRectToCMatrix (finiteTranspose A)) i
theorem lsRealRectRowSingularValue_antitone {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Antitone (lsRealRectRowSingularValue A) := by
  simpa [lsRealRectRowSingularValue] using
    complexMatrixSingularValue_antitone
      (realRectToCMatrix (finiteTranspose A))
/-- Row rank for a real rectangular matrix, measured as the complex rank of
    the transposed row-side operator.  This is the rank notion naturally paired
    with `lsRealRectRowSingularValue`. -/
noncomputable def lsRealRectRowRank {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℕ :=
  complexMatrixRank (realRectToCMatrix (finiteTranspose A))
/-- The row rank is the number of nonzero row-side singular values. -/
theorem lsRealRectRowRank_eq_card_nonzero_rowSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    lsRealRectRowRank A =
      Fintype.card {i : Fin m // lsRealRectRowSingularValue A i ≠ 0} := by
  simpa [lsRealRectRowRank, lsRealRectRowSingularValue] using
    complexMatrixRank_eq_card_nonzero_singularValue
      (realRectToCMatrix (finiteTranspose A))
/-- If every row-side singular value is nonzero, the row rank is full. -/
theorem lsRealRectRowRank_eq_card_of_forall_rowSingularValue_ne_zero
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (h : ∀ i : Fin m, lsRealRectRowSingularValue A i ≠ 0) :
    lsRealRectRowRank A = m := by
  rw [lsRealRectRowRank_eq_card_nonzero_rowSingularValue]
  classical
  simp [Fintype.card_subtype, h]
/-- Full row rank makes every row-side singular value nonzero. -/
theorem lsRealRectRowSingularValue_ne_zero_of_rowRank_eq_card {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hrank : lsRealRectRowRank A = m)
    (i : Fin m) :
    lsRealRectRowSingularValue A i ≠ 0 := by
  have h := complexMatrixSingularValue_ne_zero_of_rank_eq_card
    (realRectToCMatrix (finiteTranspose A))
    (by simpa [lsRealRectRowRank] using hrank)
  simpa [lsRealRectRowSingularValue] using h i
/-- Any rectangular operator-2 certificate bounds every row-side singular value.
    This is the local bridge from the repository's predicate-style operator
    bounds to the singular-value language used in (20.21). -/
theorem lsRealRectRowSingularValue_le_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hA : rectOpNorm2Le A c) (i : Fin m) :
    lsRealRectRowSingularValue A i ≤ c := by
  have hT : rectOpNorm2Le (finiteTranspose A) c :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le A hc hA
  have hOp :
      complexMatrixOp2 (realRectToCMatrix (finiteTranspose A)) ≤ c :=
    complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
      (finiteTranspose A) hc hT
  exact
    (complexMatrixSingularValue_le_complexMatrixOp2
      (realRectToCMatrix (finiteTranspose A)) i).trans hOp
/-- Row-side `sigma_min` for a real rectangular matrix with a nonempty row
    dimension, using the last sorted row-side singular value. -/
noncomputable def lsRealRectSigmaMinRow {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) : ℝ :=
  lsRealRectRowSingularValue A (Fin.last m)
theorem lsRealRectSigmaMinRow_nonneg {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) :
    0 ≤ lsRealRectSigmaMinRow A := by
  simpa [lsRealRectSigmaMinRow] using
    lsRealRectRowSingularValue_nonneg A (Fin.last m)
theorem lsRealRectSigmaMinRow_le_rowSingularValue {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) (i : Fin (m + 1)) :
    lsRealRectSigmaMinRow A ≤ lsRealRectRowSingularValue A i := by
  have hanti := lsRealRectRowSingularValue_antitone A
  simpa [lsRealRectSigmaMinRow] using hanti (Fin.le_last i)
/-- Positive row-side `sigma_min` forces every row-side singular value to be
    positive. -/
theorem lsRealRectRowSingularValue_pos_of_sigmaMinRow_pos {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) (hσ : 0 < lsRealRectSigmaMinRow A)
    (i : Fin (m + 1)) :
    0 < lsRealRectRowSingularValue A i :=
  lt_of_lt_of_le hσ (lsRealRectSigmaMinRow_le_rowSingularValue A i)
/-- Positivity of the row-side `sigma_min` is equivalent to positivity of all
    row-side singular values. -/
theorem lsRealRectSigmaMinRow_pos_iff_forall_rowSingularValue_pos {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) :
    0 < lsRealRectSigmaMinRow A ↔
      ∀ i : Fin (m + 1), 0 < lsRealRectRowSingularValue A i := by
  constructor
  · intro hσ i
    exact lsRealRectRowSingularValue_pos_of_sigmaMinRow_pos A hσ i
  · intro h
    simpa [lsRealRectSigmaMinRow] using h (Fin.last m)
/-- The row-side `sigma_min` vanishes exactly when some row-side singular value
    vanishes. -/
theorem lsRealRectSigmaMinRow_eq_zero_iff_exists_rowSingularValue_eq_zero
    {m n : ℕ} (A : Fin (m + 1) → Fin n → ℝ) :
    lsRealRectSigmaMinRow A = 0 ↔
      ∃ i : Fin (m + 1), lsRealRectRowSingularValue A i = 0 := by
  constructor
  · intro hσ
    exact ⟨Fin.last m, by simpa [lsRealRectSigmaMinRow] using hσ⟩
  · rintro ⟨i, hi⟩
    have hle := lsRealRectSigmaMinRow_le_rowSingularValue A i
    have hnonneg := lsRealRectSigmaMinRow_nonneg A
    rw [hi] at hle
    exact le_antisymm hle hnonneg
/-- Positive row-side `sigma_min` gives full row rank. -/
theorem lsRealRectRowRank_eq_card_of_sigmaMinRow_pos {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) (hσ : 0 < lsRealRectSigmaMinRow A) :
    lsRealRectRowRank A = m + 1 :=
  lsRealRectRowRank_eq_card_of_forall_rowSingularValue_ne_zero A
    (fun i => ne_of_gt
      (lsRealRectRowSingularValue_pos_of_sigmaMinRow_pos A hσ i))
/-- Full row rank makes the row-side `sigma_min` positive. -/
theorem lsRealRectSigmaMinRow_pos_of_rowRank_eq_card {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ)
    (hrank : lsRealRectRowRank A = m + 1) :
    0 < lsRealRectSigmaMinRow A := by
  have hne : lsRealRectSigmaMinRow A ≠ 0 := by
    simpa [lsRealRectSigmaMinRow] using
      lsRealRectRowSingularValue_ne_zero_of_rowRank_eq_card
        A hrank (Fin.last m)
  exact lt_of_le_of_ne' (lsRealRectSigmaMinRow_nonneg A) hne
/-- For a nonempty row dimension, positive row-side `sigma_min` is equivalent
    to full row rank. -/
theorem lsRealRectSigmaMinRow_pos_iff_rowRank_eq_card {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) :
    0 < lsRealRectSigmaMinRow A ↔ lsRealRectRowRank A = m + 1 := by
  constructor
  · exact lsRealRectRowRank_eq_card_of_sigmaMinRow_pos A
  · exact lsRealRectSigmaMinRow_pos_of_rowRank_eq_card A
theorem lsRealRectSigmaMinRow_le_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hA : rectOpNorm2Le A c) :
    lsRealRectSigmaMinRow A ≤ c := by
  simpa [lsRealRectSigmaMinRow] using
    lsRealRectRowSingularValue_le_of_rectOpNorm2Le A hc hA (Fin.last m)
/-- Row-side singular-value lower bound for a real rectangular matrix. -/
theorem lsRealRectSigmaMinRow_mul_vecNorm2_le_transpose_mulVec {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) (x : Fin (m + 1) → ℝ) :
    lsRealRectSigmaMinRow A * vecNorm2 x ≤
      vecNorm2 (rectMatMulVec (finiteTranspose A) x) := by
  have h :=
    complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
      (realRectToCMatrix (finiteTranspose A)) (realVecToEuclidean x)
  simpa [lsRealRectSigmaMinRow, lsRealRectRowSingularValue,
    realVecToEuclidean_norm,
    realRectToCMatrix_euclideanLin_realVecToEuclidean_norm] using h
/-- The row-side `sigma_min` of a real rectangular matrix is attained by a
    nonzero real left vector in squared transpose-action form. -/
theorem lsRealRectSigmaMinRow_exists_transpose_attaining_vector_sq {m n : ℕ}
    (A : Fin (m + 1) → Fin n → ℝ) :
    ∃ p : Fin (m + 1) → ℝ, p ≠ 0 ∧
      vecNorm2Sq (rectMatMulVec (finiteTranspose A) p) =
        (lsRealRectSigmaMinRow A) ^ 2 * vecNorm2Sq p := by
  simpa [lsRealRectSigmaMinRow, lsRealRectRowSingularValue] using
    realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq
      (finiteTranspose A)
/-- An upper-trapezoidal tall QR panel is exactly the top square block stacked
    over zero rows. -/
theorem lsQRTallBlock_of_upper_trapezoidal {n k : ℕ}
    (Rhat : Fin (n + k) → Fin n → ℝ)
    (hupper : IsUpperTrapezoidal (n + k) n Rhat) :
    Rhat =
      lsQRTallBlock (k := k) (fun i : Fin n => fun j : Fin n =>
        Rhat (Fin.castAdd k i) j) := by
  ext row col
  cases row using Fin.addCases with
  | left row =>
      simp [lsQRTallBlock, Fin.append_left]
  | right row =>
      have hlt : col.val < (Fin.natAdd n row).val := by
        have hcol : col.val < n := col.isLt
        have hlt' : col.val < n + row.val := by omega
        simpa [Fin.natAdd] using hlt'
      simpa [lsQRTallBlock, Fin.append_right] using
        hupper (Fin.natAdd n row) col hlt
/-- The square top block of an upper-trapezoidal tall QR panel is upper
    triangular. -/
theorem lsQRTallBlock_top_upper_of_upper_trapezoidal {n k : ℕ}
    (Rhat : Fin (n + k) → Fin n → ℝ)
    (hupper : IsUpperTrapezoidal (n + k) n Rhat) :
    ∀ i j : Fin n, j.val < i.val →
      Rhat (Fin.castAdd k i) j = 0 := by
  intro i j hij
  simpa using hupper (Fin.castAdd k i) j hij
/-- Embed a square top block into an `m × n` rectangular matrix, with zero
    rows below index `n`.  This is the exact shape produced by a tall QR
    factorization after applying the orthogonal transformations. -/
noncomputable def rectTopBlock {m n : ℕ}
    (R : Fin n → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => if hi : i.val < n then R ⟨i.val, hi⟩ j else 0
theorem rectTopBlock_top {m n : ℕ} (R : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (hi : i.val < n) :
    rectTopBlock R i j = R ⟨i.val, hi⟩ j := by
  unfold rectTopBlock
  simp [hi]
theorem rectTopBlock_bottom {m n : ℕ} (R : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (hi : n ≤ i.val) :
    rectTopBlock R i j = 0 := by
  unfold rectTopBlock
  have hnot : ¬ i.val < n := Nat.not_lt.mpr hi
  simp [hnot]
theorem rectTopBlock_add {m n : ℕ}
    (R S : Fin n → Fin n → ℝ) :
    rectTopBlock (m := m) (fun i j => R i j + S i j) =
      fun (i : Fin m) (j : Fin n) =>
        rectTopBlock (m := m) R i j + rectTopBlock (m := m) S i j := by
  ext i j
  by_cases hi : i.val < n
  · simp [rectTopBlock_top, hi]
  · have hle : n ≤ i.val := le_of_not_gt hi
    simp [rectTopBlock_bottom, hle]

end NumStability
