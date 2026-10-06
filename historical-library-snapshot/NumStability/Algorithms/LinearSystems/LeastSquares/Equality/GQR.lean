import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.KKT
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Source.Higham.Chapter21.Lemma02.Symmetrization.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Theorem01.ComponentwisePerturbation.UnderdeterminedSpec
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators

/-!
# GQR

Canonical reusable module extracted without change from LSE.
-/

/-- Higham, 2nd ed., Chapter 20, equation (20.27):
    the displayed block matrix for `U^T A Q`.

    The source dimensions are represented as columns `p + q`, with `q = n-p`,
    and rows `r + q`, with `r = m-n+p`. -/
noncomputable def gqrAQBlock {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (r + q) → Fin (p + q) → ℝ :=
  Fin.append
    (fun i : Fin r => Fin.append (L11 i) (fun _ : Fin q => 0))
    (fun i : Fin q => Fin.append (L21 i) (L22 i))
/-- Higham, 2nd ed., Chapter 20, equation (20.27):
    the displayed block matrix `[S 0]` for `B Q`. -/
noncomputable def gqrBQBlock {p q : ℕ}
    (S : Fin p → Fin p → ℝ) :
    Fin p → Fin (p + q) → ℝ :=
  fun i => Fin.append (S i) (fun _ : Fin q => 0)
/-- Matrix-vector multiplication by the `B Q = [S 0]` block in (20.27)
    reduces to the triangular factor `S` acting on the first block of `y`. -/
theorem gqrBQBlock_mulVec {p q : ℕ}
    (S : Fin p → Fin p → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrBQBlock S) (Fin.append y1 y2) =
      rectMatMulVec S y1 := by
  ext i
  unfold rectMatMulVec gqrBQBlock
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    reverse both indices of an upper-triangular QR block.  This is the square
    block produced when a standard `[R;0]` QR display is turned into the
    lower-triangular block in the tall associated form (20.28). -/
def gqrReverseSquare {n : ℕ} (R : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => R (Fin.rev i) (Fin.rev j)
/-- Reversing both indices turns an upper-triangular QR block into the
    lower-triangular block used in Higham's Chapter 20 GQR display (20.28). -/
theorem gqrReverseSquare_lowerTriangular_of_upper {n : ℕ}
    {R : Fin n → Fin n → ℝ}
    (hR : IsUpperTriangular n R) :
    IsLowerTriangular (gqrReverseSquare R) := by
  intro i j hij
  unfold gqrReverseSquare
  exact hR (Fin.rev i) (Fin.rev j) ((Fin.rev_lt_rev).2 hij)
/-- Diagonal nonzeroness is preserved by the index reversal used to convert an
    upper QR block into the lower GQR block. -/
theorem gqrReverseSquare_diag_ne_zero_iff {n : ℕ}
    (R : Fin n → Fin n → ℝ) :
    (∀ i : Fin n, gqrReverseSquare R i i ≠ 0) ↔
      ∀ i : Fin n, R i i ≠ 0 := by
  constructor
  · intro h i
    have hi := h (Fin.rev i)
    simpa [gqrReverseSquare] using hi
  · intro h i
    simpa [gqrReverseSquare] using h (Fin.rev i)
/-- Square GQR conversion step: if a standard QR transform triangularizes the
    column-reversed square matrix, then reversing the transformed rows produces
    `gqrReverseSquare R`, the lower-triangular block used in (20.28). -/
theorem gqrReverseRowsOfQRReversedCols {n : ℕ}
    (C V R : Fin n → Fin n → ℝ)
    (hqr : matMulRectLeft (matTranspose V) (rectPermuteCols Fin.revPerm C) = R) :
    matMulRectLeft (finPermMatrix Fin.revPerm)
      (matMulRectLeft (matTranspose V) C) = gqrReverseSquare R := by
  ext i j
  rw [matMulRectLeft_finPermMatrix]
  unfold rectPermuteRows gqrReverseSquare
  have hentry := congrFun (congrFun hqr (Fin.rev i)) (Fin.rev j)
  unfold matMulRectLeft matTranspose rectPermuteCols at hentry
  unfold matMulRectLeft matTranspose
  simpa using hentry
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    a QR transform of a column-reversed square block gives an orthogonal
    left-factor whose transpose sends the original block to a lower-triangular
    block. -/
theorem exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols {n : ℕ}
    (C V R : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V)
    (hR : IsUpperTriangular n R)
    (hqr : matMulRectLeft (matTranspose V) (rectPermuteCols Fin.revPerm C) = R) :
    ∃ U : Fin n → Fin n → ℝ,
      IsOrthogonal n U ∧
        matMulRectLeft (matTranspose U) C = gqrReverseSquare R ∧
          IsLowerTriangular (gqrReverseSquare R) := by
  let P : Fin n → Fin n → ℝ := finPermMatrix Fin.revPerm
  let U : Fin n → Fin n → ℝ := matMul n V (matTranspose P)
  refine ⟨U, ?_, ?_, gqrReverseSquare_lowerTriangular_of_upper hR⟩
  · exact hV.mul (finPermMatrix_orthogonal Fin.revPerm).transpose
  · have hUt : matTranspose U = matMul n P (matTranspose V) := by
      simp [U, P, matTranspose_matMul, matTranspose_involutive]
    calc
      matMulRectLeft (matTranspose U) C
          = matMulRectLeft (matMul n P (matTranspose V)) C := by rw [hUt]
      _ = matMulRectLeft P (matMulRectLeft (matTranspose V) C) := by
          rw [matMulRectLeft_assoc]
      _ = gqrReverseSquare R := by
          simpa [P] using gqrReverseRowsOfQRReversedCols C V R hqr
/-- Exact-MGS version of
    `exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols`: nonzero MGS stages
    for the column-reversed square block supply the orthogonal transform and
    lower-triangular GQR block. -/
theorem exists_orthogonal_gqrReverseSquare_of_mgs_reversed_cols {n : ℕ}
    (C : Fin n → Fin n → ℝ)
    (hdiag : ∀ k : Fin n,
      gsColumnNorm2
        (modifiedGramSchmidtVectors (rectPermuteCols Fin.revPerm C) k.val k) ≠ 0) :
    ∃ (U : Fin n → Fin n → ℝ) (R : Fin n → Fin n → ℝ),
      IsOrthogonal n U ∧ IsUpperTriangular n R ∧
        matMulRectLeft (matTranspose U) C = gqrReverseSquare R ∧
          IsLowerTriangular (gqrReverseSquare R) := by
  let Crev : Fin n → Fin n → ℝ := rectPermuteCols Fin.revPerm C
  let R : Fin n → Fin n → ℝ := modifiedGramSchmidtR Crev
  have hfactor :
      Crev = matMulRect n n n (modifiedGramSchmidtQ Crev) R := by
    exact modifiedGramSchmidt_exact_factorization Crev hdiag
  have horth : GramSchmidtOrthonormalColumns (modifiedGramSchmidtQ Crev) :=
    modifiedGramSchmidtQ_orthonormal_columns Crev hdiag
  obtain ⟨V, hV, _hpreserve, hqr⟩ :=
    exists_orthogonal_completion_tall_qr_block (p := n) (q := 0)
      Crev (modifiedGramSchmidtQ Crev) R horth hfactor
  have hRupper : IsUpperTriangular n R :=
    IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal Crev)
  have hqrR : matMulRectLeft (matTranspose V) (rectPermuteCols Fin.revPerm C) = R := by
    simpa [Crev, lsQRTallBlock_zero] using hqr
  rcases exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols
      C V R hV hRupper hqrR with
    ⟨U, hU, hUeq, hLower⟩
  exact ⟨U, R, hU, hRupper, hUeq, hLower⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    a supplied tall QR factorization of `Bᵀ` yields the constraint block
    identity `B Q = [Rᵀ 0]` in the GQR display (20.27).

    The hypothesis is the exact transformed QR block
    `Qᵀ Bᵀ = [R;0]`.  Taking transposes entrywise gives the source GQR
    constraint block with `S = Rᵀ`.  This is still supplied exact algebra: it
    does not construct the QR factorization itself. -/
theorem gqrBQBlock_eq_of_transpose_tall_qr {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hqr : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R) :
    matMulRect p (p + q) (p + q) B Q = gqrBQBlock (matTranspose R) := by
  ext i j
  refine Fin.addCases
    (motive := fun j : Fin (p + q) =>
      matMulRect p (p + q) (p + q) B Q i j =
        gqrBQBlock (matTranspose R) i j)
    ?left ?right j
  · intro j
    have hentry := congrFun (congrFun hqr (Fin.castAdd q j)) i
    unfold matMulRectLeft matTranspose lsQRTallBlock at hentry
    unfold matMulRect gqrBQBlock matTranspose
    rw [Fin.append_left] at hentry
    rw [Fin.append_left]
    calc
      (∑ k : Fin (p + q), B i k * Q k (Fin.castAdd q j))
          = ∑ k : Fin (p + q), Q k (Fin.castAdd q j) * B i k := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = R j i := hentry
  · intro j
    have hentry := congrFun (congrFun hqr (Fin.natAdd p j)) i
    unfold matMulRectLeft matTranspose lsQRTallBlock at hentry
    unfold matMulRect gqrBQBlock matTranspose
    rw [Fin.append_right] at hentry
    rw [Fin.append_right]
    calc
      (∑ k : Fin (p + q), B i k * Q k (Fin.natAdd p j))
          = ∑ k : Fin (p + q), Q k (Fin.natAdd p j) * B i k := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = 0 := hentry
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10 computed-constraint algebra:
    if a computed tall QR product has the form `Bhatᵀ = Q*Rhat`, with `Q`
    orthogonal and `Rhat` upper trapezoidal, then the source-side matrix
    `Bhat` satisfies the GQR constraint block identity `Bhat*Q = [S,0]`.

    The square GQR constraint block is the transpose of the top square block
    of `Rhat`.  This is the exact algebra needed to connect a concrete rounded
    Householder QR of `Bᵀ` to the GQR `B Q = [S,0]` display. -/
theorem gqrBQBlock_eq_of_transpose_product_tall_qr {p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (Rhat : Fin (p + q) → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hRupper : IsUpperTrapezoidal (p + q) p Rhat) :
    let Bhat : Fin p → Fin (p + q) → ℝ :=
      fun i j => matMulRect (p + q) (p + q) p Q Rhat j i
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p => Rhat (Fin.castAdd q i) j)
    IsLowerTriangular S ∧
      matMulRect p (p + q) (p + q) Bhat Q = gqrBQBlock S := by
  dsimp
  let R : Fin p → Fin p → ℝ :=
    fun i : Fin p => fun j : Fin p => Rhat (Fin.castAdd q i) j
  have hRhatBlock :
      Rhat = lsQRTallBlock (k := q) R :=
    lsQRTallBlock_of_upper_trapezoidal (n := p) (k := q) Rhat hRupper
  have hRupperTop : IsUpperTriangular p R := by
    intro i j hij
    exact lsQRTallBlock_top_upper_of_upper_trapezoidal
      (n := p) (k := q) Rhat hRupper i j hij
  have hQtQ : matMul (p + q) (matTranspose Q) Q = idMatrix (p + q) := by
    ext i j
    simpa [matMul, rectMatMul, idMatrix] using hQ.left_inv i j
  have hqr :
      matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p =>
            matMulRect (p + q) (p + q) p Q Rhat j i) =
        lsQRTallBlock (k := q) R := by
    calc
      matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p =>
            matMulRect (p + q) (p + q) p Q Rhat j i)
          =
        matMulRectLeft (matTranspose Q) (matMulRectLeft Q Rhat) := by
          rfl
      _ = matMulRectLeft (matMul (p + q) (matTranspose Q) Q) Rhat := by
          rw [← matMulRectLeft_assoc]
      _ = matMulRectLeft (idMatrix (p + q)) Rhat := by
          rw [hQtQ]
      _ = Rhat := matMulRectLeft_id Rhat
      _ = lsQRTallBlock (k := q) R := hRhatBlock
  exact
    ⟨isLowerTriangular_matTranspose_of_isUpperTriangular hRupperTop,
      gqrBQBlock_eq_of_transpose_tall_qr
        (fun i j => matMulRect (p + q) (p + q) p Q Rhat j i)
        Q R hqr⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ`, plus the remaining MGS orthonormality
    dependency, constructs the GQR constraint block `B Q = [S 0]` with
    `S` lower triangular. -/
theorem exists_gqr_constraint_block_of_mgs_orthonormal {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0)
    (horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j))) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S := by
  obtain ⟨Q, R, hQorth, hRupper, hqr⟩ :=
    exists_transpose_tall_qr_of_mgs_orthonormal B hdiag horth
  refine ⟨Q, matTranspose R, hQorth,
    isLowerTriangular_matTranspose_of_isUpperTriangular hRupper, ?_⟩
  exact gqrBQBlock_eq_of_transpose_tall_qr B Q R hqr
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ` with nonzero stage normalizers constructs the GQR
    constraint block `B Q = [S 0]` with `S` lower triangular. -/
theorem exists_gqr_constraint_block_of_mgs {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S := by
  have horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j)) :=
    modifiedGramSchmidtQ_orthonormal_columns
      (fun j : Fin (p + q) => fun i : Fin p => B i j) hdiag
  exact exists_gqr_constraint_block_of_mgs_orthonormal B hdiag horth
/-- Matrix-vector multiplication by the `U^T A Q` block in (20.27). -/
theorem gqrAQBlock_mulVec {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2) =
      Fin.append
        (rectMatMulVec L11 y1)
        (fun i : Fin q => rectMatMulVec L21 y1 i +
          rectMatMulVec L22 y2 i) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2) i =
        Fin.append (rectMatMulVec L11 y1)
          (fun i : Fin q => rectMatMulVec L21 y1 i +
            rectMatMulVec L22 y2 i) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec gqrAQBlock
    rw [Fin.append_left, Fin.append_left, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  · intro i
    unfold rectMatMulVec gqrAQBlock
    rw [Fin.append_right, Fin.append_right, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
/-- Candidate lower block `L` reconstructed from the (20.27) GQR block display
in the tall case `m >= n`, with `r = k + p`. Its first `p` rows are the bottom
`p` rows of `L11` followed by the zero block, and its last `q` rows are
`[L21 L22]`; lower-triangularity is an explicit hypothesis of the link theorem
below. -/
noncomputable def gqrAQTallLFromEq20_27 {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (p + q) → Fin (p + q) → ℝ :=
  Fin.append
    (fun i : Fin p => Fin.append (L11 (Fin.natAdd k i)) (fun _ : Fin q => 0))
    (fun i : Fin q => Fin.append (L21 i) (L22 i))
/-- Tall (20.28) reconstruction helper: the candidate square block `L`
    recovered from (20.27) is lower triangular once the trailing `p` rows of
    `L11` and the `L22` block have the corresponding lower-triangular patterns.

    This is still only block-shape algebra; it does not prove those patterns
    from a QR construction. -/
theorem gqrAQTallLFromEq20_27_lowerTriangular_of_blocks {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      L11 (Fin.natAdd k i) j = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) := by
  intro i
  exact Fin.addCases
    (motive := fun i : Fin (p + q) =>
      ∀ j : Fin (p + q), i.val < j.val →
        gqrAQTallLFromEq20_27 L11 L21 L22 i j = 0)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (p + q) =>
          (Fin.castAdd q i).val < j.val →
            gqrAQTallLFromEq20_27 L11 L21 L22 (Fin.castAdd q i) j = 0)
        (fun j hij => by
          simpa [gqrAQTallLFromEq20_27] using hL11 i j (by simpa using hij))
        (fun j _hij => by
          simp [gqrAQTallLFromEq20_27])
        j hij)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (p + q) =>
          (Fin.natAdd p i).val < j.val →
            gqrAQTallLFromEq20_27 L11 L21 L22 (Fin.natAdd p i) j = 0)
        (fun j hij => by
          have hij' : p + i.val < j.val := by simpa using hij
          have hle : j.val ≤ p + i.val :=
            Nat.le_trans (Nat.le_of_lt j.isLt) (Nat.le_add_right p i.val)
          exact False.elim ((Nat.not_lt.mpr hle) hij'))
        (fun j hij => by
          simpa [gqrAQTallLFromEq20_27] using hL22 i j (by simpa using hij))
        j hij)
    i
/-- Source-facing tall-case link between the (20.27) block display and the
(20.28) display. If the leading `k` rows of `L11` vanish and the reconstructed
bottom block is lower triangular, then the row action of (20.27) is exactly
`[0; L]` in the tall case `m >= n`. -/
theorem gqrAQBlock_tall_eq20_28_row_action_of_top_zero {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin k),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.castAdd p i)) = 0) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin p),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.natAdd k i)) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q i)) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd (k + p) i) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd p i)) := by
  refine ⟨hlower, ?_, ?_, ?_⟩
  · intro y1 y2 i
    unfold rectMatMulVec gqrAQBlock
    rw [Fin.append_left, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, hzero i]
  · intro y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQTallLFromEq20_27
    rw [Fin.append_left, Fin.append_left]
  · intro y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQTallLFromEq20_27
    rw [Fin.append_right, Fin.append_right]
/-- Tall (20.28) row-action reconstruction from source-shaped block conditions:
    the leading `k` rows vanish, the trailing `p` rows of `L11` are lower
    triangular, and `L22` is lower triangular.

    This avoids exposing the combined reconstructed-`L` triangularity as a
    separate hypothesis, but still does not prove those block conditions from QR.
    -/
theorem gqrAQBlock_tall_eq20_28_row_action_of_top_zero_blocks {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      L11 (Fin.natAdd k i) j = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin k),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.castAdd p i)) = 0) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin p),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q (Fin.natAdd k i)) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.castAdd q i)) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd (k + p) i) =
        rectMatMulVec (gqrAQTallLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
          (Fin.natAdd p i)) := by
  exact gqrAQBlock_tall_eq20_28_row_action_of_top_zero L11 L21 L22 hzero
    (gqrAQTallLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)
/-- Leading block `X` reconstructed from the (20.27) GQR block display in the
wide case `m < n`, with `p = k + r`. It consists of the first `k` columns of
`L11` and `L21`. -/
noncomputable def gqrAQWideXFromEq20_27 {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ) :
    Fin (r + q) → Fin k → ℝ :=
  Fin.append
    (fun i : Fin r => fun j : Fin k => L11 i (Fin.castAdd r j))
    (fun i : Fin q => fun j : Fin k => L21 i (Fin.castAdd r j))
/-- Candidate lower block `L` reconstructed from the (20.27) GQR block display
in the wide case `m < n`, with `p = k + r`. It consists of the trailing `r`
columns of `L11` and `L21`, together with the zero block and `L22`;
lower-triangularity is an explicit hypothesis of the link theorem below. -/
noncomputable def gqrAQWideLFromEq20_27 {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (r + q) → Fin (r + q) → ℝ :=
  Fin.append
    (fun i : Fin r => Fin.append (fun j : Fin r => L11 i (Fin.natAdd k j))
      (fun _ : Fin q => 0))
    (fun i : Fin q => Fin.append (fun j : Fin r => L21 i (Fin.natAdd k j)) (L22 i))
/-- Wide (20.28) reconstruction helper: the candidate trailing square block `L`
    recovered from (20.27) is lower triangular once the trailing `r` columns of
    `L11` and the `L22` block have the corresponding lower-triangular patterns.

    This is still only block-shape algebra; it does not prove those patterns
    from a QR construction. -/
theorem gqrAQWideLFromEq20_27_lowerTriangular_of_blocks {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      L11 i (Fin.natAdd k j) = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) := by
  intro i
  exact Fin.addCases
    (motive := fun i : Fin (r + q) =>
      ∀ j : Fin (r + q), i.val < j.val →
        gqrAQWideLFromEq20_27 L11 L21 L22 i j = 0)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (r + q) =>
          (Fin.castAdd q i).val < j.val →
            gqrAQWideLFromEq20_27 L11 L21 L22 (Fin.castAdd q i) j = 0)
        (fun j hij => by
          simpa [gqrAQWideLFromEq20_27] using hL11 i j (by simpa using hij))
        (fun j _hij => by
          simp [gqrAQWideLFromEq20_27])
        j hij)
    (fun i j hij =>
      Fin.addCases
        (motive := fun j : Fin (r + q) =>
          (Fin.natAdd r i).val < j.val →
            gqrAQWideLFromEq20_27 L11 L21 L22 (Fin.natAdd r i) j = 0)
        (fun j hij => by
          have hij' : r + i.val < j.val := by simpa using hij
          have hle : j.val ≤ r + i.val :=
            Nat.le_trans (Nat.le_of_lt j.isLt) (Nat.le_add_right r i.val)
          exact False.elim ((Nat.not_lt.mpr hle) hij'))
        (fun j hij => by
          simpa [gqrAQWideLFromEq20_27] using hL22 i j (by simpa using hij))
        j hij)
    i
/-- Source-facing wide-case link between the (20.27) block display and the
(20.28) display. If the reconstructed trailing block is lower triangular, then
the row action of (20.27) is exactly `[X L]` in the wide case `m < n`. -/
theorem gqrAQBlock_wide_eq20_28_row_action {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin r),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.castAdd q i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.castAdd q i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.castAdd q i)) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.natAdd r i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.natAdd r i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.natAdd r i)) := by
  refine ⟨hlower, ?_, ?_⟩
  · intro y0 y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQWideXFromEq20_27 gqrAQWideLFromEq20_27
    simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right, add_comm]
  · intro y0 y1 y2 i
    unfold rectMatMulVec gqrAQBlock gqrAQWideXFromEq20_27 gqrAQWideLFromEq20_27
    simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right, add_assoc]
/-- Wide (20.28) row-action reconstruction from source-shaped block
    conditions: the trailing `r` columns of `L11` and the `L22` block have the
    corresponding lower-triangular patterns.

    This avoids exposing the combined reconstructed-`L` triangularity as a
    separate hypothesis, but still does not prove those block conditions from QR.
    -/
theorem gqrAQBlock_wide_eq20_28_row_action_of_blocks {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      L11 i (Fin.natAdd k j) = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin r),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.castAdd q i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.castAdd q i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.castAdd q i)) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec (gqrAQBlock L11 L21 L22) (Fin.append (Fin.append y0 y1) y2)
          (Fin.natAdd r i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 L11 L21) y0 (Fin.natAdd r i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.append y1 y2)
            (Fin.natAdd r i)) := by
  exact gqrAQBlock_wide_eq20_28_row_action L11 L21 L22
    (gqrAQWideLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)
/-- Associated-row version of the tall (20.28) block `[0; L]` with row type
`Fin ((k + p) + q)`, matching the row association of (20.27) when
`r = k + p`. -/
noncomputable def gqrAQTallBlockAssoc {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin ((k + p) + q) → Fin (p + q) → ℝ :=
  Fin.append
    (Fin.append (fun _ : Fin k => fun _ : Fin (p + q) => 0)
      (fun i : Fin p => fun j => L (Fin.castAdd q i) j))
    (fun i : Fin q => fun j => L (Fin.natAdd p i) j)
/-- Vector-action form of the associated-row tall (20.28) block `[0; L]`,
    matching the row association used by (20.27). -/
theorem gqrAQTallBlockAssoc_mulVec {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ)
    (y : Fin (p + q) → ℝ) :
    rectMatMulVec (gqrAQTallBlockAssoc (k := k) L) y =
      Fin.append
        (Fin.append (0 : Fin k → ℝ)
          (fun i : Fin p => rectMatMulVec L y (Fin.castAdd q i)))
        (fun i : Fin q => rectMatMulVec L y (Fin.natAdd p i)) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin ((k + p) + q) =>
      rectMatMulVec (gqrAQTallBlockAssoc (k := k) L) y i =
        Fin.append
          (Fin.append (0 : Fin k → ℝ)
            (fun i : Fin p => rectMatMulVec L y (Fin.castAdd q i)))
          (fun i : Fin q => rectMatMulVec L y (Fin.natAdd p i)) i)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun i : Fin (k + p) =>
        rectMatMulVec (gqrAQTallBlockAssoc (k := k) L) y (Fin.castAdd q i) =
          Fin.append
            (Fin.append (0 : Fin k → ℝ)
              (fun i : Fin p => rectMatMulVec L y (Fin.castAdd q i)))
            (fun i : Fin q => rectMatMulVec L y (Fin.natAdd p i))
            (Fin.castAdd q i))
      ?zeroRows ?middleRows i
    · intro i
      simp [rectMatMulVec, gqrAQTallBlockAssoc]
    · intro i
      simp [rectMatMulVec, gqrAQTallBlockAssoc]
  · intro i
    simp [rectMatMulVec, gqrAQTallBlockAssoc]
/-- Higham, 2nd ed., Chapter 20, equation (20.28), associated-row tall-case
    shape for `U^T A Q = [0; L]` in the row association used by (20.27).

    This records the exact displayed block shape once the transformed matrix is
    supplied. It does not construct the orthogonal factors. -/
structure GQRAQTallAssocCase (k p q : ℕ)
    (M : Fin ((k + p) + q) → Fin (p + q) → ℝ) where
  /-- Lower-triangular square block `L`. -/
  L : Fin (p + q) → Fin (p + q) → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [0; L]` with associated rows. -/
  aq_eq : M = gqrAQTallBlockAssoc (k := k) L
/-- Vector-action form of a supplied associated-row tall (20.28) shape. -/
theorem GQRAQTallAssocCase.mulVec_eq {k p q : ℕ}
    {M : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    (h : GQRAQTallAssocCase k p q M) (y : Fin (p + q) → ℝ) :
    rectMatMulVec M y =
      Fin.append
        (Fin.append (0 : Fin k → ℝ)
          (fun i : Fin p => rectMatMulVec h.L y (Fin.castAdd q i)))
        (fun i : Fin q => rectMatMulVec h.L y (Fin.natAdd p i)) := by
  rcases h with ⟨L, _lowerL, hM⟩
  subst M
  simpa using gqrAQTallBlockAssoc_mulVec (k := k) L y
/-- Tall (20.28)-to-(20.27) extraction: the `L11` block induced by a supplied
    `[0; L]` shape. Its leading `k` rows vanish and its trailing `p` rows are
    the first `p` columns of `L`. -/
noncomputable def gqrAQTallL11FromEq20_28 {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin (k + p) → Fin p → ℝ :=
  Fin.append
    (fun _ : Fin k => fun _ : Fin p => 0)
    (fun i : Fin p => fun j : Fin p => L (Fin.castAdd q i) (Fin.castAdd q j))
/-- Tall (20.28)-to-(20.27) extraction: the `L21` block induced by a supplied
    `[0; L]` shape. -/
noncomputable def gqrAQTallL21FromEq20_28 {p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin q → Fin p → ℝ :=
  fun i : Fin q => fun j : Fin p => L (Fin.natAdd p i) (Fin.castAdd q j)
/-- Tall (20.28)-to-(20.27) extraction: the trailing `L22` block induced by a
    supplied `[0; L]` shape. -/
noncomputable def gqrAQTallL22FromEq20_28 {p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin q → Fin q → ℝ :=
  fun i : Fin q => fun j : Fin q => L (Fin.natAdd p i) (Fin.natAdd p j)
/-- The trailing `L22` block extracted from a lower-triangular tall-case
    (20.28) block is lower triangular. -/
theorem gqrAQTallL22FromEq20_28_lowerTriangular {p q : ℕ}
    {L : Fin (p + q) → Fin (p + q) → ℝ}
    (hL : IsLowerTriangular L) :
    IsLowerTriangular (gqrAQTallL22FromEq20_28 L) := by
  intro i j hij
  unfold gqrAQTallL22FromEq20_28
  exact hL (Fin.natAdd p i) (Fin.natAdd p j) (by simpa using hij)
/-- Tall-case reverse block packaging: extracting `L11`, `L21`, and `L22`
    from a supplied (20.28) `[0; L]` shape gives the (20.27) `UᵀAQ` block.

    This is the algebraic direction needed by the construction route in
    Theorem 20.9 after an orthogonal `U` has been supplied with
    `Uᵀ(AQ) = [0; L]`. It does not construct `U`. -/
theorem gqrAQBlock_eq_tallBlockAssoc_of_eq20_28 {k p q : ℕ}
    (L : Fin (p + q) → Fin (p + q) → ℝ)
    (hL : IsLowerTriangular L) :
    gqrAQBlock
        (gqrAQTallL11FromEq20_28 (k := k) L)
        (gqrAQTallL21FromEq20_28 L)
        (gqrAQTallL22FromEq20_28 L) =
      gqrAQTallBlockAssoc (k := k) L := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin ((k + p) + q) =>
      gqrAQBlock
          (gqrAQTallL11FromEq20_28 (k := k) L)
          (gqrAQTallL21FromEq20_28 L)
          (gqrAQTallL22FromEq20_28 L) i j =
        gqrAQTallBlockAssoc (k := k) L i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun i : Fin (k + p) =>
        gqrAQBlock
            (gqrAQTallL11FromEq20_28 (k := k) L)
            (gqrAQTallL21FromEq20_28 L)
            (gqrAQTallL22FromEq20_28 L) (Fin.castAdd q i) j =
          gqrAQTallBlockAssoc (k := k) L (Fin.castAdd q i) j)
      ?zeroRows ?middleRows i
    · intro i
      refine Fin.addCases
        (motive := fun j : Fin (p + q) =>
          gqrAQBlock
              (gqrAQTallL11FromEq20_28 (k := k) L)
              (gqrAQTallL21FromEq20_28 L)
              (gqrAQTallL22FromEq20_28 L) (Fin.castAdd q (Fin.castAdd p i)) j =
            gqrAQTallBlockAssoc (k := k) L (Fin.castAdd q (Fin.castAdd p i)) j)
        (fun j => by
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28])
        (fun j => by
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28])
        j
    · intro i
      refine Fin.addCases
        (motive := fun j : Fin (p + q) =>
          gqrAQBlock
              (gqrAQTallL11FromEq20_28 (k := k) L)
              (gqrAQTallL21FromEq20_28 L)
              (gqrAQTallL22FromEq20_28 L) (Fin.castAdd q (Fin.natAdd k i)) j =
            gqrAQTallBlockAssoc (k := k) L (Fin.castAdd q (Fin.natAdd k i)) j)
        (fun j => by
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28])
        (fun j => by
          have hij : (Fin.castAdd q i).val < (Fin.natAdd p j).val :=
            Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right p j.val)
          have hzero := hL (Fin.castAdd q i) (Fin.natAdd p j) hij
          simp [gqrAQBlock, gqrAQTallBlockAssoc, gqrAQTallL11FromEq20_28,
            hzero])
        j
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin (p + q) =>
        gqrAQBlock
            (gqrAQTallL11FromEq20_28 (k := k) L)
            (gqrAQTallL21FromEq20_28 L)
            (gqrAQTallL22FromEq20_28 L) (Fin.natAdd (k + p) i) j =
          gqrAQTallBlockAssoc (k := k) L (Fin.natAdd (k + p) i) j)
      (fun j => by
        simp [gqrAQBlock, gqrAQTallBlockAssoc,
          gqrAQTallL21FromEq20_28])
      (fun j => by
        simp [gqrAQBlock, gqrAQTallBlockAssoc,
          gqrAQTallL22FromEq20_28])
      j
/-- Matrix form of the tall (20.27)-to-(20.28) reconstruction. If the leading
`k` rows of `L11` vanish and the reconstructed bottom block is lower
triangular, then the raw (20.27) matrix is the associated-row `[0; L]` block
from (20.28). -/
theorem gqrAQBlock_tall_eq20_28_matrix_of_top_zero {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22) := by
  refine ⟨hlower, ?_⟩
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin ((k + p) + q) =>
      gqrAQBlock L11 L21 L22 i j =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22) i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun i : Fin (k + p) =>
        gqrAQBlock L11 L21 L22 (Fin.castAdd q i) j =
          gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22)
            (Fin.castAdd q i) j)
      ?zeroRows ?middleRows i
    · intro i
      refine Fin.addCases
        (motive := fun j : Fin (p + q) =>
          gqrAQBlock L11 L21 L22 (Fin.castAdd q (Fin.castAdd p i)) j =
            gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22)
              (Fin.castAdd q (Fin.castAdd p i)) j)
        ?left ?right j
      · intro j
        unfold gqrAQBlock gqrAQTallBlockAssoc
        simp [Fin.append_left, hzero i j]
      · intro j
        unfold gqrAQBlock gqrAQTallBlockAssoc
        simp [Fin.append_left, Fin.append_right]
    · intro i
      unfold gqrAQBlock gqrAQTallBlockAssoc gqrAQTallLFromEq20_27
      simp [Fin.append_left, Fin.append_right]
  · intro i
    unfold gqrAQBlock gqrAQTallBlockAssoc gqrAQTallLFromEq20_27
    simp [Fin.append_left, Fin.append_right]
/-- Tall (20.28) matrix reconstruction from source-shaped block conditions:
    the leading `k` rows vanish, the trailing `p` rows of `L11` are lower
    triangular, and `L22` is lower triangular. -/
theorem gqrAQBlock_tall_eq20_28_matrix_of_top_zero_blocks {k p q : ℕ}
    (L11 : Fin (k + p) → Fin p → ℝ) (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, L11 (Fin.castAdd p i) j = 0)
    (hL11 : ∀ i j : Fin p, i.val < j.val →
      L11 (Fin.natAdd k i) j = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 L11 L21 L22) := by
  exact gqrAQBlock_tall_eq20_28_matrix_of_top_zero L11 L21 L22 hzero
    (gqrAQTallLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)
/-- Associated-column version of the wide (20.28) block `[X L]` with column
type `Fin ((k + r) + q)`, matching the column association of (20.27) when
`p = k + r`. -/
noncomputable def gqrAQWideBlockAssoc {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin ((k + r) + q) → ℝ :=
  fun i =>
    Fin.append
      (Fin.append (X i) (fun j : Fin r => L i (Fin.castAdd q j)))
      (fun j : Fin q => L i (Fin.natAdd r j))
/-- Leading `X` block extracted from an associated-column wide matrix in
    Higham's Chapter 20 display (20.28). -/
def gqrAQWideAssocX {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    Fin (r + q) → Fin k → ℝ :=
  fun i j => M i (Fin.castAdd q (Fin.castAdd r j))
/-- Trailing square `L` block extracted from an associated-column wide matrix in
    Higham's Chapter 20 display (20.28). -/
def gqrAQWideAssocL {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    Fin (r + q) → Fin (r + q) → ℝ :=
  fun i j =>
    Fin.addCases
      (motive := fun _ : Fin (r + q) => ℝ)
      (fun a : Fin r => M i (Fin.castAdd q (Fin.natAdd k a)))
      (fun b : Fin q => M i (Fin.natAdd (k + r) b)) j
/-- Any associated-column wide matrix is recovered from its leading block and
    trailing square block.  Thus, for the wide case of (20.28), only
    lower-triangularity of the trailing block is a real shape condition. -/
theorem gqrAQWideBlockAssoc_extract_eq {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    M = gqrAQWideBlockAssoc (gqrAQWideAssocX M) (gqrAQWideAssocL M) := by
  ext i j
  unfold gqrAQWideBlockAssoc gqrAQWideAssocX gqrAQWideAssocL
  refine Fin.addCases ?_ ?_ j
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp [Fin.append_left]
    · intro j
      simp [Fin.append_left, Fin.append_right]
  · intro j
    simp [Fin.append_right]
/-- Extracting the trailing associated-column wide block commutes with a square
    left multiplication. -/
theorem gqrAQWideAssocL_matMulRectLeft {k r q : ℕ}
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    gqrAQWideAssocL (matMulRectLeft U M) =
      matMulRectLeft U (gqrAQWideAssocL M) := by
  ext i j
  unfold gqrAQWideAssocL matMulRectLeft
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp
  · intro j
    simp
/-- Vector-action form of the associated-column wide (20.28) block `[X L]`,
    matching the column association used by (20.27). -/
theorem gqrAQWideBlockAssoc_mulVec {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ)
    (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrAQWideBlockAssoc X L) (Fin.append (Fin.append y0 y1) y2) =
      fun i : Fin (r + q) =>
        rectMatMulVec X y0 i + rectMatMulVec L (Fin.append y1 y2) i := by
  ext i
  simp [rectMatMulVec, gqrAQWideBlockAssoc, Fin.sum_univ_add, add_assoc]
/-- Higham, 2nd ed., Chapter 20, equation (20.28), associated-column wide-case
    shape for `U^T A Q = [X L]` in the column association used by (20.27).

    This records the exact displayed block shape once the transformed matrix is
    supplied. It does not construct the orthogonal factors. -/
structure GQRAQWideAssocCase (k r q : ℕ)
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) where
  /-- Leading block `X`. -/
  X : Fin (r + q) → Fin k → ℝ
  /-- Lower-triangular square block `L`. -/
  L : Fin (r + q) → Fin (r + q) → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [X L]` with associated columns. -/
  aq_eq : M = gqrAQWideBlockAssoc X L
/-- Wide associated-shape constructor for Higham's Chapter 20 display (20.28):
    once the trailing extracted square block is lower triangular, the matrix has
    the required `[X L]` associated-column shape. -/
def GQRAQWideAssocCase.of_trailing_lower {k r q : ℕ}
    {M : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    (hL : IsLowerTriangular (gqrAQWideAssocL M)) :
    GQRAQWideAssocCase k r q M :=
  ⟨gqrAQWideAssocX M, gqrAQWideAssocL M, hL,
    gqrAQWideBlockAssoc_extract_eq M⟩
/-- Wide associated-shape construction from a QR transform of the column-reversed
    trailing square block.  This removes the abstract associated-shape assumption
    for the wide branch of Higham's Chapter 20 GQR construction whenever that
    square QR route is supplied. -/
theorem GQRAQWideAssocCase.exists_of_trailing_qr_reversed_cols {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ)
    (V R : Fin (r + q) → Fin (r + q) → ℝ)
    (hV : IsOrthogonal (r + q) V)
    (hR : IsUpperTriangular (r + q) R)
    (hqr : matMulRectLeft (matTranspose V)
        (rectPermuteCols Fin.revPerm (gqrAQWideAssocL M)) = R) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQWideAssocCase k r q
          (matMulRectLeft (matTranspose U) M)) := by
  rcases exists_orthogonal_gqrReverseSquare_of_qr_reversed_cols
      (gqrAQWideAssocL M) V R hV hR hqr with
    ⟨U, hU, htrail, hLower⟩
  refine ⟨U, hU, ?_⟩
  have hExtract :
      gqrAQWideAssocL (matMulRectLeft (matTranspose U) M) =
        gqrReverseSquare R := by
    rw [gqrAQWideAssocL_matMulRectLeft]
    exact htrail
  refine ⟨GQRAQWideAssocCase.of_trailing_lower ?_⟩
  rw [hExtract]
  exact hLower
/-- Exact-MGS version of
    `GQRAQWideAssocCase.exists_of_trailing_qr_reversed_cols`: nonzero MGS
    stages for the column-reversed trailing square block construct the
    orthogonal `U` and the wide associated `[X L]` shape. -/
theorem GQRAQWideAssocCase.exists_of_trailing_mgs_reversed_cols {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ)
    (hdiag : ∀ j : Fin (r + q),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (rectPermuteCols Fin.revPerm (gqrAQWideAssocL M)) j.val j) ≠ 0) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQWideAssocCase k r q
          (matMulRectLeft (matTranspose U) M)) := by
  rcases exists_orthogonal_gqrReverseSquare_of_mgs_reversed_cols
      (gqrAQWideAssocL M) hdiag with
    ⟨U, R, hU, _hRupper, htrail, hLower⟩
  refine ⟨U, hU, ?_⟩
  have hExtract :
      gqrAQWideAssocL (matMulRectLeft (matTranspose U) M) =
        gqrReverseSquare R := by
    rw [gqrAQWideAssocL_matMulRectLeft]
    exact htrail
  refine ⟨GQRAQWideAssocCase.of_trailing_lower ?_⟩
  rw [hExtract]
  exact hLower
/-- Wide associated-shape construction from exact Householder QR of the
    column-reversed trailing square block.

    This is the rank-tolerant analogue of
    `GQRAQWideAssocCase.exists_of_trailing_mgs_reversed_cols`: zero active
    columns are handled by the exact Householder recursion instead of exposed
    as nonbreakdown hypotheses. -/
theorem GQRAQWideAssocCase.exists_of_trailing_exact_householder_reversed_cols
    {k r q : ℕ}
    (M : Fin (r + q) → Fin ((k + r) + q) → ℝ) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQWideAssocCase k r q
          (matMulRectLeft (matTranspose U) M)) := by
  let C : Fin (r + q) → Fin (r + q) → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQWideAssocL M)
  exact GQRAQWideAssocCase.exists_of_trailing_qr_reversed_cols
    M
    (exactHouseholderQR_Q (r + q) C)
    (exactHouseholderQR_R (r + q) C)
    (by
      simpa [C] using exactHouseholderQR_Q_orthogonal (r + q) C)
    (by
      simpa [C] using exactHouseholderQR_R_upper (r + q) C)
    (by
      simpa [C] using
        (exactHouseholderQR_R_eq_matMulRectLeft_transpose_Q (r + q) C).symm)
/-- Vector-action form of a supplied associated-column wide (20.28) shape. -/
theorem GQRAQWideAssocCase.mulVec_eq {k r q : ℕ}
    {M : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    (h : GQRAQWideAssocCase k r q M)
    (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec M (Fin.append (Fin.append y0 y1) y2) =
      fun i : Fin (r + q) =>
        rectMatMulVec h.X y0 i + rectMatMulVec h.L (Fin.append y1 y2) i := by
  rcases h with ⟨X, L, _lowerL, hM⟩
  subst M
  simpa using gqrAQWideBlockAssoc_mulVec X L y0 y1 y2
/-- Wide (20.28)-to-(20.27) extraction: the `L11` block induced by a supplied
    `[X L]` shape. Its first `k` columns come from `X`, and its trailing `r`
    columns come from the leading columns of `L`. -/
noncomputable def gqrAQWideL11FromEq20_28 {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin r → Fin (k + r) → ℝ :=
  fun i : Fin r =>
    Fin.append
      (X (Fin.castAdd q i))
      (fun j : Fin r => L (Fin.castAdd q i) (Fin.castAdd q j))
/-- Wide (20.28)-to-(20.27) extraction: the `L21` block induced by a supplied
    `[X L]` shape. -/
noncomputable def gqrAQWideL21FromEq20_28 {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin q → Fin (k + r) → ℝ :=
  fun i : Fin q =>
    Fin.append
      (X (Fin.natAdd r i))
      (fun j : Fin r => L (Fin.natAdd r i) (Fin.castAdd q j))
/-- Wide (20.28)-to-(20.27) extraction: the trailing `L22` block induced by a
    supplied `[X L]` shape. -/
noncomputable def gqrAQWideL22FromEq20_28 {r q : ℕ}
    (L : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin q → Fin q → ℝ :=
  fun i : Fin q => fun j : Fin q => L (Fin.natAdd r i) (Fin.natAdd r j)
/-- The trailing `L22` block extracted from a lower-triangular wide-case
    (20.28) block is lower triangular. -/
theorem gqrAQWideL22FromEq20_28_lowerTriangular {r q : ℕ}
    {L : Fin (r + q) → Fin (r + q) → ℝ}
    (hL : IsLowerTriangular L) :
    IsLowerTriangular (gqrAQWideL22FromEq20_28 L) := by
  intro i j hij
  unfold gqrAQWideL22FromEq20_28
  exact hL (Fin.natAdd r i) (Fin.natAdd r j) (by simpa using hij)
/-- Wide-case reverse block packaging: extracting `L11`, `L21`, and `L22`
    from a supplied (20.28) `[X L]` shape gives the (20.27) `UᵀAQ` block.

    Lower-triangularity of `L` supplies the top-right zero block in (20.27).
    This is the algebraic direction needed by the construction route in
    Theorem 20.9 after an orthogonal `U` has been supplied with
    `Uᵀ(AQ) = [X L]`. It does not construct `U`. -/
theorem gqrAQBlock_eq_wideBlockAssoc_of_eq20_28 {k r q : ℕ}
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ)
    (hL : IsLowerTriangular L) :
    gqrAQBlock
        (gqrAQWideL11FromEq20_28 X L)
        (gqrAQWideL21FromEq20_28 X L)
        (gqrAQWideL22FromEq20_28 L) =
      gqrAQWideBlockAssoc X L := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      gqrAQBlock
          (gqrAQWideL11FromEq20_28 X L)
          (gqrAQWideL21FromEq20_28 X L)
          (gqrAQWideL22FromEq20_28 L) i j =
        gqrAQWideBlockAssoc X L i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock
            (gqrAQWideL11FromEq20_28 X L)
            (gqrAQWideL21FromEq20_28 X L)
            (gqrAQWideL22FromEq20_28 L) (Fin.castAdd q i) j =
          gqrAQWideBlockAssoc X L (Fin.castAdd q i) j)
      ?topLeftCols ?topRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock
              (gqrAQWideL11FromEq20_28 X L)
              (gqrAQWideL21FromEq20_28 X L)
              (gqrAQWideL22FromEq20_28 L) (Fin.castAdd q i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc X L (Fin.castAdd q i) (Fin.castAdd q j))
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL11FromEq20_28])
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL11FromEq20_28])
        j
    · intro j
      have hij : (Fin.castAdd q i).val < (Fin.natAdd r j).val :=
        Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right r j.val)
      have hzero := hL (Fin.castAdd q i) (Fin.natAdd r j) hij
      simp [gqrAQBlock, gqrAQWideBlockAssoc, hzero]
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock
            (gqrAQWideL11FromEq20_28 X L)
            (gqrAQWideL21FromEq20_28 X L)
            (gqrAQWideL22FromEq20_28 L) (Fin.natAdd r i) j =
          gqrAQWideBlockAssoc X L (Fin.natAdd r i) j)
      ?bottomLeftCols ?bottomRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock
              (gqrAQWideL11FromEq20_28 X L)
              (gqrAQWideL21FromEq20_28 X L)
              (gqrAQWideL22FromEq20_28 L) (Fin.natAdd r i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc X L (Fin.natAdd r i) (Fin.castAdd q j))
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL21FromEq20_28])
        (fun j => by
          simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL21FromEq20_28])
        j
    · intro j
      simp [gqrAQBlock, gqrAQWideBlockAssoc, gqrAQWideL22FromEq20_28]
/-- Matrix form of the wide (20.27)-to-(20.28) reconstruction. If the
reconstructed trailing block is lower triangular, then the raw (20.27) matrix is
the associated-column `[X L]` block from (20.28). -/
theorem gqrAQBlock_wide_eq20_28_matrix {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 L11 L21)
          (gqrAQWideLFromEq20_27 L11 L21 L22) := by
  refine ⟨hlower, ?_⟩
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      gqrAQBlock L11 L21 L22 i j =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 L11 L21)
          (gqrAQWideLFromEq20_27 L11 L21 L22) i j)
    ?topRows ?bottomRows i
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock L11 L21 L22 (Fin.castAdd q i) j =
          gqrAQWideBlockAssoc
            (gqrAQWideXFromEq20_27 L11 L21)
            (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.castAdd q i) j)
      ?topLeftCols ?topRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock L11 L21 L22 (Fin.castAdd q i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc
              (gqrAQWideXFromEq20_27 L11 L21)
              (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.castAdd q i)
              (Fin.castAdd q j))
        ?topXCols ?topLCols j
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideXFromEq20_27
        simp [Fin.append_left]
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
        simp [Fin.append_left, Fin.append_right]
    · intro j
      unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
      simp [Fin.append_left, Fin.append_right]
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin ((k + r) + q) =>
        gqrAQBlock L11 L21 L22 (Fin.natAdd r i) j =
          gqrAQWideBlockAssoc
            (gqrAQWideXFromEq20_27 L11 L21)
            (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.natAdd r i) j)
      ?bottomLeftCols ?bottomRightCols j
    · intro j
      refine Fin.addCases
        (motive := fun j : Fin (k + r) =>
          gqrAQBlock L11 L21 L22 (Fin.natAdd r i) (Fin.castAdd q j) =
            gqrAQWideBlockAssoc
              (gqrAQWideXFromEq20_27 L11 L21)
              (gqrAQWideLFromEq20_27 L11 L21 L22) (Fin.natAdd r i)
              (Fin.castAdd q j))
        ?bottomXCols ?bottomLCols j
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideXFromEq20_27
        simp [Fin.append_left, Fin.append_right]
      · intro j
        unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
        simp [Fin.append_left, Fin.append_right]
    · intro j
      unfold gqrAQBlock gqrAQWideBlockAssoc gqrAQWideLFromEq20_27
      simp [Fin.append_left, Fin.append_right]
/-- Wide (20.28) matrix reconstruction from source-shaped block conditions:
    the trailing `r` columns of `L11` and `L22` have the displayed
    lower-triangular patterns. -/
theorem gqrAQBlock_wide_eq20_28_matrix_of_blocks {k r q : ℕ}
    (L11 : Fin r → Fin (k + r) → ℝ) (L21 : Fin q → Fin (k + r) → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hL11 : ∀ i j : Fin r, i.val < j.val →
      L11 i (Fin.natAdd k j) = 0)
    (hL22 : IsLowerTriangular L22) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 L11 L21 L22) ∧
      gqrAQBlock L11 L21 L22 =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 L11 L21)
          (gqrAQWideLFromEq20_27 L11 L21 L22) := by
  exact gqrAQBlock_wide_eq20_28_matrix L11 L21 L22
    (gqrAQWideLFromEq20_27_lowerTriangular_of_blocks L11 L21 L22 hL11 hL22)
/-- Higham, 2nd ed., Chapter 20, equation (20.28), tall case `m ≥ n`:
    the displayed block `[0; L]`, with `k = m - n` zero rows. -/
noncomputable def gqrAQTallBlock {k n : ℕ}
    (L : Fin n → Fin n → ℝ) : Fin (k + n) → Fin n → ℝ :=
  Fin.append (fun _ : Fin k => fun _ : Fin n => 0) L
/-- Matrix-vector multiplication by the tall (20.28) block `[0; L]`. -/
theorem gqrAQTallBlock_mulVec {k n : ℕ}
    (L : Fin n → Fin n → ℝ) (y : Fin n → ℝ) :
    rectMatMulVec (gqrAQTallBlock L) y =
      Fin.append (0 : Fin k → ℝ) (rectMatMulVec L y) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (k + n) =>
      rectMatMulVec (gqrAQTallBlock L) y i =
        Fin.append (0 : Fin k → ℝ) (rectMatMulVec L y) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec gqrAQTallBlock
    rw [Fin.append_left, Fin.append_left]
    simp
  · intro i
    unfold rectMatMulVec gqrAQTallBlock
    rw [Fin.append_right, Fin.append_right]
/-- Higham, 2nd ed., Chapter 20, equation (20.28), wide case `m < n`:
    the displayed block `[X L]`, with `k = n - m` leading columns. -/
noncomputable def gqrAQWideBlock {k m : ℕ}
    (X : Fin m → Fin k → ℝ) (L : Fin m → Fin m → ℝ) :
    Fin m → Fin (k + m) → ℝ :=
  fun i => Fin.append (X i) (L i)
/-- Matrix-vector multiplication by the wide (20.28) block `[X L]`. -/
theorem gqrAQWideBlock_mulVec {k m : ℕ}
    (X : Fin m → Fin k → ℝ) (L : Fin m → Fin m → ℝ)
    (y1 : Fin k → ℝ) (y2 : Fin m → ℝ) :
    rectMatMulVec (gqrAQWideBlock X L) (Fin.append y1 y2) =
      fun i : Fin m => rectMatMulVec X y1 i + rectMatMulVec L y2 i := by
  ext i
  unfold rectMatMulVec gqrAQWideBlock
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Higham, 2nd ed., Chapter 20, equation (20.28), supplied tall-case
    shape for `U^T A Q = [0; L]`.

    This records the exact displayed block shape once the matrix has already
    been supplied; it does not construct the orthogonal factors. -/
structure GQRAQTallCase (k n : ℕ)
    (M : Fin (k + n) → Fin n → ℝ) where
  /-- Lower-triangular square block `L`. -/
  L : Fin n → Fin n → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [0; L]`. -/
  aq_eq : M = gqrAQTallBlock L
/-- Vector-action form of a supplied tall (20.28) shape. -/
theorem GQRAQTallCase.mulVec_eq {k n : ℕ}
    {M : Fin (k + n) → Fin n → ℝ}
    (h : GQRAQTallCase k n M) (y : Fin n → ℝ) :
    rectMatMulVec M y =
      Fin.append (0 : Fin k → ℝ) (rectMatMulVec h.L y) := by
  rcases h with ⟨L, _lowerL, hM⟩
  subst M
  simpa using gqrAQTallBlock_mulVec L y
/-- Tall associated-shape construction from a QR factorization of the
    column-reversed block.  If
    `rectPermuteCols Fin.revPerm C = Q2 R` with orthonormal `Q2` columns and
    upper-triangular `R`, then a completed square orthogonal `U` sends the
    original block `C` to `[0; gqrReverseSquare R]`.

    This strengthened form also returns the exact bottom-column placement of
    the completion, needed later to identify transformed right-hand sides in the
    rounded `A Q₂` path.

    This is the small-block row/column orientation step needed for the
    oracle-recommended `A Q₂` route in Higham's Chapter 20 GQR construction. -/
theorem GQRAQTallCase.exists_of_qr_reversed_cols_with_bottom_reversed_columns
    {r q : ℕ}
    (C : Fin (r + q) → Fin q → ℝ)
    (Q2 : Fin (r + q) → Fin q → ℝ)
    (R : Fin q → Fin q → ℝ)
    (hQ2 : GramSchmidtOrthonormalColumns Q2)
    (hR : IsUpperTriangular q R)
    (hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect (r + q) q q Q2 R) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        (∀ i j, U i (Fin.natAdd r j) = Q2 i (Fin.rev j)) ∧
        Nonempty (GQRAQTallCase r q (matMulRectLeft (matTranspose U) C)) := by
  rcases exists_orthogonal_completion_bottom_reversed_columns Q2 hQ2 with
    ⟨U, hU, hUbottom⟩
  let L : Fin q → Fin q → ℝ := gqrReverseSquare R
  refine
    ⟨U, hU, hUbottom,
      ⟨⟨L, gqrReverseSquare_lowerTriangular_of_upper hR, ?_⟩⟩⟩
  ext row col
  have hC : ∀ i : Fin (r + q),
      C i col = ∑ k : Fin q, Q2 i k * R k (Fin.rev col) := by
    intro i
    have hentry := congrFun (congrFun hfactor i) (Fin.rev col)
    simpa [rectPermuteCols, matMulRect] using hentry
  have hsum_rearrange : ∀ a : Fin (r + q),
      (∑ i : Fin (r + q),
          U i a * (∑ k : Fin q, Q2 i k * R k (Fin.rev col))) =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i a * Q2 i k) * R k (Fin.rev col) := by
    intro a
    calc
      (∑ i : Fin (r + q),
          U i a * (∑ k : Fin q, Q2 i k * R k (Fin.rev col)))
          =
        ∑ i : Fin (r + q), ∑ k : Fin q,
          U i a * (Q2 i k * R k (Fin.rev col)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ =
        ∑ k : Fin q, ∑ i : Fin (r + q),
          U i a * (Q2 i k * R k (Fin.rev col)) := by
            rw [Finset.sum_comm]
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i a * Q2 i k) * R k (Fin.rev col) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
  refine Fin.addCases
    (motive := fun row : Fin (r + q) =>
      matMulRectLeft (matTranspose U) C row col =
        gqrAQTallBlock (k := r) L row col)
    ?topRows ?bottomRows row
  · intro row
    have htail_orth : ∀ k : Fin q,
        (∑ i : Fin (r + q), U i (Fin.castAdd q row) * Q2 i k) = 0 := by
      intro k
      have hne :
          Fin.castAdd q row ≠ Fin.natAdd r (Fin.rev k) := by
        intro h
        have hval := congrArg Fin.val h
        have hrle : r ≤ row.val := by
          calc
            r ≤ r + (Fin.rev k).val := Nat.le_add_right r (Fin.rev k).val
            _ = row.val := hval.symm
        exact (Nat.not_le_of_gt row.isLt) hrle
      have hpreserve : ∀ i : Fin (r + q),
          U i (Fin.natAdd r (Fin.rev k)) = Q2 i k := by
        intro i
        simpa using hUbottom i (Fin.rev k)
      calc
        (∑ i : Fin (r + q), U i (Fin.castAdd q row) * Q2 i k)
            =
          ∑ i : Fin (r + q),
            U i (Fin.castAdd q row) * U i (Fin.natAdd r (Fin.rev k)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hpreserve i]
        _ = 0 := by
              simpa [hne] using
                hU.col_orthonormal (Fin.castAdd q row)
                  (Fin.natAdd r (Fin.rev k))
    calc
      matMulRectLeft (matTranspose U) C (Fin.castAdd q row) col
          =
        ∑ i : Fin (r + q), U i (Fin.castAdd q row) * C i col := by
            simp [matMulRectLeft, matTranspose]
      _ =
        ∑ i : Fin (r + q),
          U i (Fin.castAdd q row) *
            (∑ k : Fin q, Q2 i k * R k (Fin.rev col)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hC i]
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i (Fin.castAdd q row) * Q2 i k) *
            R k (Fin.rev col) := hsum_rearrange (Fin.castAdd q row)
      _ = 0 := by
            simp [htail_orth]
      _ = gqrAQTallBlock (k := r) L (Fin.castAdd q row) col := by
            simp [gqrAQTallBlock]
  · intro row
    have hpreserve : ∀ i : Fin (r + q),
        U i (Fin.natAdd r row) = Q2 i (Fin.rev row) := by
      intro i
      exact hUbottom i row
    calc
      matMulRectLeft (matTranspose U) C (Fin.natAdd r row) col
          =
        ∑ i : Fin (r + q), U i (Fin.natAdd r row) * C i col := by
            simp [matMulRectLeft, matTranspose]
      _ =
        ∑ i : Fin (r + q),
          U i (Fin.natAdd r row) *
            (∑ k : Fin q, Q2 i k * R k (Fin.rev col)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hC i]
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), U i (Fin.natAdd r row) * Q2 i k) *
            R k (Fin.rev col) := hsum_rearrange (Fin.natAdd r row)
      _ =
        ∑ k : Fin q,
          (∑ i : Fin (r + q), Q2 i (Fin.rev row) * Q2 i k) *
            R k (Fin.rev col) := by
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [hpreserve i]
      _ =
        ∑ k : Fin q, idMatrix q (Fin.rev row) k * R k (Fin.rev col) := by
            apply Finset.sum_congr rfl
            intro k _
            have horth :
                (∑ i : Fin (r + q), Q2 i (Fin.rev row) * Q2 i k) =
                  idMatrix q (Fin.rev row) k := by
              simpa [GramSchmidtOrthonormalColumns, rectangularGram] using
                hQ2 (Fin.rev row) k
            rw [horth]
      _ = R (Fin.rev row) (Fin.rev col) := by
            simp [idMatrix]
      _ = gqrAQTallBlock (k := r) L (Fin.natAdd r row) col := by
            simp [gqrAQTallBlock, L, gqrReverseSquare]
/-- Tall associated-shape construction from a QR factorization of the
    column-reversed block.  If
    `rectPermuteCols Fin.revPerm C = Q2 R` with orthonormal `Q2` columns and
    upper-triangular `R`, then a completed square orthogonal `U` sends the
    original block `C` to `[0; gqrReverseSquare R]`.

    This is the public shape-only wrapper around
    `GQRAQTallCase.exists_of_qr_reversed_cols_with_bottom_reversed_columns`. -/
theorem GQRAQTallCase.exists_of_qr_reversed_cols {r q : ℕ}
    (C : Fin (r + q) → Fin q → ℝ)
    (Q2 : Fin (r + q) → Fin q → ℝ)
    (R : Fin q → Fin q → ℝ)
    (hQ2 : GramSchmidtOrthonormalColumns Q2)
    (hR : IsUpperTriangular q R)
    (hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect (r + q) q q Q2 R) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQTallCase r q (matMulRectLeft (matTranspose U) C)) := by
  rcases
    GQRAQTallCase.exists_of_qr_reversed_cols_with_bottom_reversed_columns
      C Q2 R hQ2 hR hfactor with
    ⟨U, hU, _hUbottom, hCase⟩
  exact ⟨U, hU, hCase⟩
/-- Tall associated-shape construction from a square orthogonal QR-style
    factorization of the column-reversed rectangular block.

    Rounded Householder panels naturally produce a square orthogonal matrix
    `Qfull` and an upper-trapezoidal rectangular `Rhat`.  This helper extracts
    the thin top square factor and reuses
    `GQRAQTallCase.exists_of_qr_reversed_cols_with_bottom_reversed_columns` to
    obtain the GQR-oriented `[0;L]` shape and the concrete bottom-column
    placement of the completed `U`. -/
theorem GQRAQTallCase.exists_of_square_qr_reversed_cols_with_bottom_reversed_columns
    {r q : ℕ}
    (C : Fin (r + q) → Fin q → ℝ)
    (Qfull : Fin (r + q) → Fin (r + q) → ℝ)
    (Rhat : Fin (r + q) → Fin q → ℝ)
    (hQfull : IsOrthogonal (r + q) Qfull)
    (hRhat : IsUpperTrapezoidal (r + q) q Rhat)
    (hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect (r + q) (r + q) q Qfull Rhat) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        (∀ i j, U i (Fin.natAdd r j) =
          Qfull i
            (Fin.cast (Nat.add_comm q r) (Fin.castAdd r (Fin.rev j)))) ∧
        Nonempty (GQRAQTallCase r q (matMulRectLeft (matTranspose U) C)) := by
  let e : Fin (r + q) ≃ Fin (q + r) := finAddCommEquiv r q
  let C' : Fin (q + r) → Fin q → ℝ := fun i j => C (e.symm i) j
  let Qfull' : Fin (q + r) → Fin (q + r) → ℝ :=
    fun i j => Qfull (e.symm i) (e.symm j)
  let Rhat' : Fin (q + r) → Fin q → ℝ := fun i j => Rhat (e.symm i) j
  let Q2' : Fin (q + r) → Fin q → ℝ :=
    fun i j => Qfull' i (Fin.castAdd r j)
  let R : Fin q → Fin q → ℝ := fun i j => Rhat' (Fin.castAdd r i) j
  have hQfull' : IsOrthogonal (q + r) Qfull' := by
    simpa [Qfull'] using
      IsOrthogonal.reindexRowsColsEquiv (e := e.symm) hQfull
  have hRhat' : IsUpperTrapezoidal (q + r) q Rhat' := by
    intro i j hji
    have hval : j.val < (e.symm i).val := by
      simpa [e, finAddCommEquiv, Fin.cast] using hji
    simpa [Rhat'] using hRhat (e.symm i) j hval
  have hQ2' : GramSchmidtOrthonormalColumns Q2' := by
    intro a b
    simpa [Q2', Qfull', GramSchmidtOrthonormalColumns, rectangularGram,
      idMatrix, Fin.castAdd] using
      hQfull'.col_orthonormal (Fin.castAdd r a) (Fin.castAdd r b)
  have hR : IsUpperTriangular q R := by
    intro i j hji
    simpa [R, Rhat', Fin.castAdd] using hRhat' (Fin.castAdd r i) j hji
  have hfactor' :
      rectPermuteCols Fin.revPerm C' =
        matMulRect (q + r) (q + r) q Qfull' Rhat' := by
    ext i j
    have hentry := congrFun (congrFun hfactor (e.symm i)) j
    have hsum :
        (∑ k : Fin (q + r), Qfull (e.symm i) (e.symm k) *
            Rhat (e.symm k) j) =
          ∑ k : Fin (r + q), Qfull (e.symm i) k * Rhat k j := by
      exact Equiv.sum_comp e.symm
        (fun k : Fin (r + q) => Qfull (e.symm i) k * Rhat k j)
    simpa [C', Qfull', Rhat', rectPermuteCols, matMulRect, hsum] using hentry
  have hthin' :
      rectPermuteCols Fin.revPerm C' = matMulRect (q + r) q q Q2' R := by
    rw [hfactor']
    ext i j
    have hbottom : ∀ c : Fin r, Rhat' (Fin.natAdd q c) j = 0 := by
      intro c
      exact hRhat' (Fin.natAdd q c) j
        (Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right q c.val))
    unfold matMulRect Q2' R
    rw [Fin.sum_univ_add]
    simp [hbottom]
  let Q2 : Fin (r + q) → Fin q → ℝ := fun i j => Q2' (e i) j
  have hQ2 : GramSchmidtOrthonormalColumns Q2 := by
    intro a b
    unfold rectangularGram Q2
    calc
      (∑ i : Fin (r + q), Q2' (e i) a * Q2' (e i) b)
          = ∑ i' : Fin (q + r), Q2' i' a * Q2' i' b := by
              exact Equiv.sum_comp e
                (fun i' : Fin (q + r) => Q2' i' a * Q2' i' b)
      _ = idMatrix q a b := hQ2' a b
  have hthin :
      rectPermuteCols Fin.revPerm C = matMulRect (r + q) q q Q2 R := by
    ext i j
    have hentry := congrFun (congrFun hthin' (e i)) j
    simpa [C', Q2, rectPermuteCols, matMulRect] using hentry
  rcases
    GQRAQTallCase.exists_of_qr_reversed_cols_with_bottom_reversed_columns
      C Q2 R hQ2 hR hthin with
    ⟨U, hU, hUbottom, hCase⟩
  refine ⟨U, hU, ?_, hCase⟩
  intro i j
  have h := hUbottom i j
  simpa [Q2, Q2', Qfull', e, finAddCommEquiv] using h
/-- Tall associated-shape construction from a square orthogonal QR-style
    factorization of the column-reversed rectangular block.

    Rounded Householder panels naturally produce a square orthogonal matrix
    `Qfull` and an upper-trapezoidal rectangular `Rhat`.  This helper extracts
    the thin top square factor and reuses
    `GQRAQTallCase.exists_of_qr_reversed_cols` to obtain the GQR-oriented
    `[0;L]` shape. -/
theorem GQRAQTallCase.exists_of_square_qr_reversed_cols {r q : ℕ}
    (C : Fin (r + q) → Fin q → ℝ)
    (Qfull : Fin (r + q) → Fin (r + q) → ℝ)
    (Rhat : Fin (r + q) → Fin q → ℝ)
    (hQfull : IsOrthogonal (r + q) Qfull)
    (hRhat : IsUpperTrapezoidal (r + q) q Rhat)
    (hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect (r + q) (r + q) q Qfull Rhat) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQTallCase r q (matMulRectLeft (matTranspose U) C)) := by
  rcases
    GQRAQTallCase.exists_of_square_qr_reversed_cols_with_bottom_reversed_columns
      C Qfull Rhat hQfull hRhat hfactor with
    ⟨U, hU, _hUbottom, hCase⟩
  exact ⟨U, hU, hCase⟩
/-- Tall associated-shape construction from exact Householder QR of the
    column-reversed block.

    Unlike the exact-MGS wrapper, this route is rank-tolerant for the
    transformed block: zero active columns are handled by the exact Householder
    panel recursion rather than exposed as nonbreakdown hypotheses. -/
theorem GQRAQTallCase.exists_of_exact_householder_reversed_cols {r q : ℕ}
    (C : Fin (r + q) → Fin q → ℝ) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQTallCase r q (matMulRectLeft (matTranspose U) C)) := by
  let e : Fin (r + q) ≃ Fin (q + r) := finAddCommEquiv r q
  let C' : Fin (q + r) → Fin q → ℝ := fun i j => C (e.symm i) j
  let Crev : Fin (q + r) → Fin q → ℝ := rectPermuteCols Fin.revPerm C'
  let Qfull : Fin (q + r) → Fin (q + r) → ℝ :=
    exactHouseholderQRPanel_Q (q + r) q Crev
  let Rhat : Fin (q + r) → Fin q → ℝ :=
    exactHouseholderQRPanel_R (q + r) q Crev
  let Q2' : Fin (q + r) → Fin q → ℝ :=
    fun i j => Qfull i (Fin.castAdd r j)
  let R : Fin q → Fin q → ℝ :=
    fun i j => Rhat (Fin.castAdd r i) j
  have hQfull : IsOrthogonal (q + r) Qfull := by
    simpa [Qfull] using exactHouseholderQRPanel_Q_orthogonal (q + r) q Crev
  have hRhatUpper : IsUpperTrapezoidal (q + r) q Rhat := by
    simpa [Rhat] using exactHouseholderQRPanel_R_upper_trapezoidal (q + r) q Crev
  have hQ2' : GramSchmidtOrthonormalColumns Q2' := by
    intro a b
    simpa [Q2', GramSchmidtOrthonormalColumns, rectangularGram, idMatrix,
      Fin.castAdd] using
      hQfull.col_orthonormal (Fin.castAdd r a) (Fin.castAdd r b)
  have hR : IsUpperTriangular q R := by
    intro i j hji
    simpa [R, Fin.castAdd] using
      hRhatUpper (Fin.castAdd r i) j hji
  have hRhatEq :
      Rhat = matMulRectLeft (matTranspose Qfull) Crev := by
    simpa [Qfull, Rhat, Crev] using
      exactHouseholderQRPanel_R_eq_matMulRectLeft_transpose_Q
        (q + r) q Crev
  have hCrevFull : Crev = matMulRectLeft Qfull Rhat := by
    have hright :
        matMul (q + r) Qfull (matTranspose Qfull) = idMatrix (q + r) := by
      ext i j
      exact hQfull.right_inv i j
    calc
      Crev = matMulRectLeft (idMatrix (q + r)) Crev := by
          exact (matMulRectLeft_id Crev).symm
      _ = matMulRectLeft (matMul (q + r) Qfull (matTranspose Qfull)) Crev := by
          rw [hright]
      _ = matMulRectLeft Qfull (matMulRectLeft (matTranspose Qfull) Crev) := by
          rw [matMulRectLeft_assoc]
      _ = matMulRectLeft Qfull Rhat := by
          rw [← hRhatEq]
  have hThin' : Crev = matMulRect (q + r) q q Q2' R := by
    rw [hCrevFull]
    ext i j
    have hbottom : ∀ c : Fin r, Rhat (Fin.natAdd q c) j = 0 := by
      intro c
      exact hRhatUpper (Fin.natAdd q c) j
        (Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right q c.val))
    unfold matMulRectLeft matMulRect Q2' R
    rw [Fin.sum_univ_add]
    simp [hbottom]
  let Q2 : Fin (r + q) → Fin q → ℝ := fun i j => Q2' (e i) j
  have hQ2 : GramSchmidtOrthonormalColumns Q2 := by
    intro a b
    unfold rectangularGram Q2
    calc
      (∑ i : Fin (r + q), Q2' (e i) a * Q2' (e i) b)
          = ∑ i' : Fin (q + r), Q2' i' a * Q2' i' b := by
              exact Equiv.sum_comp e
                (fun i' : Fin (q + r) => Q2' i' a * Q2' i' b)
      _ = idMatrix q a b := hQ2' a b
  have hfactor :
      rectPermuteCols Fin.revPerm C = matMulRect (r + q) q q Q2 R := by
    ext i j
    have hentry := congrFun (congrFun hThin' (e i)) j
    simpa [Crev, C', Q2, rectPermuteCols, matMulRect] using hentry
  exact GQRAQTallCase.exists_of_qr_reversed_cols C Q2 R hQ2 hR hfactor
/-- Associated-row tall (20.28) construction from a QR factorization of the
    column-reversed block.  This is the same construction as
    `GQRAQTallCase.exists_of_qr_reversed_cols`, transported across the finite
    row associativity equivalence from `k + (p + q)` to `((k + p) + q)`. -/
theorem GQRAQTallAssocCase.exists_of_qr_reversed_cols {k p q : ℕ}
    (C : Fin ((k + p) + q) → Fin (p + q) → ℝ)
    (Q2 : Fin ((k + p) + q) → Fin (p + q) → ℝ)
    (R : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ2 : GramSchmidtOrthonormalColumns Q2)
    (hR : IsUpperTriangular (p + q) R)
    (hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect ((k + p) + q) (p + q) (p + q) Q2 R) :
    ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
      IsOrthogonal ((k + p) + q) U ∧
        Nonempty (GQRAQTallAssocCase k p q
          (matMulRectLeft (matTranspose U) C)) := by
  let e : Fin ((k + p) + q) ≃ Fin (k + (p + q)) :=
    finAddAssocEquiv k p q
  let C' : Fin (k + (p + q)) → Fin (p + q) → ℝ :=
    fun i j => C (e.symm i) j
  let Q2' : Fin (k + (p + q)) → Fin (p + q) → ℝ :=
    fun i j => Q2 (e.symm i) j
  have hQ2' : GramSchmidtOrthonormalColumns Q2' :=
    GramSchmidtOrthonormalColumns.reindexRowsEquiv e hQ2
  have hfactor' :
      rectPermuteCols Fin.revPerm C' =
        matMulRect (k + (p + q)) (p + q) (p + q) Q2' R := by
    ext i j
    have hentry := congrFun (congrFun hfactor (e.symm i)) j
    simpa [C', Q2', rectPermuteCols, matMulRect] using hentry
  rcases GQRAQTallCase.exists_of_qr_reversed_cols
      (r := k) (q := p + q) C' Q2' R hQ2' hR hfactor' with
    ⟨U', hU', hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ :=
    fun i j => U' (e i) (e j)
  refine ⟨U, IsOrthogonal.reindexRowsColsEquiv e hU', ?_⟩
  refine ⟨⟨hCase.L, hCase.lowerL, ?_⟩⟩
  ext row col
  have hrow_eq :
      matMulRectLeft (matTranspose U) C row col =
        matMulRectLeft (matTranspose U') C' (e row) col := by
    calc
      matMulRectLeft (matTranspose U) C row col
          = ∑ i : Fin ((k + p) + q), U' (e i) (e row) * C i col := by
              simp [matMulRectLeft, matTranspose, U]
      _ = ∑ i' : Fin (k + (p + q)), U' i' (e row) * C (e.symm i') col := by
              exact Equiv.sum_comp e
                (fun i' : Fin (k + (p + q)) =>
                  U' i' (e row) * C (e.symm i') col)
      _ = matMulRectLeft (matTranspose U') C' (e row) col := by
              simp [matMulRectLeft, matTranspose, C']
  have hblock_eq :
      gqrAQTallBlock hCase.L (e row) col =
        gqrAQTallBlockAssoc (k := k) hCase.L row col := by
    refine Fin.addCases
      (motive := fun row : Fin ((k + p) + q) =>
        gqrAQTallBlock hCase.L (e row) col =
          gqrAQTallBlockAssoc (k := k) hCase.L row col)
      ?topRows ?bottomRows row
    · intro row
      refine Fin.addCases
        (motive := fun row : Fin (k + p) =>
          gqrAQTallBlock hCase.L (e (Fin.castAdd q row)) col =
            gqrAQTallBlockAssoc (k := k) hCase.L (Fin.castAdd q row) col)
        ?zeroRows ?middleRows row
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.castAdd p row)) =
              Fin.castAdd (p + q) row := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.natAdd k row)) =
              Fin.natAdd k (Fin.castAdd q row) := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.natAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
    · intro row
      have heq :
          e (Fin.natAdd (k + p) row) =
            Fin.natAdd k (Fin.natAdd p row) := by
        ext
        simp [e, finAddAssocEquiv, Fin.natAdd, Fin.cast, Nat.add_assoc]
      rw [heq]
      simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
  calc
    matMulRectLeft (matTranspose U) C row col
        = matMulRectLeft (matTranspose U') C' (e row) col := hrow_eq
    _ = gqrAQTallBlock hCase.L (e row) col := by
          simpa using congrFun (congrFun hCase.aq_eq (e row)) col
    _ = gqrAQTallBlockAssoc (k := k) hCase.L row col := hblock_eq
/-- Exact-Householder associated-row tall (20.28) construction.

    This is the rank-tolerant analogue of
    `GQRAQTallAssocCase.exists_of_mgs_reversed_cols`: the associated-row
    display is constructed from the exact Householder QR panel recursion,
    whose zero-column branch avoids any MGS nonbreakdown hypothesis on the
    transformed `AQ` block. -/
theorem GQRAQTallAssocCase.exists_of_exact_householder_reversed_cols {k p q : ℕ}
    (C : Fin ((k + p) + q) → Fin (p + q) → ℝ) :
    ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
      IsOrthogonal ((k + p) + q) U ∧
        Nonempty (GQRAQTallAssocCase k p q
          (matMulRectLeft (matTranspose U) C)) := by
  let e : Fin ((k + p) + q) ≃ Fin (k + (p + q)) :=
    finAddAssocEquiv k p q
  let C' : Fin (k + (p + q)) → Fin (p + q) → ℝ :=
    fun i j => C (e.symm i) j
  rcases GQRAQTallCase.exists_of_exact_householder_reversed_cols
      (r := k) (q := p + q) C' with
    ⟨U', hU', hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ :=
    fun i j => U' (e i) (e j)
  refine ⟨U, IsOrthogonal.reindexRowsColsEquiv e hU', ?_⟩
  refine ⟨⟨hCase.L, hCase.lowerL, ?_⟩⟩
  ext row col
  have hrow_eq :
      matMulRectLeft (matTranspose U) C row col =
        matMulRectLeft (matTranspose U') C' (e row) col := by
    calc
      matMulRectLeft (matTranspose U) C row col
          = ∑ i : Fin ((k + p) + q), U' (e i) (e row) * C i col := by
              simp [matMulRectLeft, matTranspose, U]
      _ = ∑ i' : Fin (k + (p + q)), U' i' (e row) * C (e.symm i') col := by
              exact Equiv.sum_comp e
                (fun i' : Fin (k + (p + q)) =>
                  U' i' (e row) * C (e.symm i') col)
      _ = matMulRectLeft (matTranspose U') C' (e row) col := by
              simp [matMulRectLeft, matTranspose, C']
  have hblock_eq :
      gqrAQTallBlock hCase.L (e row) col =
        gqrAQTallBlockAssoc (k := k) hCase.L row col := by
    refine Fin.addCases
      (motive := fun row : Fin ((k + p) + q) =>
        gqrAQTallBlock hCase.L (e row) col =
          gqrAQTallBlockAssoc (k := k) hCase.L row col)
      ?topRows ?bottomRows row
    · intro row
      refine Fin.addCases
        (motive := fun row : Fin (k + p) =>
          gqrAQTallBlock hCase.L (e (Fin.castAdd q row)) col =
            gqrAQTallBlockAssoc (k := k) hCase.L (Fin.castAdd q row) col)
        ?zeroRows ?middleRows row
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.castAdd p row)) =
              Fin.castAdd (p + q) row := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
      · intro row
        have heq :
            e (Fin.castAdd q (Fin.natAdd k row)) =
              Fin.natAdd k (Fin.castAdd q row) := by
          ext
          simp [e, finAddAssocEquiv, Fin.castAdd, Fin.natAdd, Fin.cast]
        rw [heq]
        simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
    · intro row
      have heq :
          e (Fin.natAdd (k + p) row) =
            Fin.natAdd k (Fin.natAdd p row) := by
        ext
        simp [e, finAddAssocEquiv, Fin.natAdd, Fin.cast, Nat.add_assoc]
      rw [heq]
      simp [gqrAQTallBlock, gqrAQTallBlockAssoc]
  calc
    matMulRectLeft (matTranspose U) C row col
        = matMulRectLeft (matTranspose U') C' (e row) col := hrow_eq
    _ = gqrAQTallBlock hCase.L (e row) col := by
          simpa using congrFun (congrFun hCase.aq_eq (e row)) col
    _ = gqrAQTallBlockAssoc (k := k) hCase.L row col := hblock_eq
/-- Exact-MGS associated-row tall (20.28) construction.  Nonzero exact-MGS
    stages for the column-reversed full block supply the QR factorization used
    by `GQRAQTallAssocCase.exists_of_qr_reversed_cols`. -/
theorem GQRAQTallAssocCase.exists_of_mgs_reversed_cols {k p q : ℕ}
    (C : Fin ((k + p) + q) → Fin (p + q) → ℝ)
    (hdiag : ∀ j : Fin (p + q),
      gsColumnNorm2
        (modifiedGramSchmidtVectors (rectPermuteCols Fin.revPerm C) j.val j) ≠ 0) :
    ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
      IsOrthogonal ((k + p) + q) U ∧
        Nonempty (GQRAQTallAssocCase k p q
          (matMulRectLeft (matTranspose U) C)) := by
  let Crev : Fin ((k + p) + q) → Fin (p + q) → ℝ :=
    rectPermuteCols Fin.revPerm C
  let Q2 : Fin ((k + p) + q) → Fin (p + q) → ℝ :=
    modifiedGramSchmidtQ Crev
  let R : Fin (p + q) → Fin (p + q) → ℝ :=
    modifiedGramSchmidtR Crev
  have hQ2 : GramSchmidtOrthonormalColumns Q2 :=
    modifiedGramSchmidtQ_orthonormal_columns Crev hdiag
  have hR : IsUpperTriangular (p + q) R :=
    IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal Crev)
  have hfactor : rectPermuteCols Fin.revPerm C =
      matMulRect ((k + p) + q) (p + q) (p + q) Q2 R := by
    exact modifiedGramSchmidt_exact_factorization Crev hdiag
  exact GQRAQTallAssocCase.exists_of_qr_reversed_cols C Q2 R hQ2 hR hfactor
/-- Higham, 2nd ed., Chapter 20, equation (20.28), supplied wide-case
    shape for `U^T A Q = [X L]`.

    This records the exact displayed block shape once the matrix has already
    been supplied; it does not construct the orthogonal factors. -/
structure GQRAQWideCase (k m : ℕ)
    (M : Fin m → Fin (k + m) → ℝ) where
  /-- Leading block `X`. -/
  X : Fin m → Fin k → ℝ
  /-- Lower-triangular square block `L`. -/
  L : Fin m → Fin m → ℝ
  /-- Source triangularity condition on `L`. -/
  lowerL : IsLowerTriangular L
  /-- Source block identity `M = [X L]`. -/
  aq_eq : M = gqrAQWideBlock X L
/-- Vector-action form of a supplied wide (20.28) shape. -/
theorem GQRAQWideCase.mulVec_eq {k m : ℕ}
    {M : Fin m → Fin (k + m) → ℝ}
    (h : GQRAQWideCase k m M)
    (y1 : Fin k → ℝ) (y2 : Fin m → ℝ) :
    rectMatMulVec M (Fin.append y1 y2) =
      fun i : Fin m => rectMatMulVec h.X y1 i + rectMatMulVec h.L y2 i := by
  rcases h with ⟨X, L, _lowerL, hM⟩
  subst M
  simpa using gqrAQWideBlock_mulVec X L y1 y2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, exact generalized QR
    factorization data for the block form (20.27).

    This structure records the source factorization shape once the orthogonal
    factors and blocks have been supplied.  It is not the existence theorem for
    GQR, and it does not assert the nonsingularity equivalence from (20.24);
    those remain separate source rows. -/
structure GeneralizedQRFactorization (r p q : ℕ)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) where
  /-- Right orthogonal factor `Q ∈ R^{n×n}`, with `n = p+q`. -/
  Q : Fin (p + q) → Fin (p + q) → ℝ
  /-- Left orthogonal factor `U ∈ R^{m×m}`, with `m = r+q`. -/
  U : Fin (r + q) → Fin (r + q) → ℝ
  /-- Top-left block of `U^T A Q`. -/
  L11 : Fin r → Fin p → ℝ
  /-- Bottom-left block of `U^T A Q`. -/
  L21 : Fin q → Fin p → ℝ
  /-- Bottom-right lower-triangular block of `U^T A Q`. -/
  L22 : Fin q → Fin q → ℝ
  /-- Lower-triangular factor in `B Q = [S 0]`. -/
  S : Fin p → Fin p → ℝ
  /-- `Q` is orthogonal. -/
  orthQ : IsOrthogonal (p + q) Q
  /-- `U` is orthogonal. -/
  orthU : IsOrthogonal (r + q) U
  /-- Source block identity `U^T A Q = [[L11, 0], [L21, L22]]`. -/
  aq_eq :
    matMulRectLeft (matTranspose U)
      (matMulRect (r + q) (p + q) (p + q) A Q) =
        gqrAQBlock L11 L21 L22
  /-- Source block identity `B Q = [S, 0]`. -/
  bq_eq :
    matMulRect p (p + q) (p + q) B Q = gqrBQBlock S
  /-- `L22` is lower triangular. -/
  lowerL22 : IsLowerTriangular L22
  /-- `S` is lower triangular. -/
  lowerS : IsLowerTriangular S
/-- Source matrix obtained by transporting a supplied GQR transformed `A`
    block back through orthogonal factors `U` and `Q`.

    By construction, if `U` and `Q` are orthogonal then
    `Uᵀ * (gqrSourceAFromBlocks Q U L11 L21 L22) * Q =
    [[L11,0],[L21,L22]]`. -/
noncomputable def gqrSourceAFromBlocks {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    Fin (r + q) → Fin (p + q) → ℝ :=
  matMulRectLeft U
    (matMulRectRight (gqrAQBlock L11 L21 L22) (matTranspose Q))
/-- Source constraint matrix obtained by transporting a supplied GQR constraint
    block `[S,0]` back through the orthogonal factor `Q`. -/
noncomputable def gqrSourceBFromBlocks {p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S : Fin p → Fin p → ℝ) :
    Fin p → Fin (p + q) → ℝ :=
  matMulRectRight (gqrBQBlock S) (matTranspose Q)
/-- Exact GQR factorization built by transporting supplied transformed blocks
    back to source coordinates.

    This is the algebraic constructor behind the Theorem 20.10 supplied-factor
    route: once perturbed triangular blocks are provided, they define source
    matrices whose GQR factors are exactly those blocks.  It does not assert
    that those source matrices are small perturbations of a previously given
    `A` or `B`; that is a separate finite-precision bound. -/
noncomputable def GeneralizedQRFactorization.of_source_blocks
    {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (S : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hL22 : IsLowerTriangular L22)
    (hS : IsLowerTriangular S) :
    GeneralizedQRFactorization r p q
      (gqrSourceAFromBlocks Q U L11 L21 L22)
      (gqrSourceBFromBlocks Q S) := by
  let M : Fin (r + q) → Fin (p + q) → ℝ := gqrAQBlock L11 L21 L22
  let C : Fin p → Fin (p + q) → ℝ := gqrBQBlock S
  have hQtQ : rectMatMul (matTranspose Q) Q = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hQ.left_inv i j
  have hUtU : rectMatMul (matTranspose U) U = idMatrix (r + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hMQ :
      rectMatMul (rectMatMul M (matTranspose Q)) Q = M := by
    calc
      rectMatMul (rectMatMul M (matTranspose Q)) Q =
          rectMatMul M (rectMatMul (matTranspose Q) Q) :=
            rectMatMul_assoc M (matTranspose Q) Q
      _ = rectMatMul M (idMatrix (p + q)) := by rw [hQtQ]
      _ = M := rectMatMul_id_right M
  have hCQ :
      rectMatMul (rectMatMul C (matTranspose Q)) Q = C := by
    calc
      rectMatMul (rectMatMul C (matTranspose Q)) Q =
          rectMatMul C (rectMatMul (matTranspose Q) Q) :=
            rectMatMul_assoc C (matTranspose Q) Q
      _ = rectMatMul C (idMatrix (p + q)) := by rw [hQtQ]
      _ = C := rectMatMul_id_right C
  have hAqQ :
      matMulRect (r + q) (p + q) (p + q)
          (gqrSourceAFromBlocks Q U L11 L21 L22) Q =
        matMulRectLeft U M := by
    calc
      matMulRect (r + q) (p + q) (p + q)
          (gqrSourceAFromBlocks Q U L11 L21 L22) Q =
          rectMatMul
            (rectMatMul U (rectMatMul M (matTranspose Q))) Q := by
            ext i j
            rfl
      _ = rectMatMul U (rectMatMul (rectMatMul M (matTranspose Q)) Q) :=
            rectMatMul_assoc U (rectMatMul M (matTranspose Q)) Q
      _ = rectMatMul U M := by rw [hMQ]
      _ = matMulRectLeft U M := by
            rfl
  refine
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := S
      orthQ := hQ
      orthU := hU
      aq_eq := ?_
      bq_eq := ?_
      lowerL22 := hL22
      lowerS := hS }
  · calc
      matMulRectLeft (matTranspose U)
          (matMulRect (r + q) (p + q) (p + q)
            (gqrSourceAFromBlocks Q U L11 L21 L22) Q) =
          matMulRectLeft (matTranspose U) (matMulRectLeft U M) := by
            rw [hAqQ]
      _ = rectMatMul (matTranspose U) (rectMatMul U M) := by
            rfl
      _ = rectMatMul (rectMatMul (matTranspose U) U) M :=
            (rectMatMul_assoc (matTranspose U) U M).symm
      _ = rectMatMul (idMatrix (r + q)) M := by rw [hUtU]
      _ = M := rectMatMul_id_left M
      _ = gqrAQBlock L11 L21 L22 := rfl
  · calc
      matMulRect p (p + q) (p + q) (gqrSourceBFromBlocks Q S) Q =
          rectMatMul (rectMatMul C (matTranspose Q)) Q := by
            ext i j
            rfl
      _ = C := hCQ
      _ = gqrBQBlock S := rfl
/-- Exact GQR factorization built from transported `A` blocks and an already
    established constraint identity.

    This is the asymmetric constructor needed by the rounded Theorem 20.10
    path: the `A` side may still be transported from supplied/computed blocks,
    while the `B` side can come from a concrete QR-derived identity
    `B Q = [S,0]` instead of from the synthetic source matrix
    `gqrSourceBFromBlocks Q S`. -/
noncomputable def GeneralizedQRFactorization.of_sourceA_blocks_and_constraint_block
    {r p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (S : Fin p → Fin p → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hL22 : IsLowerTriangular L22)
    (hS : IsLowerTriangular S)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S) :
    GeneralizedQRFactorization r p q
      (gqrSourceAFromBlocks Q U L11 L21 L22) B := by
  let M : Fin (r + q) → Fin (p + q) → ℝ := gqrAQBlock L11 L21 L22
  have hQtQ : rectMatMul (matTranspose Q) Q = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hQ.left_inv i j
  have hUtU : rectMatMul (matTranspose U) U = idMatrix (r + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hMQ :
      rectMatMul (rectMatMul M (matTranspose Q)) Q = M := by
    calc
      rectMatMul (rectMatMul M (matTranspose Q)) Q =
          rectMatMul M (rectMatMul (matTranspose Q) Q) :=
            rectMatMul_assoc M (matTranspose Q) Q
      _ = rectMatMul M (idMatrix (p + q)) := by rw [hQtQ]
      _ = M := rectMatMul_id_right M
  have hAqQ :
      matMulRect (r + q) (p + q) (p + q)
          (gqrSourceAFromBlocks Q U L11 L21 L22) Q =
        matMulRectLeft U M := by
    calc
      matMulRect (r + q) (p + q) (p + q)
          (gqrSourceAFromBlocks Q U L11 L21 L22) Q =
          rectMatMul
            (rectMatMul U (rectMatMul M (matTranspose Q))) Q := by
            ext i j
            rfl
      _ = rectMatMul U (rectMatMul (rectMatMul M (matTranspose Q)) Q) :=
            rectMatMul_assoc U (rectMatMul M (matTranspose Q)) Q
      _ = rectMatMul U M := by rw [hMQ]
      _ = matMulRectLeft U M := by
            rfl
  refine
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := S
      orthQ := hQ
      orthU := hU
      aq_eq := ?_
      bq_eq := hBQ
      lowerL22 := hL22
      lowerS := hS }
  calc
    matMulRectLeft (matTranspose U)
        (matMulRect (r + q) (p + q) (p + q)
          (gqrSourceAFromBlocks Q U L11 L21 L22) Q) =
        matMulRectLeft (matTranspose U) (matMulRectLeft U M) := by
          rw [hAqQ]
    _ = rectMatMul (matTranspose U) (rectMatMul U M) := by
          rfl
    _ = rectMatMul (rectMatMul (matTranspose U) U) M :=
          (rectMatMul_assoc (matTranspose U) U M).symm
    _ = rectMatMul (idMatrix (r + q)) M := by rw [hUtU]
    _ = M := rectMatMul_id_left M
    _ = gqrAQBlock L11 L21 L22 := rfl
/-- Tall-case construction wrapper for Higham, 2nd ed., Theorem 20.9.

    Given the exact QR-derived constraint identity for `Bᵀ`, a supplied
    orthogonal `U` putting `AQ` into the tall (20.28) shape `[0; L]`, and
    lower-triangularity of that square `L`, this packages the corresponding
    (20.27) generalized-QR data. This is still a supplied-factor bridge: it
    does not construct the QR factorization of `Bᵀ` or the Householder product
    `U`. -/
theorem GeneralizedQRFactorization.exists_of_tall_qr_shapes {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (L : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hAQ : matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q) =
      gqrAQTallBlockAssoc (k := k) L)
    (hL : IsLowerTriangular L) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQTallL22FromEq20_28 L := by
  let L11 := gqrAQTallL11FromEq20_28 (k := k) L
  let L21 := gqrAQTallL21FromEq20_28 L
  let L22 := gqrAQTallL22FromEq20_28 L
  have hAQBlock : gqrAQBlock L11 L21 L22 = gqrAQTallBlockAssoc (k := k) L := by
    simpa [L11, L21, L22] using gqrAQBlock_eq_tallBlockAssoc_of_eq20_28
      (k := k) L hL
  have hBBlock :
      matMulRect p (p + q) (p + q) B Q = gqrBQBlock (matTranspose R) :=
    gqrBQBlock_eq_of_transpose_tall_qr B Q R hqrB
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := matTranspose R
      orthQ := hQ
      orthU := hU
      aq_eq := ?_
      bq_eq := hBBlock
      lowerL22 := gqrAQTallL22FromEq20_28_lowerTriangular hL
      lowerS := isLowerTriangular_matTranspose_of_isUpperTriangular hR },
    rfl, rfl, rfl, rfl⟩
  rw [hAQ, ← hAQBlock]
/-- Associated-row tall-case construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    This consumes a supplied associated-row (20.28) shape record for
    `Uᵀ(AQ) = [0; L]` and packages the corresponding (20.27) generalized-QR
    data. It still does not construct the QR factorization of `Bᵀ` or the
    orthogonal factor `U`. -/
theorem GeneralizedQRFactorization.exists_of_tall_qr_assoc_case {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hU : IsOrthogonal ((k + p) + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin (p + q) => fun i : Fin p => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular p R)
    (hCase : GQRAQTallAssocCase k p q
      (matMulRectLeft (matTranspose U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) :
    ∃ h : GeneralizedQRFactorization (k + p) p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQTallL22FromEq20_28 hCase.L := by
  exact GeneralizedQRFactorization.exists_of_tall_qr_shapes
    Q U R hCase.L hQ hU hqrB hR hCase.aq_eq hCase.lowerL
/-- Wide-case construction wrapper for Higham, 2nd ed., Theorem 20.9.

    Given the exact QR-derived constraint identity for `Bᵀ`, a supplied
    orthogonal `U` putting `AQ` into the wide (20.28) shape `[X L]`, and
    lower-triangularity of the trailing square `L`, this packages the
    corresponding (20.27) generalized-QR data. This is still a supplied-factor
    bridge: it does not construct the QR factorization of `Bᵀ` or the
    Householder product `U`. -/
theorem GeneralizedQRFactorization.exists_of_wide_qr_shapes {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (X : Fin (r + q) → Fin k → ℝ)
    (L : Fin (r + q) → Fin (r + q) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hAQ : matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q) =
      gqrAQWideBlockAssoc X L)
    (hL : IsLowerTriangular L) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQWideL22FromEq20_28 L := by
  let L11 := gqrAQWideL11FromEq20_28 X L
  let L21 := gqrAQWideL21FromEq20_28 X L
  let L22 := gqrAQWideL22FromEq20_28 L
  have hAQBlock : gqrAQBlock L11 L21 L22 = gqrAQWideBlockAssoc X L := by
    simpa [L11, L21, L22] using gqrAQBlock_eq_wideBlockAssoc_of_eq20_28
      X L hL
  have hBBlock :
      matMulRect (k + r) ((k + r) + q) ((k + r) + q) B Q =
        gqrBQBlock (matTranspose R) :=
    gqrBQBlock_eq_of_transpose_tall_qr B Q R hqrB
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := matTranspose R
      orthQ := hQ
      orthU := hU
      aq_eq := ?_
      bq_eq := hBBlock
      lowerL22 := gqrAQWideL22FromEq20_28_lowerTriangular hL
      lowerS := isLowerTriangular_matTranspose_of_isUpperTriangular hR },
    rfl, rfl, rfl, rfl⟩
  rw [hAQ, ← hAQBlock]
/-- Associated-column wide-case construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    This consumes a supplied associated-column (20.28) shape record for
    `Uᵀ(AQ) = [X L]` and packages the corresponding (20.27) generalized-QR
    data. It still does not construct the QR factorization of `Bᵀ` or the
    orthogonal factor `U`. -/
theorem GeneralizedQRFactorization.exists_of_wide_qr_assoc_case {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (R : Fin (k + r) → Fin (k + r) → ℝ)
    (hQ : IsOrthogonal ((k + r) + q) Q)
    (hU : IsOrthogonal (r + q) U)
    (hqrB : matMulRectLeft (matTranspose Q)
        (fun j : Fin ((k + r) + q) => fun i : Fin (k + r) => B i j) =
      lsQRTallBlock (k := q) R)
    (hR : IsUpperTriangular (k + r) R)
    (hCase : GQRAQWideAssocCase k r q
      (matMulRectLeft (matTranspose U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q))) :
    ∃ h : GeneralizedQRFactorization r (k + r) q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = matTranspose R ∧
        h.L22 = gqrAQWideL22FromEq20_28 hCase.L := by
  exact GeneralizedQRFactorization.exists_of_wide_qr_shapes
    Q U R hCase.X hCase.L hQ hU hqrB hR hCase.aq_eq hCase.lowerL
/-- Tall-case construction wrapper for Higham, 2nd ed., Theorem 20.9:
    exact MGS data for `Bᵀ` supplies the `B Q = [S 0]` side, so the only
    remaining supplied construction is an associated-row shape for `Uᵀ A Q`
    for the completed orthogonal `Q`. -/
theorem GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiag : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col) j.val j) ≠ 0)
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  rcases exists_gqr_constraint_block_of_mgs B hdiag with
    ⟨Q, S, hQorth, hSlower, hBQ⟩
  rcases hAQ Q hQorth with ⟨U, hUorth, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let L11 := gqrAQTallL11FromEq20_28 (k := k) hCase.L
  let L21 := gqrAQTallL21FromEq20_28 hCase.L
  let L22 := gqrAQTallL22FromEq20_28 hCase.L
  have hAQBlock :
      gqrAQBlock L11 L21 L22 =
        gqrAQTallBlockAssoc (k := k) hCase.L := by
    simpa [L11, L21, L22] using
      gqrAQBlock_eq_tallBlockAssoc_of_eq20_28 (k := k)
        hCase.L hCase.lowerL
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := S
      orthQ := hQorth
      orthU := hUorth
      aq_eq := ?_
      bq_eq := hBQ
      lowerL22 := gqrAQTallL22FromEq20_28_lowerTriangular hCase.lowerL
      lowerS := hSlower }⟩
  rw [hCase.aq_eq, ← hAQBlock]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 tall-case construction step:
    full row rank of `B` supplies the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the remaining supplied construction is the associated-row
    `[0; L]` shape for the actual transformed `A Q`. -/
theorem GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q)))) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ
/-- Tall-case exact-MGS construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    Exact MGS data for `Bᵀ` supplies the constraint side `B Q = [S 0]`.
    Exact MGS data for the column-reversed full transformed block `A Q`
    supplies the associated-row (20.28) display `Uᵀ A Q = [0; L]`. -/
theorem GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_full_mgs_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col) j.val j) ≠ 0)
    (hdiagAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∀ j : Fin (p + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) := by
    intro Q hQ
    exact GQRAQTallAssocCase.exists_of_mgs_reversed_cols
      (matMulRect ((k + p) + q) (p + q) (p + q) A Q)
      (hdiagAQ Q hQ)
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ
/-- Tall-case full-row-rank plus full-`AQ` exact-MGS construction wrapper for
    Higham, 2nd ed., Theorem 20.9.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the remaining explicit assumption is nonbreakdown for the
    column-reversed full transformed block `A Q`. -/
theorem GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_full_mgs_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hdiagAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∀ j : Fin (p + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_full_mgs_assoc_shape
      (A := A) (B := B) hdiagB hdiagAQ
/-- Tall-case exact-Householder construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    Exact MGS data for `Bᵀ` supplies the constraint side `B Q = [S 0]`.
    The associated-row (20.28) display for the full transformed block `A Q`
    is then constructed by exact Householder QR, without assuming exact-MGS
    nonbreakdown for that `AQ` block. -/
theorem GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_exact_householder_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col) j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hAQ : ∀ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q →
        ∃ U : Fin ((k + p) + q) → Fin ((k + p) + q) → ℝ,
          IsOrthogonal ((k + p) + q) U ∧
            Nonempty (
            GQRAQTallAssocCase k p q
              (matMulRectLeft (matTranspose U)
                (matMulRect ((k + p) + q) (p + q) (p + q) A Q))) := by
    intro Q _hQ
    exact GQRAQTallAssocCase.exists_of_exact_householder_reversed_cols
      (matMulRect ((k + p) + q) (p + q) (p + q) A Q)
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB hAQ
/-- Tall-case full-row-rank plus exact-Householder associated display wrapper
    for Higham, 2nd ed., Theorem 20.9.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; exact Householder QR constructs the associated-row display for
    `A Q` without a separate nonbreakdown hypothesis on `AQ`. -/
theorem GeneralizedQRFactorization.exists_of_tall_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B) :
    Nonempty (GeneralizedQRFactorization (k + p) p q A B) := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_tall_mgs_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hdiagB
/-- Wide-case construction wrapper for Higham, 2nd ed., Theorem 20.9:
    exact MGS data for `Bᵀ` supplies the `B Q = [S 0]` side, so the only
    remaining supplied construction is an associated-column shape for `Uᵀ A Q`
    for the completed orthogonal `Q`. -/
theorem GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiag : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0)
    (hAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
          IsOrthogonal (r + q) U ∧
            Nonempty (
            GQRAQWideAssocCase k r q
              (matMulRectLeft (matTranspose U)
                (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  rcases exists_gqr_constraint_block_of_mgs B hdiag with
    ⟨Q, S, hQorth, hSlower, hBQ⟩
  rcases hAQ Q hQorth with ⟨U, hUorth, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  let L11 := gqrAQWideL11FromEq20_28 hCase.X hCase.L
  let L21 := gqrAQWideL21FromEq20_28 hCase.X hCase.L
  let L22 := gqrAQWideL22FromEq20_28 hCase.L
  have hAQBlock :
      gqrAQBlock L11 L21 L22 =
        gqrAQWideBlockAssoc hCase.X hCase.L := by
    simpa [L11, L21, L22] using
      gqrAQBlock_eq_wideBlockAssoc_of_eq20_28 hCase.X hCase.L hCase.lowerL
  refine ⟨
    { Q := Q
      U := U
      L11 := L11
      L21 := L21
      L22 := L22
      S := S
      orthQ := hQorth
      orthU := hUorth
      aq_eq := ?_
      bq_eq := hBQ
      lowerL22 := gqrAQWideL22FromEq20_28_lowerTriangular hCase.lowerL
      lowerS := hSlower }⟩
  rw [hCase.aq_eq, ← hAQBlock]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 wide-case construction step:
    exact MGS data for `Bᵀ` supplies the constraint side, and exact MGS data
    for the column-reversed trailing square block of the actual transformed
    matrix `A Q` supplies the associated `[X L]` side. -/
theorem GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0)
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  refine
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB ?_
  intro Q hQorth
  exact GQRAQWideAssocCase.exists_of_trailing_mgs_reversed_cols
    (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)
    (hdiagAQ Q hQorth)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 wide-case construction step:
    full row rank of `B` supplies the exact-MGS nonbreakdown hypotheses for
    `Bᵀ`; the only remaining MGS nonbreakdown assumption is for the
    column-reversed trailing square block of the actual transformed `A Q`. -/
theorem GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_trailing_mgs_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hdiagAQ : ∀ Q : Fin ((k + r) + q) → Fin ((k + r) + q) → ℝ,
      IsOrthogonal ((k + r) + q) Q →
        ∀ j : Fin (r + q),
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm
                (gqrAQWideAssocL
                  (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)))
              j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  have hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_trailing_mgs_assoc_shape
      (A := A) (B := B) hdiagB hdiagAQ
/-- Wide-case exact-Householder construction wrapper for Higham, 2nd ed.,
    Theorem 20.9.

    Exact MGS data for `B^T` supplies the constraint side `B Q = [S 0]`.
    Exact Householder QR constructs the associated-column display for the full
    transformed block `A Q` without requiring exact-MGS nonbreakdown for the
    trailing square block. -/
theorem GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_exact_householder_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  refine
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_assoc_shape
      (A := A) (B := B) hdiagB ?_
  intro Q _hQ
  exact GQRAQWideAssocCase.exists_of_trailing_exact_householder_reversed_cols
    (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A Q)
/-- Wide-case full-row-rank plus exact-Householder associated display wrapper
    for Higham, 2nd ed., Theorem 20.9.

    Full row rank of `B` discharges the exact-MGS nonbreakdown hypotheses for
    `B^T`; exact Householder QR constructs the associated-column display for
    `A Q` without a separate nonbreakdown hypothesis on the trailing block. -/
theorem GeneralizedQRFactorization.exists_of_wide_fullRowRank_constraint_and_exact_householder_assoc_shape
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (hB : LSEFullRowRank B) :
    Nonempty (GeneralizedQRFactorization r (k + r) q A B) := by
  have hdiagB : ∀ j : Fin (k + r),
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin ((k + r) + q) => fun row : Fin (k + r) => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  exact
    GeneralizedQRFactorization.exists_of_wide_mgs_constraint_and_exact_householder_assoc_shape
      (A := A) (B := B) hdiagB
/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), tall case:
    a supplied `GeneralizedQRFactorization` connects the reconstructed
    `[0; L]` row action to the actual transformed matrix `U^T A Q`.

    This lifts `gqrAQBlock_tall_eq20_28_row_action_of_top_zero` from the raw
    block display to the stored orthogonal factors. It still assumes the
    top-zero and lower-triangular reconstruction hypotheses; it does not prove
    them from QR or construct the GQR factors. -/
theorem GeneralizedQRFactorization.tall_eq20_28_row_action_of_top_zero
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization (k + p) p q A B)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, h.L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin k),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.castAdd q (Fin.castAdd p i)) = 0) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin p),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.castAdd q (Fin.natAdd k i)) =
        rectMatMulVec (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)
          (Fin.append y1 y2) (Fin.castAdd q i)) ∧
      (∀ (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q))
            (Fin.append y1 y2)
          (Fin.natAdd (k + p) i) =
        rectMatMulVec (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)
          (Fin.append y1 y2) (Fin.natAdd p i)) := by
  have hlink :=
    gqrAQBlock_tall_eq20_28_row_action_of_top_zero
      h.L11 h.L21 h.L22 hzero hlower
  refine ⟨hlink.1, ?_, ?_, ?_⟩
  · intro y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.1 y1 y2 i
  · intro y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.2.1 y1 y2 i
  · intro y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.2.2 y1 y2 i
/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), wide case:
    a supplied `GeneralizedQRFactorization` connects the reconstructed
    `[X L]` row action to the actual transformed matrix `U^T A Q`.

    This lifts `gqrAQBlock_wide_eq20_28_row_action` from the raw block display
    to the stored orthogonal factors. It still assumes lower-triangularity of
    the reconstructed trailing block; it does not prove that hypothesis from
    QR or construct the GQR factors. -/
theorem GeneralizedQRFactorization.wide_eq20_28_row_action
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (h : GeneralizedQRFactorization r (k + r) q A B)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin r),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q))
            (Fin.append (Fin.append y0 y1) y2)
          (Fin.castAdd q i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 h.L11 h.L21) y0
            (Fin.castAdd q i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)
            (Fin.append y1 y2) (Fin.castAdd q i)) ∧
      (∀ (y0 : Fin k → ℝ) (y1 : Fin r → ℝ) (y2 : Fin q → ℝ) (i : Fin q),
        rectMatMulVec
            (matMulRectLeft (matTranspose h.U)
              (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q))
            (Fin.append (Fin.append y0 y1) y2)
          (Fin.natAdd r i) =
        rectMatMulVec (gqrAQWideXFromEq20_27 h.L11 h.L21) y0
            (Fin.natAdd r i) +
          rectMatMulVec (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)
            (Fin.append y1 y2) (Fin.natAdd r i)) := by
  have hlink := gqrAQBlock_wide_eq20_28_row_action h.L11 h.L21 h.L22 hlower
  refine ⟨hlink.1, ?_, ?_⟩
  · intro y0 y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.1 y0 y1 y2 i
  · intro y0 y1 y2 i
    rw [h.aq_eq]
    exact hlink.2.2 y0 y1 y2 i
/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), tall case:
    matrix form of the supplied-GQR reconstruction. Under the explicit
    top-zero and lower-triangular reconstruction hypotheses, the actual
    transformed matrix `U^T A Q` is the associated-row `[0; L]` block from
    (20.28). -/
theorem GeneralizedQRFactorization.tall_eq20_28_matrix_of_top_zero
    {k p q : ℕ}
    {A : Fin ((k + p) + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization (k + p) p q A B)
    (hzero : ∀ i : Fin k, ∀ j : Fin p, h.L11 (Fin.castAdd p i) j = 0)
    (hlower : IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) ∧
      matMulRectLeft (matTranspose h.U)
        (matMulRect ((k + p) + q) (p + q) (p + q) A h.Q) =
        gqrAQTallBlockAssoc (gqrAQTallLFromEq20_27 h.L11 h.L21 h.L22) := by
  have hlink :=
    gqrAQBlock_tall_eq20_28_matrix_of_top_zero
      h.L11 h.L21 h.L22 hzero hlower
  refine ⟨hlink.1, ?_⟩
  rw [h.aq_eq, hlink.2]
/-- Higham, 2nd ed., Chapter 20, equations (20.27)-(20.28), wide case:
    matrix form of the supplied-GQR reconstruction. Under the explicit
    lower-triangular reconstruction hypothesis, the actual transformed matrix
    `U^T A Q` is the associated-column `[X L]` block from (20.28). -/
theorem GeneralizedQRFactorization.wide_eq20_28_matrix
    {k r q : ℕ}
    {A : Fin (r + q) → Fin ((k + r) + q) → ℝ}
    {B : Fin (k + r) → Fin ((k + r) + q) → ℝ}
    (h : GeneralizedQRFactorization r (k + r) q A B)
    (hlower : IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22)) :
    IsLowerTriangular (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) ∧
      matMulRectLeft (matTranspose h.U)
        (matMulRect (r + q) ((k + r) + q) ((k + r) + q) A h.Q) =
        gqrAQWideBlockAssoc
          (gqrAQWideXFromEq20_27 h.L11 h.L21)
          (gqrAQWideLFromEq20_27 h.L11 h.L21 h.L22) := by
  have hlink := gqrAQBlock_wide_eq20_28_matrix h.L11 h.L21 h.L22 hlower
  refine ⟨hlink.1, ?_⟩
  rw [h.aq_eq, hlink.2]
/-- The constraint reduction used by the GQR method after (20.27):
    for `x = Q y` and `y = [y1; y2]`, the constraint becomes `S y1`. -/
theorem GeneralizedQRFactorization.constraint_eq {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec B (matMulVec (p + q) h.Q (Fin.append y1 y2)) =
      rectMatMulVec h.S y1 := by
  let y : Fin (p + q) → ℝ := Fin.append y1 y2
  calc
    rectMatMulVec B (matMulVec (p + q) h.Q y)
        = rectMatMulVec (rectMatMul B h.Q) y := by
            simpa [y, matMulVec] using
              (rectMatMulVec_rectMatMul B h.Q y).symm
    _ = rectMatMulVec (matMulRect p (p + q) (p + q) B h.Q) y := rfl
    _ = rectMatMulVec (gqrBQBlock h.S) y := by rw [h.bq_eq]
    _ = rectMatMulVec h.S y1 := by
            simpa [y] using gqrBQBlock_mulVec h.S y1 y2
/-- If the triangular system `S y1 = d` is solved, then `x = Q [y1; y2]`
    satisfies the original equality constraint `B x = d`. -/
theorem GeneralizedQRFactorization.feasible_of_S_mulVec {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {d : Fin p → ℝ} {y1 : Fin p → ℝ} {y2 : Fin q → ℝ}
    (hy1 : rectMatMulVec h.S y1 = d) :
    LSEFeasible B d (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  intro i
  have hc := congrFun (h.constraint_eq y1 y2) i
  rw [hc]
  exact congrFun hy1 i
/-- The transformed `A` action has exactly the block vector form displayed
    after (20.27). -/
theorem GeneralizedQRFactorization.transformed_A_mulVec_eq_block {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (Fin.append y1 y2) =
      Fin.append
        (rectMatMulVec h.L11 y1)
        (fun i : Fin q => rectMatMulVec h.L21 y1 i +
          rectMatMulVec h.L22 y2 i) := by
  calc
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (Fin.append y1 y2)
        = rectMatMulVec (gqrAQBlock h.L11 h.L21 h.L22)
            (Fin.append y1 y2) := by
            rw [h.aq_eq]
    _ = Fin.append
        (rectMatMulVec h.L11 y1)
        (fun i : Fin q => rectMatMulVec h.L21 y1 i +
          rectMatMulVec h.L22 y2 i) := by
            exact gqrAQBlock_mulVec h.L11 h.L21 h.L22 y1 y2
/-- The GQR change of variables preserves the least-squares objective:
    minimizing with `x = Q y` is equivalent to minimizing the transformed
    residual for `U^T A Q` and `U^T b`.

    This is exact algebra for the method following (20.27); it assumes supplied
    GQR data and does not assert Theorem 20.9's existence result. -/
theorem GeneralizedQRFactorization.objective_eq_transformed {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    lsObjective
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (matMulVec (r + q) (matTranspose h.U) b)
        (Fin.append y1 y2) =
      lsObjective A b (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  let y : Fin (p + q) → ℝ := Fin.append y1 y2
  calc
    lsObjective
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q))
        (matMulVec (r + q) (matTranspose h.U) b) y
        = lsObjective
            (matMulRect (r + q) (p + q) (p + q) A h.Q) b y := by
            exact lsObjective_matMulRectLeft_orthogonal
              (matTranspose h.U)
              (matMulRect (r + q) (p + q) (p + q) A h.Q)
              b y h.orthU.transpose
    _ = lsObjective A b (matMulVec (p + q) h.Q y) := by
            simpa [matMulVec, rectMatMulVec] using
              lsObjective_matMulRect_right (r + q) (p + q) (p + q)
                A h.Q b y
/-- Block-form version of `objective_eq_transformed`: after rewriting
    `U^T A Q` by the displayed GQR block in (20.27), the transformed objective
    is still the original objective at `x = Q [y1; y2]`. -/
theorem GeneralizedQRFactorization.objective_eq_block {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ)
    (y1 : Fin p → ℝ) (y2 : Fin q → ℝ) :
    lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
        (matMulVec (r + q) (matTranspose h.U) b)
        (Fin.append y1 y2) =
      lsObjective A b (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  rw [← h.aq_eq]
  exact h.objective_eq_transformed b y1 y2
private theorem matMulVec_orthogonal_mul_transpose {n : ℕ}
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
            rw [matMulVec_id]
private theorem matMulVec_orthogonal_transpose_mul {n : ℕ}
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrthogonal n Q)
    (x : Fin n → ℝ) :
    matMulVec n (matTranspose Q) (matMulVec n Q x) = x := by
  ext i
  calc
    matMulVec n (matTranspose Q) (matMulVec n Q x) i
        = matMulVec n (matMul n (matTranspose Q) Q) x i := by
            exact (matMulVec_matMul n (matTranspose Q) Q x i).symm
    _ = matMulVec n (idMatrix n) x i := by
            have hmat : matMul n (matTranspose Q) Q = idMatrix n := by
              ext a b
              exact hQ.left_inv a b
            rw [hmat]
    _ = x i := by
            rw [matMulVec_id]
private theorem matMulVec_zero {n : ℕ}
    (Q : Fin n → Fin n → ℝ) :
    matMulVec n Q (0 : Fin n → ℝ) = 0 := by
  ext i
  simp [matMulVec]
private theorem rectMatMulVec_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    rectMatMulVec A (0 : Fin n → ℝ) = 0 := by
  ext i
  simp [rectMatMulVec]
private theorem GeneralizedQRFactorization.transformed_A_action_eq
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y : Fin (p + q) → ℝ) :
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y =
      matMulVec (r + q) (matTranspose h.U)
        (rectMatMulVec A (matMulVec (p + q) h.Q y)) := by
  calc
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y
        = matMulVec (r + q) (matTranspose h.U)
            (rectMatMulVec
              (matMulRect (r + q) (p + q) (p + q) A h.Q) y) := by
            exact rectMatMulVec_matMulRectLeft
              (matTranspose h.U)
              (matMulRect (r + q) (p + q) (p + q) A h.Q) y
    _ = matMulVec (r + q) (matTranspose h.U)
        (rectMatMulVec A (matMulVec (p + q) h.Q y)) := by
            have hy :
                rectMatMulVec
                    (matMulRect (r + q) (p + q) (p + q) A h.Q) y =
                  rectMatMulVec A (matMulVec (p + q) h.Q y) := by
              simpa [matMulRect, matMulVec] using
                rectMatMulVec_rectMatMul A h.Q y
            rw [hy]
private theorem GeneralizedQRFactorization.transformed_A_zero_of_A_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {y : Fin (p + q) → ℝ}
    (hy : rectMatMulVec A (matMulVec (p + q) h.Q y) = 0) :
    rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y = 0 := by
  rw [h.transformed_A_action_eq y, hy]
  exact matMulVec_zero (matTranspose h.U)
private theorem GeneralizedQRFactorization.A_zero_of_transformed_A_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {y : Fin (p + q) → ℝ}
    (hy :
      rectMatMulVec
        (matMulRectLeft (matTranspose h.U)
          (matMulRect (r + q) (p + q) (p + q) A h.Q)) y = 0) :
    rectMatMulVec A (matMulVec (p + q) h.Q y) = 0 := by
  have haction := h.transformed_A_action_eq y
  rw [haction] at hy
  have hrecover :=
    matMulVec_orthogonal_mul_transpose h.orthU
      (rectMatMulVec A (matMulVec (p + q) h.Q y))
  rw [hy, matMulVec_zero] at hrecover
  exact hrecover.symm
private theorem finAppend_left_right {p q : ℕ}
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
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof:
    under the supplied GQR block identity `BQ = [S 0]`, injectivity of `S`
    identifies the nullspace of `B` with the `Q₂` coordinate range.

    This is the formal version of the source step
    `null(B) = range(Q₂)` after `S` is nonsingular.  It still assumes supplied
    GQR data and does not construct the orthogonal factors. -/
theorem GeneralizedQRFactorization.null_B_iff_exists_Q2_coord
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_inj : Function.Injective (rectMatMulVec h.S))
    (x : Fin (p + q) → ℝ) :
    rectMatMulVec B x = 0 ↔
      ∃ y2 : Fin q → ℝ,
        x = matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2) := by
  constructor
  · intro hBx
    let y : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) x
    let y1 : Fin p → ℝ := fun i => y (Fin.castAdd q i)
    let y2 : Fin q → ℝ := fun i => y (Fin.natAdd p i)
    have hy_append : Fin.append y1 y2 = y := by
      simpa [y1, y2] using finAppend_left_right (p := p) (q := q) y
    have hx_recover :
        matMulVec (p + q) h.Q (Fin.append y1 y2) = x := by
      rw [hy_append]
      exact matMulVec_orthogonal_mul_transpose h.orthQ x
    have hSy1 : rectMatMulVec h.S y1 = 0 := by
      have hc := h.constraint_eq y1 y2
      rw [hx_recover] at hc
      rw [hBx] at hc
      exact hc.symm
    have hy1_zero : y1 = 0 := by
      apply hS_inj
      rw [hSy1, rectMatMulVec_zero]
    refine ⟨y2, ?_⟩
    rw [← hx_recover, hy1_zero]
  · rintro ⟨y2, rfl⟩
    have hc := h.constraint_eq (0 : Fin p → ℝ) y2
    rw [hc]
    exact rectMatMulVec_zero h.S
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    the concrete matrix whose columns are the `Q₂` basis vectors for the
    supplied GQR factorization. -/
noncomputable def GeneralizedQRFactorization.Q2Basis
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Fin (p + q) → Fin q → ℝ :=
  fun i j =>
    matMulVec (p + q) h.Q
      (Fin.append (0 : Fin p → ℝ) (finiteBasisVec j)) i
/-- The concrete GQR `Q₂` basis lies in the nullspace of the constraint
    matrix `B`. -/
theorem GeneralizedQRFactorization.Q2Basis_nullspace
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    rectMatMul B h.Q2Basis =
      (fun _ : Fin p => fun _ : Fin q => 0) := by
  ext i j
  have hc := congrFun (h.constraint_eq (0 : Fin p → ℝ) (finiteBasisVec j)) i
  simpa [GeneralizedQRFactorization.Q2Basis, rectMatMul, rectMatMulVec]
    using hc
/-- Higham, 2nd ed., Chapter 20, equation (20.24) support:
    every source projector `P = I - B^+B` fixes the concrete GQR `Q₂` basis,
    because the `Q₂` columns lie in the nullspace of `B`. -/
theorem GeneralizedQRFactorization.theorem20_8Projection_mul_Q2Basis_eq_self
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (Bplus : Fin (p + q) → Fin p → ℝ) :
    rectMatMul (theorem20_8Projection B Bplus) h.Q2Basis = h.Q2Basis :=
  theorem20_8_APplus_projection_range_of_constraint_annihilates
    B Bplus h.Q2Basis h.Q2Basis_nullspace
/-- The concrete GQR `Q₂` basis acts by applying the full orthogonal `Q` to a
    vector with zero leading coordinates. -/
theorem GeneralizedQRFactorization.Q2Basis_mulVec
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y : Fin q → ℝ) :
    rectMatMulVec h.Q2Basis y =
      matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y) := by
  ext i
  unfold GeneralizedQRFactorization.Q2Basis rectMatMulVec matMulVec
  have hinner : ∀ x : Fin q,
      (∑ j : Fin (p + q), h.Q i j * Fin.append 0 (finiteBasisVec x) j) =
        h.Q i (Fin.natAdd p x) := by
    intro x
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, finiteBasisVec]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, hinner]
/-- The concrete GQR `Q₂` basis is an isometry on coefficient vectors. -/
theorem GeneralizedQRFactorization.Q2Basis_vecNorm2
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y : Fin q → ℝ) :
    vecNorm2 (rectMatMulVec h.Q2Basis y) = vecNorm2 y := by
  rw [h.Q2Basis_mulVec y]
  rw [vecNorm2_orthogonal h.Q (Fin.append (0 : Fin p → ℝ) y) h.orthQ]
  exact vecNorm2_zeroLeft_append y
/-- The concrete GQR `Q₂` basis has rectangular operator 2-norm at most one. -/
theorem GeneralizedQRFactorization.Q2Basis_rectOpNorm2Le_one
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    rectOpNorm2Le h.Q2Basis 1 := by
  intro y
  rw [h.Q2Basis_vecNorm2 y]
  simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    left multiplication by the concrete GQR `Q₂` basis preserves the vector
    2-norm of every matrix-vector action. -/
theorem GeneralizedQRFactorization.Q2Basis_rectMatMulVec_vecNorm2
    {r p q s : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (C : Fin q → Fin s → ℝ) (x : Fin s → ℝ) :
    vecNorm2 (rectMatMulVec (rectMatMul h.Q2Basis C) x) =
      vecNorm2 (rectMatMulVec C x) := by
  rw [rectMatMulVec_rectMatMul]
  exact h.Q2Basis_vecNorm2 (rectMatMulVec C x)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    rectangular operator-2 certificates are unchanged by left multiplication
    with the concrete GQR `Q₂` basis. -/
theorem GeneralizedQRFactorization.rectOpNorm2Le_rectMatMul_Q2Basis_iff
    {r p q s : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (C : Fin q → Fin s → ℝ) {c : ℝ} :
    rectOpNorm2Le (rectMatMul h.Q2Basis C) c ↔ rectOpNorm2Le C c := by
  constructor
  · intro hQC x
    calc
      vecNorm2 (rectMatMulVec C x)
          = vecNorm2 (rectMatMulVec (rectMatMul h.Q2Basis C) x) := by
              rw [h.Q2Basis_rectMatMulVec_vecNorm2 C x]
      _ ≤ c * vecNorm2 x := hQC x
  · intro hC x
    calc
      vecNorm2 (rectMatMulVec (rectMatMul h.Q2Basis C) x)
          = vecNorm2 (rectMatMulVec C x) :=
              h.Q2Basis_rectMatMulVec_vecNorm2 C x
      _ ≤ c * vecNorm2 x := hC x
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    left multiplication by the concrete GQR `Q₂` basis preserves the exact
    complexified rectangular operator 2-norm. -/
theorem GeneralizedQRFactorization.complexMatrixOp2_realRectToCMatrix_rectMatMul_Q2Basis_eq
    {r p q s : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (C : Fin q → Fin s → ℝ) :
    complexMatrixOp2 (realRectToCMatrix (rectMatMul h.Q2Basis C)) =
      complexMatrixOp2 (realRectToCMatrix C) := by
  apply le_antisymm
  · have hC :
        rectOpNorm2Le C (complexMatrixOp2 (realRectToCMatrix C)) :=
      rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le C le_rfl
    have hQC :
        rectOpNorm2Le (rectMatMul h.Q2Basis C)
          (complexMatrixOp2 (realRectToCMatrix C)) :=
      (h.rectOpNorm2Le_rectMatMul_Q2Basis_iff C).2 hC
    exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
      (rectMatMul h.Q2Basis C)
      (complexMatrixOp2_nonneg (realRectToCMatrix C)) hQC
  · have hQC :
        rectOpNorm2Le (rectMatMul h.Q2Basis C)
          (complexMatrixOp2
            (realRectToCMatrix (rectMatMul h.Q2Basis C))) :=
      rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
        (rectMatMul h.Q2Basis C) le_rfl
    have hC :
        rectOpNorm2Le C
          (complexMatrixOp2
            (realRectToCMatrix (rectMatMul h.Q2Basis C))) :=
      (h.rectOpNorm2Le_rectMatMul_Q2Basis_iff C).1 hQC
    exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le C
      (complexMatrixOp2_nonneg
        (realRectToCMatrix (rectMatMul h.Q2Basis C))) hC
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    the trailing `Q₂` coordinate block of the transformed data matrix `A Q`.

    Its columns are the last `q` columns of `A Q`, i.e. the action of `A` on
    the source `Q₂` coordinate range used in the proof of
    `null(B) = range(Q₂)`. -/
noncomputable def gqrAQ2Block {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ) :
    Fin (r + q) → Fin q → ℝ :=
  fun i j => matMulRect (r + q) (p + q) (p + q) A Q i (Fin.natAdd p j)
/-- Linearity bridge for the trailing `A Q₂` block: perturbing `A` by
    `DeltaA` changes the reduced GQR block by `DeltaA Q₂`. -/
theorem gqrAQ2Block_add_sub_eq {r p q : ℕ}
    (A DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ) :
    (fun i j =>
      gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j -
        gqrAQ2Block A Q i j) =
      gqrAQ2Block DeltaA Q := by
  ext i j
  unfold gqrAQ2Block matMulRect
  have hsum :
      (∑ k, (A i k + DeltaA i k) * Q k (Fin.natAdd p j)) =
        (∑ k, A i k * Q k (Fin.natAdd p j)) +
          ∑ k, DeltaA i k * Q k (Fin.natAdd p j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring
/-- Vector-action form of the `A Q₂` block. -/
theorem gqrAQ2Block_mulVec {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (y2 : Fin q → ℝ) :
    rectMatMulVec (gqrAQ2Block A Q) y2 =
      rectMatMulVec A (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) y2)) := by
  calc
    rectMatMulVec (gqrAQ2Block A Q) y2 =
        rectMatMulVec (matMulRect (r + q) (p + q) (p + q) A Q)
          (Fin.append (0 : Fin p → ℝ) y2) := by
      ext i
      unfold rectMatMulVec gqrAQ2Block
      rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
    _ = rectMatMulVec A
        (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) y2)) := by
      exact rectMatMulVec_rectMatMul A Q (Fin.append (0 : Fin p → ℝ) y2)
/-- Multiplying `A` by the concrete GQR `Q₂` basis gives the trailing
    transformed block `A Q₂`. -/
theorem GeneralizedQRFactorization.A_mul_Q2Basis
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    rectMatMul A h.Q2Basis = gqrAQ2Block A h.Q := by
  ext i j
  have hblock :=
    congrFun (gqrAQ2Block_mulVec A h.Q (finiteBasisVec j)) i
  have hcol :=
    congrFun (rectMatMulVec_finiteBasisVec_gsColumn
      (gqrAQ2Block A h.Q) j) i
  calc
    rectMatMul A h.Q2Basis i j =
        rectMatMulVec A
          (matMulVec (p + q) h.Q
            (Fin.append (0 : Fin p → ℝ) (finiteBasisVec j))) i := by
          simp [GeneralizedQRFactorization.Q2Basis, rectMatMul,
            rectMatMulVec]
    _ = rectMatMulVec (gqrAQ2Block A h.Q) (finiteBasisVec j) i :=
          hblock.symm
    _ = gqrAQ2Block A h.Q i j := by
          simpa [gsColumn] using hcol
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    the lifted reduced-Gram pseudoinverse candidate obtained by applying the
    concrete GQR `Q₂` basis to the Gram pseudoinverse of the trailing `A Q₂`
    block. -/
noncomputable def GeneralizedQRFactorization.liftedReducedGramAPplus
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Fin (p + q) → Fin (r + q) → ℝ :=
  rectMatMul h.Q2Basis
    (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    lifting the reduced-Gram pseudoinverse through the concrete GQR `Q₂` basis
    preserves its exact complexified rectangular operator 2-norm. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_op2_eq
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    complexMatrixOp2
        (realRectToCMatrix h.liftedReducedGramAPplus) =
      complexMatrixOp2
        (realRectToCMatrix
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) := by
  simpa [GeneralizedQRFactorization.liftedReducedGramAPplus] using
    h.complexMatrixOp2_realRectToCMatrix_rectMatMul_Q2Basis_eq
      (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source `kappa_B(A)` for the concrete lifted reduced-Gram candidate
    `Q₂(AQ₂)^+`, rewritten in reduced `A Q₂` coordinates.

    This is the GQR-specific norm identification used by the Eldén--Cox--
    Higham transfer; it does not assert a Moore--Penrose certificate for the
    lifted table. -/
theorem GeneralizedQRFactorization.theorem20_8KappaB_liftedReducedGramAPplus_eq
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    theorem20_8KappaB A h.liftedReducedGramAPplus =
      complexMatrixOp2
          (realRectToCMatrix
            (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) *
        frobNormRect A := by
  unfold theorem20_8KappaB
  rw [h.liftedReducedGramAPplus_op2_eq]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    the lifted reduced-Gram `APplus` candidate has all columns in the
    constraint nullspace, because its range is contained in the concrete GQR
    `Q₂` range and `B Q₂ = 0`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_constraint_annihilates
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    rectMatMul B h.liftedReducedGramAPplus =
      (fun _i : Fin p => fun _j : Fin (r + q) => 0) := by
  calc
    rectMatMul B h.liftedReducedGramAPplus =
        rectMatMul B
          (rectMatMul h.Q2Basis
            (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) := by
          rfl
    _ =
        rectMatMul (rectMatMul B h.Q2Basis)
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) := by
          rw [rectMatMul_assoc]
    _ =
        rectMatMul (fun _i : Fin p => fun _j : Fin q => 0)
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) := by
          rw [h.Q2Basis_nullspace]
    _ = (fun _i : Fin p => fun _j : Fin (r + q) => 0) := by
          ext i j
          unfold rectMatMul
          simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    vector-action form of the lifted reduced-Gram `APplus` range-null
    certificate. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_range_null
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (w : Fin (r + q) → ℝ) :
    rectMatMulVec B (rectMatMulVec h.liftedReducedGramAPplus w) =
      (fun _i : Fin p => 0) :=
  theorem20_8_APplus_range_null_of_constraint_annihilates B
    h.liftedReducedGramAPplus
    h.liftedReducedGramAPplus_constraint_annihilates w
/-- Reduced-operator perturbation bridge for Theorem 20.8:
    a bound stated on the GQR reduced blocks `A Q₂` transfers to the
    nullspace-basis form `A*N` with `N` chosen as the concrete GQR `Q₂` basis. -/
theorem GeneralizedQRFactorization.rectOpNorm2Le_reduced_delta_of_gqrAQ2Block
    {r p q : ℕ}
    {A Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {B Bpert : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    {c : ℝ}
    (hDelta :
      rectOpNorm2Le
        (fun i j => gqrAQ2Block Apert hpert.Q i j -
          gqrAQ2Block A h.Q i j) c) :
    rectOpNorm2Le
      (fun i j => rectMatMul Apert hpert.Q2Basis i j -
        rectMatMul A h.Q2Basis i j) c := by
  simpa [h.A_mul_Q2Basis, hpert.A_mul_Q2Basis] using hDelta
/-- The block `[S,0]` used in the GQR constraint equation has the same
    Frobenius norm as `S`. -/
theorem frobNormRect_gqrBQBlock {p q : ℕ}
    (S : Fin p → Fin p → ℝ) :
    frobNormRect (gqrBQBlock (q := q) S) = frobNormRect S := by
  simpa [gqrBQBlock] using
    (frobNormRect_zeroRightCols_append (m := p) (p := p) (q := q) S)
/-- With no trailing columns, the displayed GQR constraint block is exactly
    its square triangular block. -/
theorem gqrBQBlock_zero_eq {p : ℕ} (S : Fin p → Fin p → ℝ) :
    gqrBQBlock (q := 0) S = S := by
  ext i j
  refine Fin.addCases
    (motive := fun j : Fin (p + 0) => gqrBQBlock (q := 0) S i j = S i j)
    ?_ ?_ j
  · intro k
    simpa only [gqrBQBlock, Fin.castAdd_zero, Fin.cast_eq_self] using
      (Fin.append_left (S i) (fun _ : Fin 0 => (0 : ℝ)) k)
  · intro k
    exact Fin.elim0 k
/-- Transporting a displayed constraint block back through an orthogonal
    factor and then forward through the same factor recovers the block. -/
theorem gqrSourceBFromBlocks_mul_Q {p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S : Fin p → Fin p → ℝ) (hQ : IsOrthogonal (p + q) Q) :
    matMulRectRight (gqrSourceBFromBlocks Q S) Q = gqrBQBlock S := by
  have hQtQ : rectMatMul (matTranspose Q) Q = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hQ.left_inv i j
  calc
    matMulRectRight (gqrSourceBFromBlocks Q S) Q =
        rectMatMul (rectMatMul (gqrBQBlock S) (matTranspose Q)) Q := rfl
    _ = rectMatMul (gqrBQBlock S) (rectMatMul (matTranspose Q) Q) :=
          rectMatMul_assoc (gqrBQBlock S) (matTranspose Q) Q
    _ = rectMatMul (gqrBQBlock S) (idMatrix (p + q)) := by rw [hQtQ]
    _ = gqrBQBlock S := rectMatMul_id_right _
/-- An exact constraint identity `BQ=[S,0]` determines `B` as the transported
    source block.  This is the constraint-only form of GQR reconstruction and
    does not require packaging an unrelated least-squares block. -/
theorem gqrSourceBFromBlocks_eq_of_bq_eq {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S : Fin p → Fin p → ℝ) (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRectRight B Q = gqrBQBlock S) :
    gqrSourceBFromBlocks Q S = B := by
  have hQQt : rectMatMul Q (matTranspose Q) = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using hQ.right_inv i j
  calc
    gqrSourceBFromBlocks Q S =
        matMulRectRight (gqrBQBlock S) (matTranspose Q) := rfl
    _ = matMulRectRight (matMulRectRight B Q) (matTranspose Q) := by rw [hBQ]
    _ = rectMatMul (rectMatMul B Q) (matTranspose Q) := rfl
    _ = rectMatMul B (rectMatMul Q (matTranspose Q)) :=
          rectMatMul_assoc B Q (matTranspose Q)
    _ = rectMatMul B (idMatrix (p + q)) := by rw [hQQt]
    _ = B := rectMatMul_id_right B
/-- Orthogonal transport preserves the Frobenius norm of the displayed
    constraint block. -/
theorem frobNormRect_gqrSourceBFromBlocks {p q : ℕ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S : Fin p → Fin p → ℝ) (hQ : IsOrthogonal (p + q) Q) :
    frobNormRect (gqrSourceBFromBlocks Q S) = frobNormRect S := by
  calc
    frobNormRect (gqrSourceBFromBlocks Q S) =
        frobNormRect (gqrBQBlock (q := q) S) := by
          exact frobNormRect_orthogonal_right _ _ hQ.transpose
    _ = frobNormRect S := frobNormRect_gqrBQBlock S
/-- The GQR constraint block is additive in its triangular factor. -/
theorem gqrBQBlock_add {p q : ℕ}
    (S DeltaS : Fin p → Fin p → ℝ) :
    gqrBQBlock (q := q) (fun i j => S i j + DeltaS i j) =
      fun i j => gqrBQBlock (q := q) S i j + gqrBQBlock DeltaS i j := by
  ext i j
  refine Fin.addCases
    (motive := fun j : Fin (p + q) =>
      gqrBQBlock (q := q) (fun i j => S i j + DeltaS i j) i j =
        gqrBQBlock (q := q) S i j + gqrBQBlock DeltaS i j)
    ?left ?right j
  · intro j
    simp [gqrBQBlock, Fin.append_left]
  · intro j
    simp [gqrBQBlock, Fin.append_right]
/-- A supplied GQR factorization reconstructs its original constraint matrix
    from the displayed `[S,0]` block and `Qᵀ`. -/
theorem GeneralizedQRFactorization.sourceBFromBlocks_eq {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    gqrSourceBFromBlocks h.Q h.S = B := by
  have hbq :
      matMulRectRight B h.Q = gqrBQBlock h.S := by
    simpa [matMulRectRight] using h.bq_eq
  have hright : rectMatMul h.Q (matTranspose h.Q) = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using h.orthQ.right_inv i j
  calc
    gqrSourceBFromBlocks h.Q h.S =
        matMulRectRight (gqrBQBlock h.S) (matTranspose h.Q) := rfl
    _ = matMulRectRight (matMulRectRight B h.Q) (matTranspose h.Q) := by
          rw [← hbq]
    _ = rectMatMul (rectMatMul B h.Q) (matTranspose h.Q) := rfl
    _ = rectMatMul B (rectMatMul h.Q (matTranspose h.Q)) :=
          rectMatMul_assoc B h.Q (matTranspose h.Q)
    _ = rectMatMul B (idMatrix (p + q)) := by rw [hright]
    _ = B := rectMatMul_id_right B
/-- In a supplied GQR factorization, the Frobenius norm of the displayed
    constraint block `S` is the source Frobenius norm of `B`. -/
theorem GeneralizedQRFactorization.frobNormRect_S_eq_sourceB {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    frobNormRect h.S = frobNormRect B := by
  have hbq :
      matMulRectRight B h.Q = gqrBQBlock h.S := by
    simpa [matMulRectRight] using h.bq_eq
  calc
    frobNormRect h.S = frobNormRect (gqrBQBlock (q := q) h.S) := by
      exact (frobNormRect_gqrBQBlock h.S).symm
    _ = frobNormRect (matMulRectRight B h.Q) := by rw [← hbq]
    _ = frobNormRect B := frobNormRect_orthogonal_right B h.Q h.orthQ
/-- The GQR block with only the bottom-right `L22` perturbation nonzero has
    Frobenius norm exactly the Frobenius norm of that perturbation. -/
theorem frobNormRect_gqrAQBlock_only_L22 {r p q : ℕ}
    (DeltaL22 : Fin q → Fin q → ℝ) :
    frobNormRect
      (gqrAQBlock (r := r) (p := p) (q := q)
        (fun _ _ => 0) (fun _ _ => 0) DeltaL22) =
      frobNormRect DeltaL22 := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  rw [Fin.sum_univ_add]
  simp [gqrAQBlock, Fin.append_left, Fin.append_right, Fin.sum_univ_add]
/-- The displayed GQR `UᵀAQ` block is additive in its bottom-right `L22`
    block when all other perturbation blocks are zero. -/
theorem gqrAQBlock_L22_add {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 DeltaL22 : Fin q → Fin q → ℝ) :
    gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j) =
      fun i j =>
        gqrAQBlock L11 L21 L22 i j +
          gqrAQBlock (r := r) (p := p) (q := q)
            (fun _ _ => 0) (fun _ _ => 0) DeltaL22 i j := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (r + q) =>
      gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j) i j =
        gqrAQBlock L11 L21 L22 i j +
          gqrAQBlock (r := r) (p := p) (q := q)
            (fun _ _ => 0) (fun _ _ => 0) DeltaL22 i j)
    ?top ?bottom i
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin (p + q) =>
        gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j)
            (Fin.castAdd q i) j =
          gqrAQBlock L11 L21 L22 (Fin.castAdd q i) j +
            gqrAQBlock (r := r) (p := p) (q := q)
              (fun _ _ => 0) (fun _ _ => 0) DeltaL22 (Fin.castAdd q i) j)
      ?top_left ?top_right j
    · intro j
      simp [gqrAQBlock, Fin.append_left]
    · intro j
      simp [gqrAQBlock, Fin.append_left, Fin.append_right]
  · intro i
    refine Fin.addCases
      (motive := fun j : Fin (p + q) =>
        gqrAQBlock L11 L21 (fun i j => L22 i j + DeltaL22 i j)
            (Fin.natAdd r i) j =
          gqrAQBlock L11 L21 L22 (Fin.natAdd r i) j +
            gqrAQBlock (r := r) (p := p) (q := q)
              (fun _ _ => 0) (fun _ _ => 0) DeltaL22 (Fin.natAdd r i) j)
      ?bottom_left ?bottom_right j
    · intro j
      simp [gqrAQBlock, Fin.append_right, Fin.append_left]
    · intro j
      simp [gqrAQBlock, Fin.append_right]
/-- The `A Q₂` block has Frobenius norm no larger than `A` when `Q` is
    orthogonal. -/
theorem frobNormRect_gqrAQ2Block_le
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q) :
    frobNormRect (gqrAQ2Block A Q) ≤ frobNormRect A := by
  let AQ : Fin (r + q) → Fin (p + q) → ℝ := matMulRectRight A Q
  have htrail :
      gqrAQ2Block A Q =
        fun i : Fin (r + q) => fun j : Fin q => AQ i (Fin.natAdd p j) := by
    ext i j
    rfl
  calc
    frobNormRect (gqrAQ2Block A Q)
        = frobNormRect
            (fun i : Fin (r + q) => fun j : Fin q => AQ i (Fin.natAdd p j)) := by
          rw [htrail]
    _ ≤ frobNormRect AQ := frobNormRect_trailingCols_le AQ
    _ = frobNormRect A := by
          simpa [AQ] using frobNormRect_orthogonal_right A Q hQ
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if the perturbed GQR record uses the same `Q` as the source record, a
    full-source Frobenius perturbation bound for `DeltaA` supplies the reduced
    trailing-block Frobenius budget. -/
theorem GeneralizedQRFactorization.gqrAQ2Block_delta_frobNorm_le_of_same_Q
    {r p q : ℕ}
    {A DeltaA : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hpert : GeneralizedQRFactorization r p q
      (fun i j => A i j + DeltaA i j) Bpert)
    {c : ℝ}
    (hQsame : hpert.Q = h.Q)
    (hDeltaA : frobNormRect DeltaA ≤ c) :
    frobNormRect
      (fun i j =>
        gqrAQ2Block (fun i j => A i j + DeltaA i j) hpert.Q i j -
          gqrAQ2Block A h.Q i j) ≤ c := by
  rw [hQsame, gqrAQ2Block_add_sub_eq]
  exact le_trans (frobNormRect_gqrAQ2Block_le DeltaA h.Q h.orthQ) hDeltaA
/-- The bottom-right `L22` block in the displayed GQR `UᵀAQ` matrix has
    Frobenius norm no larger than the full displayed block. -/
theorem frobNormRect_gqrAQBlock_L22_le {r p q : ℕ}
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ) :
    frobNormRect L22 ≤ frobNormRect (gqrAQBlock L11 L21 L22) := by
  let bottom : Fin q → Fin (p + q) → ℝ :=
    fun i j => gqrAQBlock L11 L21 L22 (Fin.natAdd r i) j
  have hL22 :
      L22 = fun i : Fin q => fun j : Fin q => bottom i (Fin.natAdd p j) := by
    ext i j
    simp [bottom, gqrAQBlock, Fin.append_right]
  calc
    frobNormRect L22 =
        frobNormRect (fun i : Fin q => fun j : Fin q =>
          bottom i (Fin.natAdd p j)) := by rw [hL22]
    _ ≤ frobNormRect bottom := frobNormRect_trailingCols_le bottom
    _ ≤ frobNormRect (gqrAQBlock L11 L21 L22) :=
          frobNormRect_bottomRows_le (gqrAQBlock L11 L21 L22)
/-- A supplied GQR factorization reconstructs its original data matrix from
    the displayed `UᵀAQ` block and the orthogonal factors `U` and `Qᵀ`. -/
theorem GeneralizedQRFactorization.sourceAFromBlocks_eq {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 h.L22 = A := by
  let M : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrAQBlock h.L11 h.L21 h.L22
  let AQ : Fin (r + q) → Fin (p + q) → ℝ := matMulRectRight A h.Q
  have haq : matMulRectLeft (matTranspose h.U) AQ = M := by
    simpa [M, AQ, matMulRectRight] using h.aq_eq
  have hUright : rectMatMul h.U (matTranspose h.U) = idMatrix (r + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using h.orthU.right_inv i j
  have hQright : rectMatMul h.Q (matTranspose h.Q) = idMatrix (p + q) := by
    ext i j
    simpa [rectMatMul, idMatrix] using h.orthQ.right_inv i j
  calc
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 h.L22 =
        matMulRectLeft h.U (matMulRectRight M (matTranspose h.Q)) := rfl
    _ = matMulRectLeft h.U
          (matMulRectRight
            (matMulRectLeft (matTranspose h.U) AQ) (matTranspose h.Q)) := by
          rw [haq]
    _ = rectMatMul h.U
          (rectMatMul
            (rectMatMul (matTranspose h.U) (rectMatMul A h.Q))
            (matTranspose h.Q)) := by
          rfl
    _ = rectMatMul h.U
          (rectMatMul (matTranspose h.U)
            (rectMatMul (rectMatMul A h.Q) (matTranspose h.Q))) := by
          rw [rectMatMul_assoc]
    _ = rectMatMul
          (rectMatMul h.U (matTranspose h.U))
          (rectMatMul (rectMatMul A h.Q) (matTranspose h.Q)) := by
          rw [← rectMatMul_assoc]
    _ = rectMatMul
          (idMatrix (r + q))
          (rectMatMul (rectMatMul A h.Q) (matTranspose h.Q)) := by
          rw [hUright]
    _ = rectMatMul (rectMatMul A h.Q) (matTranspose h.Q) := by
          rw [rectMatMul_id_left]
    _ = rectMatMul A (rectMatMul h.Q (matTranspose h.Q)) :=
          rectMatMul_assoc A h.Q (matTranspose h.Q)
    _ = rectMatMul A (idMatrix (p + q)) := by rw [hQright]
    _ = A := rectMatMul_id_right A
/-- In a supplied GQR factorization, the bottom-right displayed block `L22`
    has Frobenius norm no larger than the source data matrix `A`. -/
theorem GeneralizedQRFactorization.frobNormRect_L22_le_sourceA {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    frobNormRect h.L22 ≤ frobNormRect A := by
  let M : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrAQBlock h.L11 h.L21 h.L22
  have haq : matMulRectLeft (matTranspose h.U) (matMulRectRight A h.Q) = M := by
    simpa [M, matMulRectRight] using h.aq_eq
  have hMnorm : frobNormRect M = frobNormRect A := by
    calc
      frobNormRect M =
          frobNormRect
            (matMulRectLeft (matTranspose h.U) (matMulRectRight A h.Q)) := by
            rw [← haq]
      _ = frobNormRect (matMulRectRight A h.Q) := by
            exact frobNormRect_orthogonal_left (matTranspose h.U)
              (matMulRectRight A h.Q) (IsOrthogonal.transpose h.orthU)
      _ = frobNormRect A := frobNormRect_orthogonal_right A h.Q h.orthQ
  calc
    frobNormRect h.L22 ≤ frobNormRect M :=
      frobNormRect_gqrAQBlock_L22_le h.L11 h.L21 h.L22
    _ = frobNormRect A := hMnorm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    the `A Q₂` block has trivial kernel using only the constraint block
    identity `B Q = [S 0]`, orthogonality of `Q`, and the local
    null-intersection condition.

    This is the construction-level form of the `Q₂` kernel bridge: it does not
    assume a complete supplied `GeneralizedQRFactorization`, so it can be used
    immediately after constructing the `Bᵀ` QR side. -/
theorem gqrAQ2_kernel_trivial_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B)
    (y2 : Fin q → ℝ)
    (hAy2 :
      rectMatMulVec A
        (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) y2)) = 0) :
    y2 = 0 := by
  let y : Fin (p + q) → ℝ := Fin.append (0 : Fin p → ℝ) y2
  let x : Fin (p + q) → ℝ := matMulVec (p + q) Q y
  have hBx : rectMatMulVec B x = 0 := by
    calc
      rectMatMulVec B (matMulVec (p + q) Q y)
          = rectMatMulVec (matMulRect p (p + q) (p + q) B Q) y := by
              exact (rectMatMulVec_rectMatMul B Q y).symm
      _ = rectMatMulVec (gqrBQBlock S) y := by
              rw [hBQ]
      _ = rectMatMulVec S (0 : Fin p → ℝ) := by
              simpa [y] using gqrBQBlock_mulVec S (0 : Fin p → ℝ) y2
      _ = 0 := rectMatMulVec_zero S
  have hxzero : x = 0 := hnull x hAy2 hBx
  have hyzero : y = 0 := by
    have hrec := matMulVec_orthogonal_transpose_mul hQ y
    dsimp [x] at hxzero
    rw [hxzero, matMulVec_zero] at hrec
    exact hrec.symm
  ext i
  have hi := congrFun hyzero (Fin.natAdd p i)
  simpa [y, Fin.append_right] using hi
/-- Construction-level injectivity of the `A Q₂` rectangular column map from
    the constraint block identity and the local null-intersection condition. -/
theorem gqrAQ2_rectMatMulVec_injective_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B) :
    Function.Injective (rectMatMulVec (gqrAQ2Block A Q)) := by
  intro y2 z2 hyz
  let w : Fin q → ℝ := fun i => y2 i - z2 i
  have hAw :
      rectMatMulVec A
        (matMulVec (p + q) Q (Fin.append (0 : Fin p → ℝ) w)) = 0 := by
    have hblock : rectMatMulVec (gqrAQ2Block A Q) w = 0 := by
      ext i
      have hi := congrFun hyz i
      have hsub := congrFun (rectMatMulVec_sub (gqrAQ2Block A Q) y2 z2) i
      dsimp [w]
      rw [hsub, hi]
      ring
    simpa [gqrAQ2Block_mulVec A Q w] using hblock
  have hw : w = 0 :=
    gqrAQ2_kernel_trivial_of_constraint_block_nullIntersection
      hQ hBQ hnull w hAw
  ext i
  have hwi := congrFun hw i
  dsimp [w] at hwi
  linarith
/-- Construction-level exact-MGS nonbreakdown for the smaller `A Q₂` block. -/
theorem gqrAQ2_mgs_norm_ne_zero_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors (gqrAQ2Block A Q) j.val j) ≠ 0 :=
  modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
    (gqrAQ2Block A Q)
    (gqrAQ2_rectMatMulVec_injective_of_constraint_block_nullIntersection
      hQ hBQ hnull) j
/-- Construction-level injectivity for the column-reversed smaller `A Q₂`
    block.  This is the precise nonbreakdown route for the QR input that will
    later be converted into the lower-triangular `L₂₂` block in (20.28). -/
theorem gqrAQ2_reversed_rectMatMulVec_injective_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B) :
    Function.Injective
      (rectMatMulVec (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q))) :=
  rectMatMulVec_injective_rectPermuteCols Fin.revPerm
    (gqrAQ2_rectMatMulVec_injective_of_constraint_block_nullIntersection
      hQ hBQ hnull)
/-- Construction-level exact-MGS nonbreakdown for the column-reversed smaller
    `A Q₂` block. -/
theorem gqrAQ2_reversed_mgs_norm_ne_zero_of_constraint_block_nullIntersection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {S : Fin p → Fin p → ℝ}
    (hQ : IsOrthogonal (p + q) Q)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hnull : LSENullIntersectionTrivial A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors
        (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)) j.val j) ≠ 0 :=
  modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
    (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q))
    (gqrAQ2_reversed_rectMatMulVec_injective_of_constraint_block_nullIntersection
      hQ hBQ hnull) j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    full row rank of `B` constructs the constraint block side, while stacked
    full column rank supplies exact-MGS nonbreakdown for the smaller `A Q₂`
    block associated with the constructed `Q`. -/
theorem exists_gqr_constraint_block_and_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        ∀ j : Fin q,
          gsColumnNorm2
            (modifiedGramSchmidtVectors (gqrAQ2Block A Q) j.val j) ≠ 0 := by
  have hdiagB : ∀ j : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun col : Fin (p + q) => fun row : Fin p => B row col)
          j.val j) ≠ 0 := by
    intro j
    exact hB.transpose_mgs_norm_ne_zero j
  rcases exists_gqr_constraint_block_of_mgs B hdiagB with
    ⟨Q, S, hQ, hS, hBQ⟩
  have hnull : LSENullIntersectionTrivial A B :=
    (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack
  refine ⟨Q, S, hQ, hS, hBQ, ?_⟩
  intro j
  exact
    gqrAQ2_mgs_norm_ne_zero_of_constraint_block_nullIntersection
      hQ hBQ hnull j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    full row rank of `B` constructs the constraint block side, while stacked
    full column rank supplies exact-MGS nonbreakdown for the column-reversed
    smaller `A Q₂` block. -/
theorem exists_gqr_constraint_block_and_reversed_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        ∀ j : Fin q,
          gsColumnNorm2
            (modifiedGramSchmidtVectors
              (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)) j.val j) ≠ 0 := by
  rcases
    exists_gqr_constraint_block_and_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, hQ, hS, hBQ, _hdiagAQ2⟩
  have hnull : LSENullIntersectionTrivial A B :=
    (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack
  refine ⟨Q, S, hQ, hS, hBQ, ?_⟩
  intro j
  exact
    gqrAQ2_reversed_mgs_norm_ne_zero_of_constraint_block_nullIntersection
      hQ hBQ hnull j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    after constructing the `Bᵀ` constraint block from full row rank of `B`,
    the smaller `A Q₂` block has an exact MGS QR factorization under the
    source stacked-full-column-rank hypothesis.

    This packages the oracle-recommended smaller-block route as explicit
    QR data for the next associated-shape construction step. -/
theorem exists_gqr_constraint_block_and_A_Q2_mgs_qr_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ)
        (Q2 : Fin (r + q) → Fin q → ℝ) (R2 : Fin q → Fin q → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        GramSchmidtOrthonormalColumns Q2 ∧
        IsUpperTriangular q R2 ∧
        gqrAQ2Block A Q = matMulRect (r + q) q q Q2 R2 := by
  rcases
    exists_gqr_constraint_block_and_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, hQ, hS, hBQ, hdiagAQ2⟩
  let C : Fin (r + q) → Fin q → ℝ := gqrAQ2Block A Q
  let Q2 : Fin (r + q) → Fin q → ℝ := modifiedGramSchmidtQ C
  let R2 : Fin q → Fin q → ℝ := modifiedGramSchmidtR C
  have horthQ2 : GramSchmidtOrthonormalColumns Q2 := by
    exact modifiedGramSchmidtQ_orthonormal_columns C hdiagAQ2
  have hR2upper : IsUpperTriangular q R2 := by
    exact IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal C)
  have hfactor : C = matMulRect (r + q) q q Q2 R2 := by
    exact modifiedGramSchmidt_exact_factorization C hdiagAQ2
  exact ⟨Q, S, Q2, R2, hQ, hS, hBQ, horthQ2, hR2upper, hfactor⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    after constructing the `Bᵀ` constraint block from full row rank of `B`,
    the column-reversed smaller `A Q₂` block has an exact MGS QR factorization
    under the source stacked-full-column-rank hypothesis. -/
theorem exists_gqr_constraint_block_and_reversed_A_Q2_mgs_qr_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ)
        (Q2 : Fin (r + q) → Fin q → ℝ) (R2 : Fin q → Fin q → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        GramSchmidtOrthonormalColumns Q2 ∧
        IsUpperTriangular q R2 ∧
        rectPermuteCols Fin.revPerm (gqrAQ2Block A Q) =
          matMulRect (r + q) q q Q2 R2 := by
  rcases
    exists_gqr_constraint_block_and_reversed_A_Q2_mgs_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, hQ, hS, hBQ, hdiagAQ2rev⟩
  let C : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
  let Q2 : Fin (r + q) → Fin q → ℝ := modifiedGramSchmidtQ C
  let R2 : Fin q → Fin q → ℝ := modifiedGramSchmidtR C
  have horthQ2 : GramSchmidtOrthonormalColumns Q2 := by
    exact modifiedGramSchmidtQ_orthonormal_columns C hdiagAQ2rev
  have hR2upper : IsUpperTriangular q R2 := by
    exact IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal C)
  have hfactor : C = matMulRect (r + q) q q Q2 R2 := by
    exact modifiedGramSchmidt_exact_factorization C hdiagAQ2rev
  exact ⟨Q, S, Q2, R2, hQ, hS, hBQ, horthQ2, hR2upper, hfactor⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    after constructing the `Bᵀ` constraint block, the smaller `A Q₂` block can
    be put into the tall associated shape `[0; L₂₂]` by an orthogonal row
    factor.

    This is still a smaller-block result: it does not yet lift the constructed
    `U` to the full transformed matrix `A Q` with its leading `p` columns. -/
theorem exists_gqr_constraint_block_and_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (S : Fin p → Fin p → ℝ)
        (U : Fin (r + q) → Fin (r + q) → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsLowerTriangular S ∧
        matMulRect p (p + q) (p + q) B Q = gqrBQBlock S ∧
        IsOrthogonal (r + q) U ∧
        Nonempty (GQRAQTallCase r q
          (matMulRectLeft (matTranspose U) (gqrAQ2Block A Q))) := by
  rcases
    exists_gqr_constraint_block_and_reversed_A_Q2_mgs_qr_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, Q2, R2, hQ, hS, hBQ, hQ2orth, hR2upper, hfactor⟩
  rcases GQRAQTallCase.exists_of_qr_reversed_cols
      (gqrAQ2Block A Q) Q2 R2 hQ2orth hR2upper hfactor with
    ⟨U, hU, hCase⟩
  exact ⟨Q, S, U, hQ, hS, hBQ, hU, hCase⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction route:
    a constructed constraint block `B Q = [S 0]` plus a tall associated shape
    for the smaller trailing block `A Q₂` packages the full generalized QR
    block display (20.27).

    The leading blocks `L₁₁` and `L₂₁` are extracted from the already
    transformed full matrix `Uᵀ A Q`; the supplied `A Q₂` tall shape supplies
    exactly the top-right zero block and the lower-triangular `L₂₂`. -/
theorem GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (S : Fin p → Fin p → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hS : IsLowerTriangular S)
    (hBQ : matMulRect p (p + q) (p + q) B Q = gqrBQBlock S)
    (hU : IsOrthogonal (r + q) U)
    (hCase : GQRAQTallCase r q
      (matMulRectLeft (matTranspose U) (gqrAQ2Block A Q))) :
    ∃ h : GeneralizedQRFactorization r p q A B,
      h.Q = Q ∧ h.U = U ∧ h.S = S ∧ h.L22 = hCase.L := by
  rcases hCase with ⟨Lcase, hLcase, hAQ2⟩
  let M : Fin (r + q) → Fin (p + q) → ℝ :=
    matMulRectLeft (matTranspose U)
      (matMulRect (r + q) (p + q) (p + q) A Q)
  let L11 : Fin r → Fin p → ℝ :=
    fun i j => M (Fin.castAdd q i) (Fin.castAdd q j)
  let L21 : Fin q → Fin p → ℝ :=
    fun i j => M (Fin.natAdd r i) (Fin.castAdd q j)
  let L22 : Fin q → Fin q → ℝ := Lcase
  have htrail : ∀ row : Fin (r + q), ∀ j : Fin q,
      M row (Fin.natAdd p j) =
        matMulRectLeft (matTranspose U) (gqrAQ2Block A Q) row j := by
    intro row j
    simp [M, matMulRectLeft, gqrAQ2Block]
  have hAQ : M = gqrAQBlock L11 L21 L22 := by
    ext row col
    refine Fin.addCases
      (motive := fun col : Fin (p + q) =>
        M row col = gqrAQBlock L11 L21 L22 row col)
      ?leftCols ?rightCols col
    · intro col
      refine Fin.addCases
        (motive := fun row : Fin (r + q) =>
          M row (Fin.castAdd q col) =
            gqrAQBlock L11 L21 L22 row (Fin.castAdd q col))
        (fun row => by simp [L11, gqrAQBlock])
        (fun row => by simp [L21, gqrAQBlock])
        row
    · intro col
      refine Fin.addCases
        (motive := fun row : Fin (r + q) =>
          M row (Fin.natAdd p col) =
            gqrAQBlock L11 L21 L22 row (Fin.natAdd p col))
        ?topRows ?bottomRows row
      · intro row
        calc
          M (Fin.castAdd q row) (Fin.natAdd p col)
              =
            matMulRectLeft (matTranspose U) (gqrAQ2Block A Q)
              (Fin.castAdd q row) col := htrail (Fin.castAdd q row) col
          _ = gqrAQTallBlock Lcase (Fin.castAdd q row) col := by
                rw [hAQ2]
          _ = 0 := by
                simp [gqrAQTallBlock]
          _ = gqrAQBlock L11 L21 L22 (Fin.castAdd q row) (Fin.natAdd p col) := by
                simp [gqrAQBlock, L22]
      · intro row
        calc
          M (Fin.natAdd r row) (Fin.natAdd p col)
              =
            matMulRectLeft (matTranspose U) (gqrAQ2Block A Q)
              (Fin.natAdd r row) col := htrail (Fin.natAdd r row) col
          _ = gqrAQTallBlock Lcase (Fin.natAdd r row) col := by
                rw [hAQ2]
          _ = L22 row col := by
                simp [gqrAQTallBlock, L22]
          _ = gqrAQBlock L11 L21 L22 (Fin.natAdd r row) (Fin.natAdd p col) := by
                simp [gqrAQBlock]
  refine ⟨{
    Q := Q
    U := U
    L11 := L11
    L21 := L21
    L22 := L22
    S := S
    orthQ := hQ
    orthU := hU
    aq_eq := ?_
    bq_eq := hBQ
    lowerL22 := hLcase
    lowerS := hS
  }, rfl, rfl, rfl, rfl⟩
  simpa [M] using hAQ
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9, exact GQR existence.

    For arbitrary real matrices `A ∈ ℝ^((r+q)×(p+q))` and
    `B ∈ ℝ^(p×(p+q))`, there are orthogonal factors `U`, `Q` and
    lower-triangular blocks giving the generalized QR display (20.27).  No
    full-row-rank assumption on `B` and no stacked-rank assumption on
    `[A; B]` is needed for this existence statement.

    The construction uses the exact zero-aware rectangular Householder QR of
    `Bᵀ`, so rank-deficient and zero-column cases are included.  A second
    exact Householder construction puts the trailing block `A Q₂` into the
    required lower-triangular form.  The rank hypotheses in the remainder of
    Theorem 20.9 concern nonsingularity of `S` and `L22`, not existence of the
    GQR factorization itself. -/
theorem GeneralizedQRFactorization.exists_theorem20_9_exact_householder
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) :
    Nonempty (GeneralizedQRFactorization r p q A B) := by
  let Bt : Fin (p + q) → Fin p → ℝ := fun j i => B i j
  let Q : Fin (p + q) → Fin (p + q) → ℝ :=
    exactHouseholderQRPanel_Q (p + q) p Bt
  let Rhat : Fin (p + q) → Fin p → ℝ :=
    exactHouseholderQRPanel_R (p + q) p Bt
  let R : Fin p → Fin p → ℝ :=
    fun i j => Rhat (Fin.castAdd q i) j
  have hQ : IsOrthogonal (p + q) Q := by
    simpa [Q] using exactHouseholderQRPanel_Q_orthogonal (p + q) p Bt
  have hRhatUpper : IsUpperTrapezoidal (p + q) p Rhat := by
    simpa [Rhat] using
      exactHouseholderQRPanel_R_upper_trapezoidal (p + q) p Bt
  have hRhatBlock : Rhat = lsQRTallBlock (k := q) R :=
    lsQRTallBlock_of_upper_trapezoidal (n := p) (k := q) Rhat hRhatUpper
  have hRupper : IsUpperTriangular p R := by
    intro i j hij
    exact lsQRTallBlock_top_upper_of_upper_trapezoidal
      (n := p) (k := q) Rhat hRhatUpper i j hij
  have hRhatEq :
      Rhat = matMulRectLeft (matTranspose Q) Bt := by
    simpa [Q, Rhat] using
      exactHouseholderQRPanel_R_eq_matMulRectLeft_transpose_Q
        (p + q) p Bt
  have hqrB :
      matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p => B i j) =
        lsQRTallBlock (k := q) R := by
    calc
      matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p => B i j) =
          matMulRectLeft (matTranspose Q) Bt := by rfl
      _ = Rhat := hRhatEq.symm
      _ = lsQRTallBlock (k := q) R := hRhatBlock
  let S : Fin p → Fin p → ℝ := matTranspose R
  have hS : IsLowerTriangular S := by
    exact isLowerTriangular_matTranspose_of_isUpperTriangular hRupper
  have hBQ :
      matMulRect p (p + q) (p + q) B Q = gqrBQBlock S := by
    simpa [S] using gqrBQBlock_eq_of_transpose_tall_qr B Q R hqrB
  rcases GQRAQTallCase.exists_of_exact_householder_reversed_cols
      (gqrAQ2Block A Q) with
    ⟨U, hU, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  rcases GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
      (A := A) (B := B) Q S U hQ hS hBQ hU hCase with
    ⟨h, _hQeq, _hUeq, _hSeq, _hL22eq⟩
  exact ⟨h⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction theorem for the
    block form (20.27): source full row rank of `B` and full column rank of the
    stacked matrix `[A; B]` construct exact generalized QR factorization data.

    This closes the exact algebraic GQR existence surface for (20.27).  The
    associated (20.28) display, numerical rank equivalences, and computed
    finite-precision GQR stability remain separate rows. -/
theorem GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    Nonempty (GeneralizedQRFactorization r p q A B) := by
  rcases
    exists_gqr_constraint_block_and_A_Q2_tall_assoc_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨Q, S, U, hQ, hS, hBQ, hU, hCase⟩
  rcases hCase with ⟨hCase⟩
  rcases GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
      (A := A) (B := B) Q S U hQ hS hBQ hU hCase with
    ⟨h, _hQeq, _hUeq, _hSeq, _hL22eq⟩
  exact ⟨h⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof:
    on the `Q₂` coordinate range, the equation `A x = 0` is equivalent to
    `L22 y₂ = 0`.

    This names the exact algebra behind the source statement
    `AQ₂ = U₂ L22`, which is used to relate
    `null(A) ∩ null(B) = {0}` to nonsingularity of `L22`. -/
theorem GeneralizedQRFactorization.A_Q2_zero_iff_L22_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (y2 : Fin q → ℝ) :
    rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0 ↔
      rectMatMulVec h.L22 y2 = 0 := by
  constructor
  · intro hAy
    have htrans :=
      h.transformed_A_zero_of_A_zero
        (y := Fin.append (0 : Fin p → ℝ) y2) hAy
    have hblock := h.transformed_A_mulVec_eq_block (0 : Fin p → ℝ) y2
    rw [htrans] at hblock
    ext i
    have hi := congrFun hblock (Fin.natAdd r i)
    have hi0 :
        (0 : Fin (r + q) → ℝ) (Fin.natAdd r i) =
          rectMatMulVec h.L21 (0 : Fin p → ℝ) i +
            rectMatMulVec h.L22 y2 i := by
      simpa [Fin.append_right] using hi
    have hleft : rectMatMulVec h.L21 (0 : Fin p → ℝ) i = 0 := by
      simp [rectMatMulVec]
    have hzero : 0 = rectMatMulVec h.L22 y2 i := by
      simpa [hleft] using hi0
    exact hzero.symm
  · intro hL22
    have hblock :
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q))
          (Fin.append (0 : Fin p → ℝ) y2) = 0 := by
      rw [h.transformed_A_mulVec_eq_block (0 : Fin p → ℝ) y2]
      ext i
      refine Fin.addCases
        (motive := fun i : Fin (r + q) =>
          Fin.append (rectMatMulVec h.L11 (0 : Fin p → ℝ))
            (fun i : Fin q =>
              rectMatMulVec h.L21 (0 : Fin p → ℝ) i +
                rectMatMulVec h.L22 y2 i) i =
            (0 : Fin (r + q) → ℝ) i)
        ?left ?right i
      · intro i
        simp [Fin.append_left, rectMatMulVec]
      · intro i
        have hi := congrFun hL22 i
        simpa [Fin.append_right, rectMatMulVec] using hi
    exact h.A_zero_of_transformed_A_zero hblock
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    under the source null-intersection condition, the `Q₂` coordinate block
    has trivial kernel through `A`.

    This is the source-faithful kernel consequence behind the proof step
    `null(B) = range(Q₂)` followed by `AQ₂ = U₂ L22`: if
    `A (Q [0; y₂]) = 0`, then the same vector also satisfies the constraint
    block equation, hence lies in `null(A) ∩ null(B)` and must be zero. -/
theorem GeneralizedQRFactorization.A_Q2_kernel_trivial_of_nullIntersectionTrivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hnull : LSENullIntersectionTrivial A B)
    (y2 : Fin q → ℝ)
    (hAy2 :
      rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0) :
    y2 = 0 := by
  let y : Fin (p + q) → ℝ := Fin.append (0 : Fin p → ℝ) y2
  let x : Fin (p + q) → ℝ := matMulVec (p + q) h.Q y
  have hBx : rectMatMulVec B x = 0 := by
    have hc := h.constraint_eq (0 : Fin p → ℝ) y2
    change
      rectMatMulVec B
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0
    rw [hc]
    exact rectMatMulVec_zero h.S
  have hxzero : x = 0 := hnull x hAy2 hBx
  have hyzero : y = 0 := by
    have hrec := matMulVec_orthogonal_transpose_mul h.orthQ y
    dsimp [x] at hxzero
    rw [hxzero, matMulVec_zero] at hrec
    exact hrec.symm
  ext i
  have hi := congrFun hyzero (Fin.natAdd p i)
  simpa [y, Fin.append_right] using hi
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    stacked full column rank gives the same trivial-kernel property for the
    `A Q₂` block, using the repository's equivalence between stacked rank and
    the local null-intersection condition. -/
theorem GeneralizedQRFactorization.A_Q2_kernel_trivial_of_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hstack : LSEStackedFullColumnRank A B)
    (y2 : Fin q → ℝ)
    (hAy2 :
      rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2)) = 0) :
    y2 = 0 :=
  h.A_Q2_kernel_trivial_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    y2 hAy2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    the `A Q₂` block has injective column map under the local
    null-intersection condition. -/
theorem GeneralizedQRFactorization.A_Q2_rectMatMulVec_injective_of_nullIntersectionTrivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hnull : LSENullIntersectionTrivial A B) :
    Function.Injective (rectMatMulVec (gqrAQ2Block A h.Q)) := by
  intro y2 z2 hyz
  let w : Fin q → ℝ := fun i => y2 i - z2 i
  have hAw :
      rectMatMulVec A
        (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) w)) = 0 := by
    have hblock : rectMatMulVec (gqrAQ2Block A h.Q) w = 0 := by
      ext i
      have hi := congrFun hyz i
      have hsub :=
        congrFun (rectMatMulVec_sub (gqrAQ2Block A h.Q) y2 z2) i
      dsimp [w]
      rw [hsub, hi]
      ring
    simpa [gqrAQ2Block_mulVec A h.Q w] using hblock
  have hw : w = 0 :=
    h.A_Q2_kernel_trivial_of_nullIntersectionTrivial hnull w hAw
  ext i
  have hwi := congrFun hw i
  dsimp [w] at hwi
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    stacked full column rank gives injectivity of the `A Q₂` column map. -/
theorem GeneralizedQRFactorization.A_Q2_rectMatMulVec_injective_of_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hstack : LSEStackedFullColumnRank A B) :
    Function.Injective (rectMatMulVec (gqrAQ2Block A h.Q)) :=
  h.A_Q2_rectMatMulVec_injective_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    stacked full column rank supplies the concrete Gram-pseudoinverse fields
    for the reduced `A Q₂` block. -/
theorem GeneralizedQRFactorization.A_Q2_reduced_gram_left_inverse_and_projection_symmetric
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hstack : LSEStackedFullColumnRank A B) :
    rectMatMul (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
        (gqrAQ2Block A h.Q) = idMatrix q ∧
      IsSymmetricFiniteMatrix
        (rectMatMul (gqrAQ2Block A h.Q)
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) :=
  lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric
    (gqrAQ2Block A h.Q)
    (h.A_Q2_rectMatMulVec_injective_of_stackedFullColumnRank hstack)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    stacked full column rank makes the concrete reduced Gram pseudoinverse for
    `A Q₂` a nonzero left inverse, hence its operator norm is positive. -/
theorem GeneralizedQRFactorization.A_Q2_reduced_gram_pseudoinverse_op2_pos
    {r p k : ℕ}
    {A : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {B : Fin p → Fin (p + (k + 1)) → ℝ}
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hstack : LSEStackedFullColumnRank A B) :
    0 < complexMatrixOp2
      (realRectToCMatrix (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))) := by
  have hred := h.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstack
  exact complexMatrixOp2_realRectToCMatrix_pos_of_rect_left_inverse
    (gqrAQ2Block A h.Q)
    (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) hred.1
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    positivity of the lifted reduced-Gram source `kappa_B(A)` under the source
    stacked-rank condition and positive `||A||_F`. -/
theorem GeneralizedQRFactorization.theorem20_8KappaB_liftedReducedGramAPplus_pos
    {r p k : ℕ}
    {A : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {B : Fin p → Fin (p + (k + 1)) → ℝ}
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hstack : LSEStackedFullColumnRank A B)
    (hApos : 0 < frobNormRect A) :
    0 < theorem20_8KappaB A h.liftedReducedGramAPplus := by
  rw [h.theorem20_8KappaB_liftedReducedGramAPplus_eq]
  exact mul_pos (h.A_Q2_reduced_gram_pseudoinverse_op2_pos hstack) hApos
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8/20.9 support:
    stacked full column rank makes the concrete reduced block `A Q₂` a
    nonzero operator. -/
theorem GeneralizedQRFactorization.A_Q2_reduced_block_op2_pos
    {r p k : ℕ}
    {A : Fin (r + (k + 1)) → Fin (p + (k + 1)) → ℝ}
    {B : Fin p → Fin (p + (k + 1)) → ℝ}
    (h : GeneralizedQRFactorization r p (k + 1) A B)
    (hstack : LSEStackedFullColumnRank A B) :
    0 < complexMatrixOp2 (realRectToCMatrix (gqrAQ2Block A h.Q)) := by
  have hred := h.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstack
  exact complexMatrixOp2_realRectToCMatrix_pos_of_rect_has_left_inverse
    (gqrAQ2Block A h.Q)
    (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) hred.1
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS A-side bridge:
    the source null-intersection condition supplies every nonzero-stage
    normalizer needed for exact MGS applied to the smaller `A Q₂` block. -/
theorem GeneralizedQRFactorization.A_Q2_mgs_norm_ne_zero_of_nullIntersectionTrivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hnull : LSENullIntersectionTrivial A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors (gqrAQ2Block A h.Q) j.val j) ≠ 0 :=
  modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
    (gqrAQ2Block A h.Q)
    (h.A_Q2_rectMatMulVec_injective_of_nullIntersectionTrivial hnull) j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS A-side bridge:
    stacked full column rank supplies every exact-MGS nonzero-stage normalizer
    for the smaller `A Q₂` block. -/
theorem GeneralizedQRFactorization.A_Q2_mgs_norm_ne_zero_of_stackedFullColumnRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hstack : LSEStackedFullColumnRank A B)
    (j : Fin q) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors (gqrAQ2Block A h.Q) j.val j) ≠ 0 :=
  h.A_Q2_mgs_norm_ne_zero_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    j
/-- Exact GQR method handoff for (20.27):
    if the transformed block vector `[y1; y2]` minimizes the transformed
    least-squares objective among all transformed feasible blocks
    `S z1 = d`, then `x = Q [y1; y2]` is an exact solution of the original
    equality-constrained least-squares problem.

    This is still supplied-factorization algebra.  It does not assert GQR
    existence, triangular nonsingularity, or floating-point stability. -/
theorem GeneralizedQRFactorization.isLSEMinimizer_of_transformed_block_minimizer
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    {y1 : Fin p → ℝ} {y2 : Fin q → ℝ}
    (hy1 : rectMatMulVec h.S y1 = d)
    (hmin : ∀ z1 : Fin p → ℝ, ∀ z2 : Fin q → ℝ,
      rectMatMulVec h.S z1 = d →
        lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
            (matMulVec (r + q) (matTranspose h.U) b)
            (Fin.append y1 y2) ≤
          lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
            (matMulVec (r + q) (matTranspose h.U) b)
            (Fin.append z1 z2)) :
    IsLSEMinimizer A b B d
      (matMulVec (p + q) h.Q (Fin.append y1 y2)) := by
  refine ⟨h.feasible_of_S_mulVec hy1, ?_⟩
  intro x hx
  let z : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) x
  let z1 : Fin p → ℝ := fun i => z (Fin.castAdd q i)
  let z2 : Fin q → ℝ := fun i => z (Fin.natAdd p i)
  have hz_append : Fin.append z1 z2 = z := by
    simpa [z1, z2] using finAppend_left_right (p := p) (q := q) z
  have hx_recover :
      matMulVec (p + q) h.Q (Fin.append z1 z2) = x := by
    rw [hz_append]
    exact matMulVec_orthogonal_mul_transpose h.orthQ x
  have hz_feasible : rectMatMulVec h.S z1 = d := by
    have hconstraint := h.constraint_eq z1 z2
    rw [hx_recover] at hconstraint
    ext i
    have hi := congrFun hconstraint i
    rw [← hi, hx i]
  calc
    lsObjective A b (matMulVec (p + q) h.Q (Fin.append y1 y2))
        = lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
            (matMulVec (r + q) (matTranspose h.U) b)
            (Fin.append y1 y2) := by
            exact (h.objective_eq_block b y1 y2).symm
    _ ≤ lsObjective (gqrAQBlock h.L11 h.L21 h.L22)
          (matMulVec (r + q) (matTranspose h.U) b)
          (Fin.append z1 z2) := hmin z1 z2 hz_feasible
    _ = lsObjective A b (matMulVec (p + q) h.Q (Fin.append z1 z2)) := by
            exact h.objective_eq_block b z1 z2
    _ = lsObjective A b x := by
            rw [hx_recover]
/-- The lower-triangular GQR constraint block `S` is a bijective solve map when
    its diagonal entries are nonzero.  This is the source-facing triangular
    nonsingularity bridge for Theorem 20.9, under supplied GQR data. -/
theorem GeneralizedQRFactorization.s_bijective_of_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hdiag : ∀ i : Fin p, h.S i i ≠ 0) :
    Function.Bijective (rectMatMulVec h.S) :=
  rectMatMulVec_bijective_of_lowerTriangular_diag_ne_zero h.lowerS hdiag
/-- The lower-triangular GQR block `L22` is a bijective solve map when its
    diagonal entries are nonzero.  This is the source-facing triangular
    nonsingularity bridge for Theorem 20.9, under supplied GQR data. -/
theorem GeneralizedQRFactorization.l22_bijective_of_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hdiag : ∀ i : Fin q, h.L22 i i ≠ 0) :
    Function.Bijective (rectMatMulVec h.L22) :=
  rectMatMulVec_bijective_of_lowerTriangular_diag_ne_zero h.lowerL22 hdiag
/-- Converse triangular nonsingularity bridge for the GQR constraint block
    `S`: a bijective square solve map has nonzero diagonal entries. -/
theorem GeneralizedQRFactorization.s_diag_ne_zero_of_bijective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hbij : Function.Bijective (rectMatMulVec h.S)) :
    ∀ i : Fin p, h.S i i ≠ 0 :=
  rectMatMulVec_diag_ne_zero_of_lowerTriangular_bijective h.lowerS hbij
/-- Converse triangular nonsingularity bridge for the GQR lower block `L22`:
    a bijective square solve map has nonzero diagonal entries. -/
theorem GeneralizedQRFactorization.l22_diag_ne_zero_of_bijective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hbij : Function.Bijective (rectMatMulVec h.L22)) :
    ∀ i : Fin q, h.L22 i i ≠ 0 :=
  rectMatMulVec_diag_ne_zero_of_lowerTriangular_bijective h.lowerL22 hbij
/-- Supplied-GQR lower-triangular nonsingularity equivalence for the
    constraint block `S`: nonzero diagonal entries are equivalent to bijective
    solvability of `S y = d`. -/
theorem GeneralizedQRFactorization.s_bijective_iff_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Bijective (rectMatMulVec h.S) ↔
      ∀ i : Fin p, h.S i i ≠ 0 := by
  constructor
  · exact h.s_diag_ne_zero_of_bijective
  · exact h.s_bijective_of_diag_ne_zero
/-- Supplied-GQR lower-triangular nonsingularity equivalence for the lower
    block `L22`: nonzero diagonal entries are equivalent to bijective
    solvability of `L22 y = e`. -/
theorem GeneralizedQRFactorization.l22_bijective_iff_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Bijective (rectMatMulVec h.L22) ↔
      ∀ i : Fin q, h.L22 i i ≠ 0 := by
  constructor
  · exact h.l22_diag_ne_zero_of_bijective
  · exact h.l22_bijective_of_diag_ne_zero
/-- Supplied-GQR equivalence for the first condition in (20.24):
    the local full-row-rank formulation for `B`, namely surjectivity of
    `x ↦ Bx`, is equivalent to surjectivity of the transformed square solve
    map `y1 ↦ S y1` in `B Q = [S 0]`.

    This is exact algebra for supplied GQR data.  It does not construct the
    GQR factors or prove a triangular determinant/numeric-rank theorem. -/
theorem GeneralizedQRFactorization.s_surjective_iff_lseFullRowRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Surjective (rectMatMulVec h.S) ↔ LSEFullRowRank B := by
  constructor
  · intro hS d
    rcases hS d with ⟨y1, hy1⟩
    let y2 : Fin q → ℝ := 0
    refine ⟨matMulVec (p + q) h.Q (Fin.append y1 y2), ?_⟩
    ext i
    have hc := congrFun (h.constraint_eq y1 y2) i
    simpa [lseConstraintLinearMap, hy1] using hc
  · intro hB d
    rcases hB d with ⟨x, hx⟩
    let z : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) x
    let z1 : Fin p → ℝ := fun i => z (Fin.castAdd q i)
    let z2 : Fin q → ℝ := fun i => z (Fin.natAdd p i)
    refine ⟨z1, ?_⟩
    have hz_append : Fin.append z1 z2 = z := by
      simpa [z1, z2] using finAppend_left_right (p := p) (q := q) z
    have hx_recover :
        matMulVec (p + q) h.Q (Fin.append z1 z2) = x := by
      rw [hz_append]
      exact matMulVec_orthogonal_mul_transpose h.orthQ x
    have hconstraint := h.constraint_eq z1 z2
    rw [hx_recover] at hconstraint
    ext i
    have hc := congrFun hconstraint i
    have hxi := congrFun hx i
    have hxi' : rectMatMulVec B x i = d i := by
      simpa [lseConstraintLinearMap] using hxi
    exact hc.symm.trans hxi'
/-- Supplied-GQR bijective form of the first condition in (20.24):
    because `S` is square, the local full-row-rank condition for `B` is
    equivalent to bijectivity of the solve map `y1 ↦ S y1`.

    The square surjective-to-injective step uses Mathlib finite-dimensional
    linear algebra; no triangular determinant theorem is claimed here. -/
theorem GeneralizedQRFactorization.s_bijective_iff_lseFullRowRank
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    Function.Bijective (rectMatMulVec h.S) ↔ LSEFullRowRank B := by
  constructor
  · intro hS
    exact (h.s_surjective_iff_lseFullRowRank).1 hS.2
  · intro hB
    have hsurj : Function.Surjective (rectMatMulVec h.S) :=
      (h.s_surjective_iff_lseFullRowRank).2 hB
    have hlinSurj : Function.Surjective (lseConstraintLinearMap h.S) := by
      simpa [lseConstraintLinearMap] using hsurj
    have hlinInj : Function.Injective (lseConstraintLinearMap h.S) :=
      (LinearMap.injective_iff_surjective).mpr hlinSurj
    have hinj : Function.Injective (rectMatMulVec h.S) := by
      simpa [lseConstraintLinearMap] using hlinInj
    exact ⟨hinj, hsurj⟩
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    `B^+`-parametric form of the lifted reduced-Gram left inverse on
    the homogeneous constraint nullspace.  The proof uses only the nullspace
    action of `AP = A(I-B^+B)`, so the supplied `Bplus` need not be the
    noncomputable `LSEFullRowRank.rightInverse`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_AP_left_inverse_on_nullspace_of_Bplus
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (Bplus : Fin (p + q) → Fin p → ℝ)
    (z : Fin (p + q) → ℝ)
    (hz : rectMatMulVec B z = (fun _i : Fin p => 0)) :
    rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (theorem20_8AP A B Bplus) z) = z := by
  have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
    (h.s_bijective_iff_lseFullRowRank).2 hB
  rcases (h.null_B_iff_exists_Q2_coord hS_bij.1 z).1 hz with
    ⟨y2, hzQ⟩
  have hzQ2 : z = rectMatMulVec h.Q2Basis y2 := by
    calc
      z = matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2) := hzQ
      _ = rectMatMulVec h.Q2Basis y2 := (h.Q2Basis_mulVec y2).symm
  have hAPz :
      rectMatMulVec (theorem20_8AP A B Bplus) z =
        rectMatMulVec A z :=
    theorem20_8AP_apply_nullspace A B Bplus z hz
  have hAz :
      rectMatMulVec A z =
        rectMatMulVec (gqrAQ2Block A h.Q) y2 := by
    rw [hzQ2]
    calc
      rectMatMulVec A (rectMatMulVec h.Q2Basis y2) =
          rectMatMulVec (rectMatMul A h.Q2Basis) y2 := by
            exact (rectMatMulVec_rectMatMul A h.Q2Basis y2).symm
      _ = rectMatMulVec (gqrAQ2Block A h.Q) y2 := by
            rw [h.A_mul_Q2Basis]
  have hred :=
    h.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstack
  have hCleft :
      rectMatMulVec
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMulVec (gqrAQ2Block A h.Q) y2) = y2 := by
    calc
      rectMatMulVec
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMulVec (gqrAQ2Block A h.Q) y2) =
          rectMatMulVec
            (rectMatMul
              (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
              (gqrAQ2Block A h.Q)) y2 := by
            exact
              (rectMatMulVec_rectMatMul
                (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
                (gqrAQ2Block A h.Q) y2).symm
      _ = rectMatMulVec (idMatrix q) y2 := by
            rw [hred.1]
      _ = y2 := rectMatMulVec_idMatrix y2
  calc
    rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (theorem20_8AP A B Bplus) z) =
        rectMatMulVec h.liftedReducedGramAPplus (rectMatMulVec A z) := by
          rw [hAPz]
    _ = rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (gqrAQ2Block A h.Q) y2) := by
          rw [hAz]
    _ = rectMatMulVec
        (rectMatMul h.Q2Basis
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)))
        (rectMatMulVec (gqrAQ2Block A h.Q) y2) := by
          rfl
    _ = rectMatMulVec h.Q2Basis
        (rectMatMulVec
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMulVec (gqrAQ2Block A h.Q) y2)) := by
          exact
            rectMatMulVec_rectMatMul h.Q2Basis
              (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
              (rectMatMulVec (gqrAQ2Block A h.Q) y2)
    _ = rectMatMulVec h.Q2Basis y2 := by
          rw [hCleft]
    _ = z := hzQ2.symm
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    under the source rank assumptions, the concrete lifted reduced-Gram
    candidate `Q₂ (A Q₂)^+` left-inverts the reduced operator `AP` on the
    homogeneous constraint nullspace.

    This is the GQR-specialized algebra behind `(AP)^+ AP z = z` for
    `B z = 0`: write `z = Q₂ y₂`, replace `AP z` by `A z`, and use the
    reduced Gram left-inverse for the `A Q₂` block. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_AP_left_inverse_on_nullspace
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (z : Fin (p + q) → ℝ)
    (hz : rectMatMulVec B z = (fun _i : Fin p => 0)) :
    rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z := by
  have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
    (h.s_bijective_iff_lseFullRowRank).2 hB
  rcases (h.null_B_iff_exists_Q2_coord hS_bij.1 z).1 hz with
    ⟨y2, hzQ⟩
  have hzQ2 : z = rectMatMulVec h.Q2Basis y2 := by
    calc
      z = matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) y2) := hzQ
      _ = rectMatMulVec h.Q2Basis y2 := (h.Q2Basis_mulVec y2).symm
  have hAPz :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse) z =
        rectMatMulVec A z :=
    theorem20_8AP_apply_nullspace A B hB.rightInverse z hz
  have hAz :
      rectMatMulVec A z =
        rectMatMulVec (gqrAQ2Block A h.Q) y2 := by
    rw [hzQ2]
    calc
      rectMatMulVec A (rectMatMulVec h.Q2Basis y2) =
          rectMatMulVec (rectMatMul A h.Q2Basis) y2 := by
            exact (rectMatMulVec_rectMatMul A h.Q2Basis y2).symm
      _ = rectMatMulVec (gqrAQ2Block A h.Q) y2 := by
            rw [h.A_mul_Q2Basis]
  have hred :=
    h.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstack
  have hCleft :
      rectMatMulVec
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMulVec (gqrAQ2Block A h.Q) y2) = y2 := by
    calc
      rectMatMulVec
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMulVec (gqrAQ2Block A h.Q) y2) =
          rectMatMulVec
            (rectMatMul
              (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
              (gqrAQ2Block A h.Q)) y2 := by
            exact
              (rectMatMulVec_rectMatMul
                (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
                (gqrAQ2Block A h.Q) y2).symm
      _ = rectMatMulVec (idMatrix q) y2 := by
            rw [hred.1]
      _ = y2 := rectMatMulVec_idMatrix y2
  calc
    rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) =
        rectMatMulVec h.liftedReducedGramAPplus (rectMatMulVec A z) := by
          rw [hAPz]
    _ = rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (gqrAQ2Block A h.Q) y2) := by
          rw [hAz]
    _ = rectMatMulVec
        (rectMatMul h.Q2Basis
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)))
        (rectMatMulVec (gqrAQ2Block A h.Q) y2) := by
          rfl
    _ = rectMatMulVec h.Q2Basis
        (rectMatMulVec
          (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
          (rectMatMulVec (gqrAQ2Block A h.Q) y2)) := by
          exact
            rectMatMulVec_rectMatMul h.Q2Basis
              (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q))
              (rectMatMulVec (gqrAQ2Block A h.Q) y2)
    _ = rectMatMulVec h.Q2Basis y2 := by
          rw [hCleft]
    _ = z := hzQ2.symm
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    the concrete lifted reduced-Gram candidate realizes the projected action
    `(AP)^+ AP v = P v` for the full-row-rank right-inverse projector. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_projected_action
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (v : Fin (p + q) → ℝ) :
    rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (theorem20_8AP A B hB.rightInverse) v) =
      rectMatMulVec (theorem20_8Projection B hB.rightInverse) v :=
  theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
    A B hB.rightInverse h.liftedReducedGramAPplus hB.rightInverse_spec
    (fun z hz =>
      h.liftedReducedGramAPplus_AP_left_inverse_on_nullspace hB hstack z hz)
    v
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    matrix form of the GQR-specialized projected-action identity
    `Q₂ (A Q₂)^+ AP = P`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_AP_eq_projection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    rectMatMul h.liftedReducedGramAPplus
        (theorem20_8AP A B hB.rightInverse) =
      theorem20_8Projection B hB.rightInverse :=
  theorem20_8_APplus_AP_eq_projection_of_AP_left_inverse_on_nullspace
    A B hB.rightInverse h.liftedReducedGramAPplus hB.rightInverse_spec
    (fun z hz =>
      h.liftedReducedGramAPplus_AP_left_inverse_on_nullspace hB hstack z hz)
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    the lifted reduced-Gram candidate satisfies the first Penrose reproduction
    equation for the reduced source product `AP`.

    This proves only the reproduction identity.  The symmetry fields needed for
    a full Moore--Penrose certificate remain separate obligations. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_reproduces_matrix
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    rectMatMul
        (rectMatMul (theorem20_8AP A B hB.rightInverse)
          h.liftedReducedGramAPplus)
        (theorem20_8AP A B hB.rightInverse) =
      theorem20_8AP A B hB.rightInverse := by
  calc
    rectMatMul
        (rectMatMul (theorem20_8AP A B hB.rightInverse)
          h.liftedReducedGramAPplus)
        (theorem20_8AP A B hB.rightInverse) =
        rectMatMul (theorem20_8AP A B hB.rightInverse)
          (rectMatMul h.liftedReducedGramAPplus
            (theorem20_8AP A B hB.rightInverse)) := by
          rw [rectMatMul_assoc]
    _ = rectMatMul (theorem20_8AP A B hB.rightInverse)
          (theorem20_8Projection B hB.rightInverse) := by
          rw [h.liftedReducedGramAPplus_AP_eq_projection hB hstack]
    _ = theorem20_8AP A B hB.rightInverse :=
          theorem20_8AP_mul_projection_eq_self
            A B hB.rightInverse hB.rightInverse_spec
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    the lifted reduced-Gram candidate satisfies the second Penrose reproduction
    equation for the reduced source product `AP`.

    This follows from `(AP)^+ AP = P` and the fact that the lifted candidate's
    columns lie in `null(B)`, so the source projector fixes them. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_reproduces_pseudoinverse
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    rectMatMul
        (rectMatMul h.liftedReducedGramAPplus
          (theorem20_8AP A B hB.rightInverse))
        h.liftedReducedGramAPplus =
      h.liftedReducedGramAPplus := by
  have hProjFix :
      rectMatMul (theorem20_8Projection B hB.rightInverse)
          h.liftedReducedGramAPplus =
        h.liftedReducedGramAPplus :=
    LSEFullRowRank.theorem20_8_APplus_projection_range_of_constraint_annihilates
      hB h.liftedReducedGramAPplus h.liftedReducedGramAPplus_constraint_annihilates
  calc
    rectMatMul
        (rectMatMul h.liftedReducedGramAPplus
          (theorem20_8AP A B hB.rightInverse))
        h.liftedReducedGramAPplus =
        rectMatMul (theorem20_8Projection B hB.rightInverse)
          h.liftedReducedGramAPplus := by
          rw [h.liftedReducedGramAPplus_AP_eq_projection hB hstack]
    _ = h.liftedReducedGramAPplus := hProjFix
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    the range projection `AP * Q₂(AQ₂)^+` for the lifted reduced-Gram
    candidate is exactly the reduced Gram projection `(AQ₂)(AQ₂)^+`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_range_projection_eq_reduced
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (Bplus : Fin (p + q) → Fin p → ℝ) :
    rectMatMul (theorem20_8AP A B Bplus) h.liftedReducedGramAPplus =
      rectMatMul (gqrAQ2Block A h.Q)
        (lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)) := by
  let Cplus : Fin q → Fin (r + q) → ℝ :=
    lsAplusOfGramNonsingInv (gqrAQ2Block A h.Q)
  have hPQ2 :
      rectMatMul (theorem20_8Projection B Bplus) h.Q2Basis = h.Q2Basis :=
    h.theorem20_8Projection_mul_Q2Basis_eq_self Bplus
  calc
    rectMatMul (theorem20_8AP A B Bplus) h.liftedReducedGramAPplus =
        rectMatMul (rectMatMul A (theorem20_8Projection B Bplus))
          (rectMatMul h.Q2Basis Cplus) := by
          rfl
    _ = rectMatMul A
          (rectMatMul (theorem20_8Projection B Bplus)
            (rectMatMul h.Q2Basis Cplus)) := by
          rw [rectMatMul_assoc]
    _ = rectMatMul A
          (rectMatMul
            (rectMatMul (theorem20_8Projection B Bplus) h.Q2Basis)
            Cplus) := by
          rw [← rectMatMul_assoc
            (theorem20_8Projection B Bplus) h.Q2Basis Cplus]
    _ = rectMatMul A (rectMatMul h.Q2Basis Cplus) := by
          rw [hPQ2]
    _ = rectMatMul (rectMatMul A h.Q2Basis) Cplus := by
          rw [← rectMatMul_assoc]
    _ = rectMatMul (gqrAQ2Block A h.Q) Cplus := by
          rw [h.A_mul_Q2Basis]
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    the range-projection symmetry Penrose field for the lifted reduced-Gram
    candidate follows from the reduced Gram-pseudoinverse symmetry. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_range_projection_symmetric
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (Bplus : Fin (p + q) → Fin p → ℝ)
    (hstack : LSEStackedFullColumnRank A B) :
    IsSymmetricFiniteMatrix
      (rectMatMul (theorem20_8AP A B Bplus) h.liftedReducedGramAPplus) := by
  rw [h.liftedReducedGramAPplus_range_projection_eq_reduced Bplus]
  exact (h.A_Q2_reduced_gram_left_inverse_and_projection_symmetric hstack).2
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    the lifted reduced-Gram candidate realizes the projected action
    `(AP)^+ AP v = P v` for any source right inverse `B^+`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_projected_action_of_rightInverse
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (Bplus : Fin (p + q) → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (v : Fin (p + q) → ℝ) :
    rectMatMulVec h.liftedReducedGramAPplus
        (rectMatMulVec (theorem20_8AP A B Bplus) v) =
      rectMatMulVec (theorem20_8Projection B Bplus) v :=
  theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
    A B Bplus h.liftedReducedGramAPplus hright
    (fun z hz =>
      h.liftedReducedGramAPplus_AP_left_inverse_on_nullspace_of_Bplus
        hB hstack Bplus z hz)
    v
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    matrix form `Q₂(AQ₂)^+ AP = P` for any source right inverse `B^+`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_AP_eq_projection_of_rightInverse
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (Bplus : Fin (p + q) → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p) :
    rectMatMul h.liftedReducedGramAPplus (theorem20_8AP A B Bplus) =
      theorem20_8Projection B Bplus :=
  theorem20_8_APplus_AP_eq_projection_of_AP_left_inverse_on_nullspace
    A B Bplus h.liftedReducedGramAPplus hright
    (fun z hz =>
      h.liftedReducedGramAPplus_AP_left_inverse_on_nullspace_of_Bplus
        hB hstack Bplus z hz)
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    first Penrose reproduction equation for the lifted reduced-Gram candidate
    and any source right inverse `B^+`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_reproduces_matrix_of_rightInverse
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (Bplus : Fin (p + q) → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p) :
    rectMatMul
        (rectMatMul (theorem20_8AP A B Bplus)
          h.liftedReducedGramAPplus)
        (theorem20_8AP A B Bplus) =
      theorem20_8AP A B Bplus := by
  calc
    rectMatMul
        (rectMatMul (theorem20_8AP A B Bplus)
          h.liftedReducedGramAPplus)
        (theorem20_8AP A B Bplus) =
        rectMatMul (theorem20_8AP A B Bplus)
          (rectMatMul h.liftedReducedGramAPplus
            (theorem20_8AP A B Bplus)) := by
          rw [rectMatMul_assoc]
    _ = rectMatMul (theorem20_8AP A B Bplus)
          (theorem20_8Projection B Bplus) := by
          rw [h.liftedReducedGramAPplus_AP_eq_projection_of_rightInverse
            hB hstack Bplus hright]
    _ = theorem20_8AP A B Bplus :=
          theorem20_8AP_mul_projection_eq_self A B Bplus hright
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    second Penrose reproduction equation for the lifted reduced-Gram candidate
    and any source right inverse `B^+`. -/
theorem GeneralizedQRFactorization.liftedReducedGramAPplus_reproduces_pseudoinverse_of_rightInverse
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (Bplus : Fin (p + q) → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p) :
    rectMatMul
        (rectMatMul h.liftedReducedGramAPplus
          (theorem20_8AP A B Bplus))
        h.liftedReducedGramAPplus =
      h.liftedReducedGramAPplus := by
  have hProjFix :
      rectMatMul (theorem20_8Projection B Bplus)
          h.liftedReducedGramAPplus =
        h.liftedReducedGramAPplus :=
    theorem20_8_APplus_projection_range_of_constraint_annihilates
      B Bplus h.liftedReducedGramAPplus
      h.liftedReducedGramAPplus_constraint_annihilates
  calc
    rectMatMul
        (rectMatMul h.liftedReducedGramAPplus
          (theorem20_8AP A B Bplus))
        h.liftedReducedGramAPplus =
        rectMatMul (theorem20_8Projection B Bplus)
          h.liftedReducedGramAPplus := by
          rw [h.liftedReducedGramAPplus_AP_eq_projection_of_rightInverse
            hB hstack Bplus hright]
    _ = h.liftedReducedGramAPplus := hProjFix
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    conditional Moore--Penrose certificate for the lifted reduced-Gram
    candidate.  The remaining source-side symmetry obligation is exactly the
    symmetry of the domain projector `I-B^+B`. -/
theorem
    GeneralizedQRFactorization.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_projection_symmetric
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B)
    (Bplus : Fin (p + q) → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hPsym : IsSymmetricFiniteMatrix (theorem20_8Projection B Bplus)) :
    RectMoorePenrosePseudoinverse (r + q) (p + q)
      (theorem20_8AP A B Bplus) h.liftedReducedGramAPplus := by
  constructor
  · exact h.liftedReducedGramAPplus_reproduces_matrix_of_rightInverse
      hB hstack Bplus hright
  · exact h.liftedReducedGramAPplus_reproduces_pseudoinverse_of_rightInverse
      hB hstack Bplus hright
  · exact h.liftedReducedGramAPplus_range_projection_symmetric Bplus hstack
  · rw [h.liftedReducedGramAPplus_AP_eq_projection_of_rightInverse
      hB hstack Bplus hright]
    exact hPsym
/-- Higham, 2nd ed., Chapter 20, equation (20.24) and Theorem 20.9 support:
    concrete Moore--Penrose certificate for the lifted reduced-Gram candidate
    using the source Gram pseudoinverse `Bᵀ(BBᵀ)⁻¹` as `B^+`. -/
theorem
    GeneralizedQRFactorization.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    RectMoorePenrosePseudoinverse (r + q) (p + q)
      (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
      h.liftedReducedGramAPplus :=
  h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_projection_symmetric
    hB hstack (undetAplusOfGramNonsingInv B)
    (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      B hB.rectGram_det_ne_zero)
    (theorem20_8Projection_symmetric_of_gram_pseudoinverse B)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    determinant-free existence of a rank-tolerant `(AP)^+` candidate.

    Source full row rank of `B` and stacked full column rank of `[A;B]`
    construct exact GQR data.  The lifted reduced-Gram table supplied by that
    data is a Moore--Penrose pseudoinverse of `AP = A(I-B^+B)` and has columns
    in `null(B)`.  This packages the viable rank-tolerant route after the
    concrete `det(rectGram(AP))` shortcut has been ruled out. -/
theorem LSEFullRowRank.exists_theorem20_8_rank_tolerant_APplus_MP_gram_projection
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hstack : LSEStackedFullColumnRank A B) :
    ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
      RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
        rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) := by
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hstack with
    ⟨h⟩
  exact
    ⟨h.liftedReducedGramAPplus,
      h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
        hB hstack,
      h.liftedReducedGramAPplus_constraint_annihilates⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    for supplied GQR data, `B` has full row rank iff the displayed
    lower-triangular constraint block `S` has trivial kernel.

    This is the source proof sentence "B has full rank if and only if S is
    nonsingular" in kernel form.  It does not construct the GQR factors. -/
theorem GeneralizedQRFactorization.lseFullRowRank_iff_s_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    LSEFullRowRank B ↔
      ∀ y1 : Fin p → ℝ, rectMatMulVec h.S y1 = 0 → y1 = 0 := by
  constructor
  · intro hB y1 hy1
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_lseFullRowRank).2 hB
    apply hS_bij.1
    rw [hy1, rectMatMulVec_zero]
  · intro hker
    have hS_inj : Function.Injective (rectMatMulVec h.S) := by
      intro y1 z1 hyz
      let w : Fin p → ℝ := fun i => y1 i - z1 i
      have hSw : rectMatMulVec h.S w = 0 := by
        ext i
        have hi := congrFun hyz i
        have hsub := congrFun (rectMatMulVec_sub h.S y1 z1) i
        dsimp [w]
        rw [hsub, hi]
        ring
      have hw : w = 0 := hker w hSw
      ext i
      have hwi := congrFun hw i
      dsimp [w] at hwi
      linarith
    have hS_diag : ∀ i : Fin p, h.S i i ≠ 0 :=
      rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective
        h.lowerS hS_inj
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_diag_ne_zero).2 hS_diag
    exact (h.s_bijective_iff_lseFullRowRank).1 hS_bij
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    for supplied GQR data, `B` has full row rank iff the lower-triangular
    constraint block `S` has nonzero diagonal entries.

    This is the source proof sentence "B has full rank if and only if S is
    nonsingular" in triangular diagonal form. -/
theorem GeneralizedQRFactorization.lseFullRowRank_iff_s_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B) :
    LSEFullRowRank B ↔
      ∀ i : Fin p, h.S i i ≠ 0 := by
  constructor
  · intro hB
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_lseFullRowRank).2 hB
    exact (h.s_bijective_iff_diag_ne_zero).1 hS_bij
  · intro hS_diag
    have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
      (h.s_bijective_iff_diag_ne_zero).2 hS_diag
    exact (h.s_bijective_iff_lseFullRowRank).1 hS_bij
/-- Supplied-GQR equivalence for the second condition in (20.24):
    once the constraint block `S` is injective, the null-intersection
    condition `null(A) ∩ null(B) = {0}` is equivalent to injectivity of the
    lower-right block solve map `y2 ↦ L22 y2`.

    This is the exact block-algebra part of the source statement that the
    assumptions (20.24) correspond to nonsingularity of `S` and `L22`.  It does
    not prove GQR existence, (20.28), or any floating-point stability theorem. -/
theorem GeneralizedQRFactorization.nullIntersectionTrivial_iff_l22_injective
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_inj : Function.Injective (rectMatMulVec h.S)) :
    LSENullIntersectionTrivial A B ↔
      Function.Injective (rectMatMulVec h.L22) := by
  constructor
  · intro hnull y2 z2 hyz
    let w : Fin q → ℝ := fun i => y2 i - z2 i
    have hLw : rectMatMulVec h.L22 w = 0 := by
      ext i
      have hi := congrFun hyz i
      have hsub := congrFun (rectMatMulVec_sub h.L22 y2 z2) i
      dsimp [w]
      rw [hsub, hi]
      ring
    let y : Fin (p + q) → ℝ := Fin.append (0 : Fin p → ℝ) w
    let v : Fin (p + q) → ℝ := matMulVec (p + q) h.Q y
    have hBv : rectMatMulVec B v = 0 := by
      have hc := h.constraint_eq (0 : Fin p → ℝ) w
      change
        rectMatMulVec B
          (matMulVec (p + q) h.Q (Fin.append (0 : Fin p → ℝ) w)) = 0
      rw [hc]
      exact rectMatMulVec_zero h.S
    have hblock :
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q)) y = 0 := by
      have hb := h.transformed_A_mulVec_eq_block (0 : Fin p → ℝ) w
      change
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q))
          (Fin.append (0 : Fin p → ℝ) w) = 0
      rw [hb]
      ext i
      refine Fin.addCases
        (motive := fun i : Fin (r + q) =>
          Fin.append (rectMatMulVec h.L11 (0 : Fin p → ℝ))
            (fun i : Fin q =>
              rectMatMulVec h.L21 (0 : Fin p → ℝ) i +
                rectMatMulVec h.L22 w i) i =
              (0 : Fin (r + q) → ℝ) i)
        ?left ?right i
      · intro i
        simp [Fin.append_left, rectMatMulVec]
      · intro i
        have hi := congrFun hLw i
        simpa [Fin.append_right, rectMatMulVec] using hi
    have hAv : rectMatMulVec A v = 0 := by
      change rectMatMulVec A (matMulVec (p + q) h.Q y) = 0
      exact h.A_zero_of_transformed_A_zero hblock
    have hvzero : v = 0 := hnull v hAv hBv
    have hyzero : y = 0 := by
      have hrec := matMulVec_orthogonal_transpose_mul h.orthQ y
      dsimp [v] at hvzero
      rw [hvzero, matMulVec_zero] at hrec
      exact hrec.symm
    ext i
    have hwi : w i = 0 := by
      have hi := congrFun hyzero (Fin.natAdd p i)
      simpa [y, w, Fin.append_right] using hi
    dsimp [w] at hwi
    linarith
  · intro hL22 v hAv hBv
    let y : Fin (p + q) → ℝ := matMulVec (p + q) (matTranspose h.Q) v
    let y1 : Fin p → ℝ := fun i => y (Fin.castAdd q i)
    let y2 : Fin q → ℝ := fun i => y (Fin.natAdd p i)
    have hy_append : Fin.append y1 y2 = y := by
      simpa [y1, y2] using finAppend_left_right (p := p) (q := q) y
    have hv_recover :
        matMulVec (p + q) h.Q (Fin.append y1 y2) = v := by
      rw [hy_append]
      exact matMulVec_orthogonal_mul_transpose h.orthQ v
    have hSy1 : rectMatMulVec h.S y1 = 0 := by
      have hc := h.constraint_eq y1 y2
      rw [hv_recover] at hc
      rw [hBv] at hc
      exact hc.symm
    have hy1_zero : y1 = 0 := by
      apply hS_inj
      rw [hSy1, rectMatMulVec_zero]
    have htrans_zero :
        rectMatMulVec
          (matMulRectLeft (matTranspose h.U)
            (matMulRect (r + q) (p + q) (p + q) A h.Q))
          (Fin.append y1 y2) = 0 := by
      have hAv' :
          rectMatMulVec A
            (matMulVec (p + q) h.Q (Fin.append y1 y2)) = 0 := by
        rw [hv_recover]
        exact hAv
      exact h.transformed_A_zero_of_A_zero hAv'
    have hblock := h.transformed_A_mulVec_eq_block y1 y2
    rw [htrans_zero] at hblock
    have hL22y2 : rectMatMulVec h.L22 y2 = 0 := by
      ext i
      have hi := congrFun hblock (Fin.natAdd r i)
      have hi0 :
          (0 : Fin (r + q) → ℝ) (Fin.natAdd r i) =
            rectMatMulVec h.L21 y1 i + rectMatMulVec h.L22 y2 i := by
        simpa [Fin.append_right] using hi
      have hy1i : rectMatMulVec h.L21 y1 i = 0 := by
        rw [hy1_zero]
        simp [rectMatMulVec]
      have hiL : 0 = rectMatMulVec h.L22 y2 i := by
        simpa [hy1i] using hi0
      exact hiL.symm
    have hy2_zero : y2 = 0 := by
      apply hL22
      rw [hL22y2, rectMatMulVec_zero]
    have hy_zero : Fin.append y1 y2 = 0 := by
      rw [hy1_zero, hy2_zero]
      ext i
      exact Fin.addCases
        (motive := fun i : Fin (p + q) =>
          Fin.append (0 : Fin p → ℝ) (0 : Fin q → ℝ) i =
            (0 : Fin (p + q) → ℝ) i)
        (fun i => by simp [Fin.append_left])
        (fun i => by simp [Fin.append_right])
        i
    rw [← hv_recover, hy_zero]
    exact matMulVec_zero h.Q
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    assuming the GQR constraint block `S` is nonsingular, the condition
    `null(A) ∩ null(B) = {0}` is equivalent to the displayed `L22` block
    having trivial kernel.

    This names the source proof step `AQ₂ = U₂ L22` in kernel form, under
    supplied GQR data.  It is not a GQR existence theorem. -/
theorem GeneralizedQRFactorization.nullIntersectionTrivial_iff_l22_kernel_trivial
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_inj : Function.Injective (rectMatMulVec h.S)) :
    LSENullIntersectionTrivial A B ↔
      ∀ y2 : Fin q → ℝ, rectMatMulVec h.L22 y2 = 0 → y2 = 0 := by
  constructor
  · intro hnull y2 hy2
    have hL22_inj : Function.Injective (rectMatMulVec h.L22) :=
      (h.nullIntersectionTrivial_iff_l22_injective hS_inj).1 hnull
    apply hL22_inj
    rw [hy2, rectMatMulVec_zero]
  · intro hker
    have hL22_inj : Function.Injective (rectMatMulVec h.L22) := by
      intro y2 z2 hyz
      let w : Fin q → ℝ := fun i => y2 i - z2 i
      have hLw : rectMatMulVec h.L22 w = 0 := by
        ext i
        have hi := congrFun hyz i
        have hsub := congrFun (rectMatMulVec_sub h.L22 y2 z2) i
        dsimp [w]
        rw [hsub, hi]
        ring
      have hw : w = 0 := hker w hLw
      ext i
      have hwi := congrFun hw i
      dsimp [w] at hwi
      linarith
    exact (h.nullIntersectionTrivial_iff_l22_injective hS_inj).2 hL22_inj
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 proof after (20.28):
    once the GQR constraint block `S` is nonsingular, the local
    null-intersection condition is equivalent to nonsingularity of the
    lower-triangular `L22` block, expressed as nonzero diagonal entries.

    This is the conditional form of the source sentence before the combined
    `(20.24)`-to-`S`/`L22` equivalence below. -/
theorem GeneralizedQRFactorization.nullIntersectionTrivial_iff_l22_diag_ne_zero_of_s_diag_ne_zero
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (hS_diag : ∀ i : Fin p, h.S i i ≠ 0) :
    LSENullIntersectionTrivial A B ↔
      ∀ i : Fin q, h.L22 i i ≠ 0 := by
  have hS_bij : Function.Bijective (rectMatMulVec h.S) :=
    (h.s_bijective_iff_diag_ne_zero).2 hS_diag
  have hS_inj : Function.Injective (rectMatMulVec h.S) := hS_bij.1
  constructor
  · intro hnull
    have hL22_inj : Function.Injective (rectMatMulVec h.L22) :=
      (h.nullIntersectionTrivial_iff_l22_injective hS_inj).1 hnull
    exact rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective
      h.lowerL22 hL22_inj
  · intro hL22_diag
    have hL22_bij : Function.Bijective (rectMatMulVec h.L22) :=
      (h.l22_bijective_iff_diag_ne_zero).2 hL22_diag
    exact (h.nullIntersectionTrivial_iff_l22_injective hS_inj).2
      hL22_bij.1
/-- Higham, 2nd ed., Chapter 20, equations (20.29)-(20.30):
    exact minimizer handoff for the elimination method.

    If `x2` minimizes the reduced unconstrained problem obtained after
    eliminating `x1`, then `[R1^{-1}(qtd - R2 x2); x2]` is an exact minimizer of
    the equality-constrained least-squares problem with coefficient blocks
    `[A1 A2]` and constraint blocks `[R1 R2]`. The theorem assumes the inverse
    action for `R1` is supplied in both orders; it does not construct the
    pivoted QR factorization or prove `R1` nonsingular. -/
theorem lseElimination_isLSEMinimizer_of_reduced_minimizer {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ)
    (hleft : ∀ v : Fin p → ℝ, rectMatMulVec R1 (rectMatMulVec R1inv v) = v)
    (hright : ∀ v : Fin p → ℝ, rectMatMulVec R1inv (rectMatMulVec R1 v) = v)
    (hmin : IsLSEEliminationReducedMinimizer A1 A2 R1inv R2 qtd b x2) :
    IsLSEMinimizer (lseEliminationBlockMatrix A1 A2) b
      (lseEliminationBlockMatrix R1 R2) qtd
      (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) := by
  refine ⟨?feasible, ?minimal⟩
  · intro i
    exact congrFun
      (lseEliminationBlockConstraint_eq_qtd_of_left_inverse
        R1 R1inv R2 qtd x2 hleft) i
  · intro y hy
    let y1 : Fin p → ℝ := fun i => y (Fin.castAdd q i)
    let y2 : Fin q → ℝ := fun i => y (Fin.natAdd p i)
    have hy_append : Fin.append y1 y2 = y := by
      simpa [y1, y2] using finAppend_left_right (p := p) (q := q) y
    have hy_constraint :
        rectMatMulVec (lseEliminationBlockMatrix R1 R2) (Fin.append y1 y2) =
          qtd := by
      ext i
      rw [hy_append]
      exact hy i
    have hy1_eq :
        y1 = lseEliminationBackSubstitution R1inv R2 qtd y2 :=
      lseEliminationBackSubstitution_eq_of_block_constraint
        R1 R1inv R2 qtd y1 y2 hright hy_constraint
    have hy_eq :
        y = Fin.append (lseEliminationBackSubstitution R1inv R2 qtd y2) y2 := by
      rw [← hy_append, hy1_eq]
    calc
      lsObjective (lseEliminationBlockMatrix A1 A2) b
          (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2)
          =
            lseEliminationReducedObjective A1 A2 R1inv R2 qtd b x2 := by
              exact lseEliminationObjective_eq_reduced A1 A2 R1inv R2 qtd b x2
      _ ≤ lseEliminationReducedObjective A1 A2 R1inv R2 qtd b y2 :=
            hmin y2
      _ =
          lsObjective (lseEliminationBlockMatrix A1 A2) b
            (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd y2) y2) := by
            exact (lseEliminationObjective_eq_reduced
              A1 A2 R1inv R2 qtd b y2).symm
      _ = lsObjective (lseEliminationBlockMatrix A1 A2) b y := by
            rw [hy_eq]
/-- Higham, 2nd ed., Chapter 20, equations (20.29)-(20.30):
    original-coordinate form of the elimination minimizer handoff.

    If column pivoting gives `BΠ = [R1 R2]` and `AΠ = [A1 A2]`, then a
    minimizer of the reduced unconstrained problem in (20.30), combined with
    the back-substitution in (20.29) and pulled back by `Πᵀ`, is an exact
    minimizer of the original equality-constrained problem. The theorem uses
    supplied partition and inverse-action data; it does not construct the
    pivoted QR factorization or prove `R1` nonsingular. -/
theorem lseElimination_isLSEMinimizer_original_of_reduced_minimizer
    {m p q : ℕ} (π : Fin (p + q) ≃ Fin (p + q))
    (A : Fin m → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ)
    (hAπ : rectPermuteCols π A = lseEliminationBlockMatrix A1 A2)
    (hBπ : rectPermuteCols π B = lseEliminationBlockMatrix R1 R2)
    (hleft : ∀ v : Fin p → ℝ, rectMatMulVec R1 (rectMatMulVec R1inv v) = v)
    (hright : ∀ v : Fin p → ℝ, rectMatMulVec R1inv (rectMatMulVec R1 v) = v)
    (hmin : IsLSEEliminationReducedMinimizer A1 A2 R1inv R2 qtd b x2) :
    IsLSEMinimizer A b B qtd
      (vecPermute π.symm
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2)) := by
  apply IsLSEMinimizer.of_permuteCols π
  simpa [hAπ, hBπ] using
    (lseElimination_isLSEMinimizer_of_reduced_minimizer
      A1 A2 R1 R1inv R2 qtd b x2 hleft hright hmin)
/-- Homogeneous uniqueness for the source equality-constrained KKT augmented
    system under Higham's conditions (20.24).

    This is the nonsingularity kernel for the Cox--Higham block-inverse route:
    with zero data, stationarity, and constraint right-hand sides, the residual,
    solution, and multiplier components are all zero. -/
theorem LSEKKTSystem.eq_zero_of_homogeneous {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B)
    {dr : Fin m → ℝ} {dx : Fin n → ℝ} {dlambda : Fin p → ℝ}
    (hsys : LSEKKTSystem A B (0 : Fin m → ℝ) (0 : Fin n → ℝ)
      (0 : Fin p → ℝ) dr dx dlambda) :
    dr = 0 ∧ dx = 0 ∧ dlambda = 0 := by
  rcases hsys with ⟨htop, hstat, hconstr⟩
  have hA_dot :
      (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i)) =
        ∑ i : Fin m, rectMatMulVec A dx i * dr i := by
    calc
      (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i))
          = ∑ j : Fin n, ∑ i : Fin m, dx j * (A i j * dr i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ j : Fin n, dx j * (A i j * dr i) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin m, rectMatMulVec A dx i * dr i := by
              apply Finset.sum_congr rfl
              intro i _
              calc
                (∑ j : Fin n, dx j * (A i j * dr i))
                    = ∑ j : Fin n, (A i j * dx j) * dr i := by
                        apply Finset.sum_congr rfl
                        intro j _
                        ring
                _ = (∑ j : Fin n, A i j * dx j) * dr i := by
                        rw [Finset.sum_mul]
                _ = rectMatMulVec A dx i * dr i := rfl
  have hB_dot :
      (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r)) =
        ∑ r : Fin p, rectMatMulVec B dx r * dlambda r := by
    calc
      (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r))
          = ∑ j : Fin n, ∑ r : Fin p, dx j * (B r j * dlambda r) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
      _ = ∑ r : Fin p, ∑ j : Fin n, dx j * (B r j * dlambda r) := by
              rw [Finset.sum_comm]
      _ = ∑ r : Fin p, rectMatMulVec B dx r * dlambda r := by
              apply Finset.sum_congr rfl
              intro r _
              calc
                (∑ j : Fin n, dx j * (B r j * dlambda r))
                    = ∑ j : Fin n, (B r j * dx j) * dlambda r := by
                        apply Finset.sum_congr rfl
                        intro j _
                        ring
                _ = (∑ j : Fin n, B r j * dx j) * dlambda r := by
                        rw [Finset.sum_mul]
                _ = rectMatMulVec B dx r * dlambda r := rfl
  have hstation_sum :
      (∑ j : Fin n,
        dx j *
          ((∑ i : Fin m, A i j * dr i) -
            (∑ r : Fin p, B r j * dlambda r))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : (∑ i : Fin m, A i j * dr i) -
        (∑ r : Fin p, B r j * dlambda r) = 0 := by
      simpa using hstat j
    rw [hj]
    ring
  have hstation_split :
      (∑ j : Fin n,
        dx j *
          ((∑ i : Fin m, A i j * dr i) -
            (∑ r : Fin p, B r j * dlambda r))) =
        (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i)) -
          (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstation_source :
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) -
          (∑ r : Fin p, rectMatMulVec B dx r * dlambda r) = 0 := by
    calc
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) -
          (∑ r : Fin p, rectMatMulVec B dx r * dlambda r)
          = (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i)) -
              (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r)) := by
              rw [hA_dot, hB_dot]
      _ = (∑ j : Fin n,
            dx j *
              ((∑ i : Fin m, A i j * dr i) -
                (∑ r : Fin p, B r j * dlambda r))) := by
              rw [hstation_split]
      _ = 0 := hstation_sum
  have hBdot_zero :
      (∑ r : Fin p, rectMatMulVec B dx r * dlambda r) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have hr : rectMatMulVec B dx r = 0 := by
      simpa using hconstr r
    rw [hr]
    ring
  have hAdot_zero :
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) = 0 := by
    linarith
  have hAdx_neg : ∀ i : Fin m, rectMatMulVec A dx i = -dr i := by
    intro i
    have hi : dr i + rectMatMulVec A dx i = 0 := by
      simpa using htop i
    linarith
  have hAdot_eq_neg_sq :
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) = -vecNorm2Sq dr := by
    unfold vecNorm2Sq
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hAdx_neg i]
    ring
  have hdrsq : vecNorm2Sq dr = 0 := by
    linarith
  have hdrnorm : vecNorm2 dr = 0 := by
    unfold vecNorm2
    rw [Real.sqrt_eq_zero (vecNorm2Sq_nonneg dr)]
    exact hdrsq
  have hdr_zero : dr = 0 := by
    ext i
    exact (vecNorm2_eq_zero_iff dr).mp hdrnorm i
  have hAdx_zero : rectMatMulVec A dx = 0 := by
    ext i
    change rectMatMulVec A dx i = 0
    have hi : dr i + rectMatMulVec A dx i = 0 := by
      simpa using htop i
    have hdri : dr i = 0 := by
      simpa using congrFun hdr_zero i
    linarith
  have hBdx_zero : rectMatMulVec B dx = 0 := by
    ext r
    change rectMatMulVec B dx r = 0
    simpa using hconstr r
  have hdx_zero : dx = 0 := hnull dx hAdx_zero hBdx_zero
  have hBt_zero :
      rectMatMulVec (fun j : Fin n => fun r : Fin p => B r j) dlambda = 0 := by
    ext j
    change (∑ r : Fin p, B r j * dlambda r) = 0
    have hj : (∑ i : Fin m, A i j * dr i) -
        (∑ r : Fin p, B r j * dlambda r) = 0 := by
      simpa using hstat j
    have hArow_zero : (∑ i : Fin m, A i j * dr i) = 0 := by
      rw [hdr_zero]
      simp
    linarith
  have hdlambda_zero : dlambda = 0 := by
    apply hB.transpose_rectMatMulVec_injective
    rw [hBt_zero, rectMatMulVec_zero]
  exact ⟨hdr_zero, hdx_zero, hdlambda_zero⟩
/-- A source LSE Lagrange multiplier satisfying the normal equations solves the
    source KKT system with right-hand side `(r,0,0)`, where
    `r = b - A*x` is Higham's signed residual. -/
theorem LSEKKTSystem.sourceResidual_of_lagrange_normal_equations {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {x : Fin n → ℝ}
    {lambda : Fin p → ℝ}
    (hnormal : ∀ j : Fin n,
      ∑ i : Fin m, A i j * lsResidualHigham A b x i =
        ∑ r : Fin p, B r j * lambda r) :
    LSEKKTSystem A B (lsResidualHigham A b x) 0 0
      (lsResidualHigham A b x) 0 lambda := by
  constructor
  · intro i
    rw [congrFun (rectMatMulVec_zero A) i]
    simp
  · constructor
    · intro j
      rw [hnormal j]
      simp
    · intro r
      rw [congrFun (rectMatMulVec_zero B) r]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    first lower-triangular solve `S y₁ = d`. -/
noncomputable def theorem20_10_gqr_y1hat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (d : Fin p → ℝ) : Fin p → ℝ :=
  fl_forwardSub fp p h.S d
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    right-hand side for the trailing lower-triangular solve. -/
noncomputable def theorem20_10_gqr_rhs2hat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fun i : Fin q =>
    matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
      rectMatMulVec h.L21 (theorem20_10_gqr_y1hat fp h d) i
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    second lower-triangular solve `L₂₂ y₂ = Uᵀb - L₂₁y₁`. -/
noncomputable def theorem20_10_gqr_y2hat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fl_forwardSub fp q h.L22 (theorem20_10_gqr_rhs2hat fp h b d)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    final computed vector `xhat = Q [y₁hat; y₂hat]` for supplied GQR data.

    This definition names the computed path; it does not by itself prove that
    the vector is a minimizer of a perturbed LSE problem. -/
noncomputable def theorem20_10_gqr_xhat
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) : Fin (p + q) → ℝ :=
  matMulVec (p + q) h.Q
    (Fin.append
      (theorem20_10_gqr_y1hat fp h d)
      (theorem20_10_gqr_y2hat fp h b d))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    right-hand side for the trailing lower-triangular solve when the trailing
    transformed vector has already been computed or perturbed.

    This variant is the bridge needed for the rounded Householder RHS path:
    `beta` represents the trailing entries of the transformed right-hand side,
    rather than forcing the exact vector `Uᵀ b`. -/
noncomputable def theorem20_10_gqr_rhs2hat_of_transformed_tail
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fun i : Fin q =>
    beta i - rectMatMulVec h.L21 (theorem20_10_gqr_y1hat fp h d) i
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    second lower-triangular solve driven by a supplied trailing transformed
    right-hand side. -/
noncomputable def theorem20_10_gqr_y2hat_of_transformed_tail
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ) : Fin q → ℝ :=
  fl_forwardSub fp q h.L22
    (theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    final vector for the supplied-trailing-RHS computed path. -/
noncomputable def theorem20_10_gqr_xhat_of_transformed_tail
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (fp : FPModel) (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ) : Fin (p + q) → ℝ :=
  matMulVec (p + q) h.Q
    (Fin.append
      (theorem20_10_gqr_y1hat fp h d)
      (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    exact trailing block of the transformed right-hand side `Uᵀ b`.

    This names the specialization point at which the supplied-transformed-tail
    API reduces to the ordinary computed GQR path. -/
noncomputable def theorem20_10_gqr_exact_transformed_tail
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) : Fin q → ℝ :=
  fun i : Fin q =>
    matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    the supplied-transformed-tail trailing RHS reduces to the ordinary GQR RHS
    when the supplied tail is the exact trailing block of `Uᵀ b`. -/
theorem theorem20_10_gqr_rhs2hat_of_exact_transformed_tail_eq
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) :
    theorem20_10_gqr_rhs2hat_of_transformed_tail fp h
        (theorem20_10_gqr_exact_transformed_tail h b) d =
      theorem20_10_gqr_rhs2hat fp h b d := by
  rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    the supplied-transformed-tail second triangular solve reduces to the
    ordinary GQR second solve at the exact tail `Uᵀ b`. -/
theorem theorem20_10_gqr_y2hat_of_exact_transformed_tail_eq
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) :
    theorem20_10_gqr_y2hat_of_transformed_tail fp h
        (theorem20_10_gqr_exact_transformed_tail h b) d =
      theorem20_10_gqr_y2hat fp h b d := by
  rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    the supplied-transformed-tail returned vector reduces to the ordinary
    computed GQR returned vector at the exact tail `Uᵀ b`. -/
theorem theorem20_10_gqr_xhat_of_exact_transformed_tail_eq
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ) :
    theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_gqr_exact_transformed_tail h b) d =
      theorem20_10_gqr_xhat fp h b d := by
  rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    trailing entries of the rounded Householder RHS transform for the `A Q₂`
    panel. -/
noncomputable def theorem20_10_householder_AQ2_rhs_tail
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) : Fin q → ℝ :=
  fun i : Fin q =>
    fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b
      (Fin.natAdd r i)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    trailing entries of the rounded Householder RHS transform for the
    column-reversed `A Q₂` panel used by the constructed GQR `L₂₂` path. -/
noncomputable def theorem20_10_householder_reversed_AQ2_rhs_tail
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) : Fin q → ℝ :=
  fun j : Fin q =>
    fl_householderQRPanel_rhs fp (r + q) q
        (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)) b
      (Fin.cast (Nat.add_comm q r) (Fin.castAdd r (Fin.rev j)))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    named proposition for the concrete Householder component Part B route.

    The long component package appears in several source-facing wrappers.  This
    predicate names exactly that surface: concrete `A Q₂`, `Bᵀ`, transformed
    RHS, and constraint-RHS perturbation identities, the conservative
    source-shaped norm bounds, and the exact perturbed GQR/minimizer package. -/
def Theorem20_10HouseholderComponentPartBRoute
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ) : Prop :=
  let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
  let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
  ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB : Fin p → Fin (p + q) → ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (Deltad : Fin p → ℝ),
    (∀ i j,
      gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
        matMulRect (r + q) (r + q) q
          (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
          (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
    (∀ i j,
      B i j + DeltaB i j =
        matMulRect (p + q) (p + q) p
          (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
          (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
    (∀ i,
      fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
        matMulVec (r + q)
          (matTranspose
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
          (fun k => b k + Deltab k) i) ∧
    (∀ i,
      rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
        rectMatMulVec B xhat i + Deltad i) ∧
    frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
    frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
    vecNorm2 Deltab ≤
      gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
    vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
    (∃ hpert : GeneralizedQRFactorization r p q
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j),
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
        rectMatMulVec hpert.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose hpert.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) -
              rectMatMulVec hpert.L21 yz.1 i) ∧
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i)
          (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ,
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) x))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    named proposition for the constructed rounded Householder returned-vector
    route.

    This is the existential body of
    `theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_component_unit_roundoff_smallnessThreshold_composed_conservative_gamma`
    with the returned vector pulled out as an explicit argument. -/
def Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ) : Prop :=
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let Rb : Fin (p + q) → Fin p → ℝ :=
    fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
  let S : Fin p → Fin p → ℝ :=
    matTranspose (fun i : Fin p => fun j : Fin p =>
      Rb (Fin.castAdd q i) j)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
  ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
  ∃ Deltab0 : Fin (r + q) → ℝ,
    (∀ i j,
      B i j + DeltaB0 i j =
        matMulRect (p + q) (p + q) p Qb Rb j i) ∧
    frobNormRect DeltaA0 ≤
      theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
    frobNormRect DeltaB0 ≤
      theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
    vecNorm2 Deltab0 ≤
      theorem20_10_householder_rhs_conservative_gamma fp r p q *
        vecNorm2 b ∧
    ∃ hpert : GeneralizedQRFactorization r p q
        (fun i j => A i j + DeltaA0 i j)
        (fun i j => B i j + DeltaB0 i j),
      hpert.Q = Qb ∧ hpert.S = S ∧
      (∀ j : Fin q,
        matMulVec (r + q) (matTranspose hpert.U)
            (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
          beta j) ∧
      xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
      let gammaA : ℝ :=
        theorem20_10_householder_composed_partA_gammaA fp r p q
      let gammaB : ℝ :=
        theorem20_10_householder_composed_partA_gammaB fp r p q
      ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      ∃ Deltab : Fin (r + q) → ℝ,
      ∃ Deltad : Fin p → ℝ,
        Deltad = (0 : Fin p → ℝ) ∧
        frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
        frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
        vecNorm2 Deltab ≤
          gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
        vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) xhat ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)

end NumStability
