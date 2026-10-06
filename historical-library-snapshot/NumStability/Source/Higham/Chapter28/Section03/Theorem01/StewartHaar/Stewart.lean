import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.RandomSVD.Basic
import NumStability.Analysis.TestMatrices.RandomSVD.Stewart

/-!
# Chapter28 Section03 Theorem01 StewartHaar Stewart

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Stewart` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

/-- Orthogonal left and right factors transport the right Gram matrix of a
randsvd matrix to the diagonal singular-value Gram matrix. -/
theorem randsvdMatrix_transpose_mul_self
    {m n : ℕ} (U : RSqMat m) (V : RSqMat n) (sigma : ℕ → ℝ)
    (hU : IsOrthogonal m U) :
    (randsvdMatrix U sigma V).transpose * randsvdMatrix U sigma V =
      V * ((rectangularDiagonal (m := m) (n := n) sigma).transpose *
        rectangularDiagonal (m := m) (n := n) sigma) * V.transpose := by
  let S := rectangularDiagonal (m := m) (n := n) sigma
  have hUeq : U.transpose * U = (1 : RSqMat m) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hU.left_inv i j
  change (U * S * V.transpose).transpose * (U * S * V.transpose) =
    V * (S.transpose * S) * V.transpose
  calc
    (U * S * V.transpose).transpose * (U * S * V.transpose) =
        V * (S.transpose * (U.transpose * U) * S) * V.transpose := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    _ = V * (S.transpose * S) * V.transpose := by
      rw [hUeq, Matrix.mul_one]

/-- The squared singular-value schedule, including the zero padding forced by
rectangular dimensions. -/
noncomputable def randsvdSingularValueSq {m n : ℕ}
    (sigma : ℕ → ℝ) (k : Fin n) : ℝ :=
  if k.val < m then sigma k.val ^ 2 else 0

/-- The Gram matrix of the rectangular diagonal has exactly the scheduled
squared singular values on its diagonal. -/
theorem rectangularDiagonal_gram_apply {m n : ℕ}
    (sigma : ℕ → ℝ) (i j : Fin n) :
    ((rectangularDiagonal (m := m) (n := n) sigma).transpose *
      rectangularDiagonal (m := m) (n := n) sigma) i j =
      if i = j then randsvdSingularValueSq (m := m) sigma i else 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rectangularDiagonal,
    randsvdSingularValueSq]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    by_cases hi : i.val < m
    · let ii : Fin m := ⟨i.val, hi⟩
      have hidx : ∀ x : Fin m, x.val = i.val ↔ x = ii := by
        intro x
        exact ⟨fun h => Fin.ext h, congrArg Fin.val⟩
      simp_rw [hidx]
      simp [ii, hi, pow_two]
    · have hnone : ∀ x : Fin m, x.val ≠ i.val := by
        intro x hx
        omega
      simp_rw [if_neg (hnone _)]
      simp [hi]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x.val = i.val
    · have hxj : x.val ≠ j.val := by omega
      change
        (if x.val = i.val then sigma x.val else 0) *
            (if x.val = j.val then sigma x.val else 0) = 0
      rw [if_pos hxi, if_neg hxj, mul_zero]
    · change
        (if x.val = i.val then sigma x.val else 0) *
            (if x.val = j.val then sigma x.val else 0) = 0
      rw [if_neg hxi, zero_mul]

/-- The columns of the right orthogonal factor are actual Gram eigenvectors
with the scheduled squared singular values. -/
theorem randsvdMatrix_rightGram_column_eigenpair {m n : ℕ}
    (U : RSqMat m) (V : RSqMat n) (sigma : ℕ → ℝ)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) (k : Fin n) :
    Matrix.mulVec
        ((randsvdMatrix U sigma V).transpose * randsvdMatrix U sigma V)
        (fun i ↦ V i k) =
      randsvdSingularValueSq (m := m) sigma k • (fun i ↦ V i k) := by
  let D : RSqMat n :=
    (rectangularDiagonal (m := m) (n := n) sigma).transpose *
      rectangularDiagonal (m := m) (n := n) sigma
  have hVtV : V.transpose * V = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hV.left_inv i j
  have hmatrix :
      ((randsvdMatrix U sigma V).transpose * randsvdMatrix U sigma V) * V =
        V * D := by
    rw [randsvdMatrix_transpose_mul_self U V sigma hU]
    calc
      (V * D * V.transpose) * V = V * D * (V.transpose * V) := by
        noncomm_ring
      _ = V * D := by rw [hVtV, Matrix.mul_one]
  funext i
  have hentry := congrFun (congrFun hmatrix i) k
  change
    (((randsvdMatrix U sigma V).transpose * randsvdMatrix U sigma V) * V) i k =
      randsvdSingularValueSq (m := m) sigma k * V i k
  rw [hentry]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single k]
  · dsimp [D]
    rw [rectangularDiagonal_gram_apply]
    simp [mul_comm]
  · intro j _ hj
    dsimp [D]
    rw [rectangularDiagonal_gram_apply]
    simp [hj]
  · simp

/-- Higham's prescribed-singular-value claim in an explicit finite spectral
form: the right Gram matrix has an orthonormal eigenbasis whose eigenvalues
are precisely the scheduled squared singular values (with rectangular zero
padding). -/
theorem randsvdMatrix_rightSingularVectors_orthonormal {m n : ℕ}
    (U : RSqMat m) (V : RSqMat n) (sigma : ℕ → ℝ)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    (∀ k : Fin n,
      Matrix.mulVec
          ((randsvdMatrix U sigma V).transpose * randsvdMatrix U sigma V)
          (fun i ↦ V i k) =
        randsvdSingularValueSq (m := m) sigma k • (fun i ↦ V i k)) ∧
      (∀ i j : Fin n,
        dotProduct (fun k ↦ V k i) (fun k ↦ V k j) = if i = j then 1 else 0) := by
  refine ⟨fun k => randsvdMatrix_rightGram_column_eigenpair U V sigma hU hV k, ?_⟩
  exact hV.col_orthonormal

/-- Higham, p. 518: the symmetric adaptation of `randsvd`,
`A = Q Λ Qᵀ`, with prescribed real eigenvalues on the diagonal. -/
noncomputable def symmetricRandsvdMatrix {n : ℕ}
    (Q : RSqMat n) (lambda : ℕ → ℝ) : RSqMat n :=
  Q * rectangularDiagonal (m := n) (n := n) lambda * Q.transpose

theorem rectangularDiagonal_square_transpose {n : ℕ} (lambda : ℕ → ℝ) :
    (rectangularDiagonal (m := n) (n := n) lambda).transpose =
      rectangularDiagonal (m := n) (n := n) lambda := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [rectangularDiagonal, Matrix.transpose_apply]
  · have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    simp [rectangularDiagonal, Matrix.transpose_apply, hval, hval.symm]

/-- The symmetric `randsvd` construction is symmetric for every factor `Q`;
orthogonality is needed only for the spectral conclusion. -/
theorem symmetricRandsvdMatrix_transpose {n : ℕ}
    (Q : RSqMat n) (lambda : ℕ → ℝ) :
    (symmetricRandsvdMatrix Q lambda).transpose =
      symmetricRandsvdMatrix Q lambda := by
  simp only [symmetricRandsvdMatrix, Matrix.transpose_mul,
    Matrix.transpose_transpose, rectangularDiagonal_square_transpose]
  noncomm_ring

/-- Every column of the orthogonal factor is an eigenvector with its
prescribed diagonal eigenvalue.  Thus the construction on p. 518 preserves
the entire prescribed eigenvalue list without appealing to a spectral
multiset transfer. -/
theorem symmetricRandsvdMatrix_column_eigenpair {n : ℕ}
    (Q : RSqMat n) (lambda : ℕ → ℝ) (hQ : IsOrthogonal n Q)
    (k : Fin n) :
    Matrix.mulVec (symmetricRandsvdMatrix Q lambda) (fun i ↦ Q i k) =
      lambda k.val • (fun i ↦ Q i k) := by
  let D : RSqMat n := rectangularDiagonal (m := n) (n := n) lambda
  have hQtQ : Q.transpose * Q = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hQ.left_inv i j
  have hmatrix : symmetricRandsvdMatrix Q lambda * Q = Q * D := by
    change (Q * D * Q.transpose) * Q = Q * D
    calc
      (Q * D * Q.transpose) * Q = Q * D * (Q.transpose * Q) := by
        noncomm_ring
      _ = Q * D := by rw [hQtQ, Matrix.mul_one]
  funext i
  have hentry := congrFun (congrFun hmatrix i) k
  have hleft :
      Matrix.mulVec (symmetricRandsvdMatrix Q lambda) (fun j ↦ Q j k) i =
        (symmetricRandsvdMatrix Q lambda * Q) i k := by
    rfl
  rw [hleft, hentry]
  have hk : ∀ x : Fin n, x.val = k.val ↔ x = k := by
    intro x
    exact ⟨Fin.ext, congrArg Fin.val⟩
  simp_rw [D, Matrix.mul_apply, rectangularDiagonal, hk]
  simp
  ring

/-- The two columns that span the correction when both `randsvd` factors are
single Householder matrices. -/
noncomputable def singleHouseholderRandsvdCorrectionLeft {m n : ℕ}
    (S : RMat m n) (u : Fin m → ℝ) (v : Fin n → ℝ) : RMat m 2 :=
  fun i r ↦ if r.val = 0 then u i else ∑ k : Fin n, S i k * v k

/-- The paired two rows in the exact rank-two correction factorization. -/
noncomputable def singleHouseholderRandsvdCorrectionRight {m n : ℕ}
    (S : RMat m n) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (beta gamma : ℝ) : RMat 2 n :=
  fun r j ↦
    if r.val = 0 then
      -beta * (∑ k : Fin m, u k * S k j) +
        beta * gamma *
          (∑ p : Fin n, (∑ k : Fin m, u k * S k p) * v p) * v j
    else -gamma * v j

/-- Rows in the inactive prefix agree exactly with the identity, making the
source's block-diagonal embedding visible. -/
theorem stewartEmbeddedHouseholder_prefix_row
    {n : ℕ} (i a b : Fin n) (x : Fin (n - i.val) → ℝ)
    (hai : a.val < i.val) :
    stewartEmbeddedHouseholder i x a b = idMatrix n a b := by
  simp [stewartEmbeddedHouseholder, householder,
    stewartEmbeddedHouseholderVector_of_lt i a x hai]

/-- Independent Stewart inputs for the left and right orthogonal factors. -/
abbrev StewartRandsvdInputs (m n : ℕ) :=
  StewartGaussianInputs m × StewartGaussianInputs n

/-- The product Gaussian law driving the two independent randsvd factors. -/
noncomputable def stewartRandsvdInputMeasure (m n : ℕ) :
    Measure (StewartRandsvdInputs m n) :=
  (stewartGaussianInputMeasure m).prod (stewartGaussianInputMeasure n)

theorem stewartRandsvdInputMeasure_univ (m n : ℕ) :
    stewartRandsvdInputMeasure m n Set.univ = 1 := by
  unfold stewartRandsvdInputMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod,
    stewartGaussianInputMeasure_univ, stewartGaussianInputMeasure_univ]
  norm_num

/-- A genuine randsvd sample path using two independent Stewart producers. -/
noncomputable def stewartRandsvdMatrix {m n : ℕ} (sigma : ℕ → ℝ)
    (z : StewartRandsvdInputs m n) : RMat m n :=
  randsvdMatrix (stewartOrthogonalMatrix z.1) sigma
    (stewartOrthogonalMatrix z.2)

/-- The right Gram matrix of the paired producer is orthogonally similar to
the squared rectangular diagonal, on every Gaussian input sample. -/
theorem stewartRandsvdMatrix_transpose_mul_self
    {m n : ℕ} (sigma : ℕ → ℝ) (z : StewartRandsvdInputs m n) :
    (stewartRandsvdMatrix sigma z).transpose *
        stewartRandsvdMatrix sigma z =
      stewartOrthogonalMatrix z.2 *
        ((rectangularDiagonal (m := m) (n := n) sigma).transpose *
          rectangularDiagonal (m := m) (n := n) sigma) *
        (stewartOrthogonalMatrix z.2).transpose := by
  exact randsvdMatrix_transpose_mul_self _ _ _
    (stewartOrthogonalMatrix_orthogonal z.1)

end NumStability
