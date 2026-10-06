import HighamBench.P40Definitions
import NumStability.Analysis.MatrixAlgebra

namespace HighamBench

open scoped BigOperators

private lemma p40FrobeniusSq_orthogonal_conjugation
    {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) :
    p40FrobeniusSq (Q.transpose * M * Q) = p40FrobeniusSq M := by
  have hQ : NumStability.IsOrthogonal n Q := by
    constructor
    · intro i j
      have h := congrFun (congrFun hQtQ i) j
      simpa [Matrix.mul_apply, NumStability.matTranspose] using h
    · intro i j
      have h := congrFun (congrFun hQQt i) j
      simpa [Matrix.mul_apply, NumStability.matTranspose] using h
  rw [p40FrobeniusSq, p40FrobeniusSq]
  change NumStability.frobNormSq
      (NumStability.matMul n
        (NumStability.matMul n (NumStability.matTranspose Q) M) Q) =
    NumStability.frobNormSq M
  rw [NumStability.frobNormSq_orthogonal_right _ _ hQ,
    NumStability.frobNormSq_orthogonal_left _ _ hQ.transpose]

private lemma p40FrobeniusSq_diagonal_positive_part_min
    {n : ℕ} (lambda : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hRdiag : ∀ i, 0 ≤ R i i) :
    p40FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - R) := by
  unfold p40FrobeniusSq
  calc
    (∑ i, ∑ j,
        ((Matrix.diagonal lambda -
          Matrix.diagonal (fun i => max (lambda i) 0)) i j) ^ 2) =
        ∑ i, (lambda i - max (lambda i) 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp [Matrix.diagonal_apply]
      · intro j _ hji
        simp [Matrix.diagonal_apply, hji, Ne.symm hji]
      · simp
    _ ≤ ∑ i, (lambda i - R i i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : lambda i ≤ 0
      · rw [max_eq_right hi]
        nlinarith [hRdiag i]
      · rw [max_eq_left (le_of_not_ge hi)]
        nlinarith [sq_nonneg (lambda i - R i i)]
    _ ≤ ∑ i, ∑ j, ((Matrix.diagonal lambda - R) i j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
          sq_nonneg ((Matrix.diagonal lambda - R) i j))
        (Finset.mem_univ i)
      simpa using hi

/-- P40-T3: the weighted positive-semidefinite projection formula of Theorem 3.2. -/
theorem p40_t3_weighted_psd_projection
    (n : ℕ)
    (A S Sinv Q : Matrix (Fin n) (Fin n) ℝ) (lambda : Fin n → ℝ)
    (hSsymm : S.transpose = S)
    (hSinvSymm : Sinv.transpose = Sinv)
    (hSInv : S * Sinv = 1)
    (hInvS : Sinv * S = 1)
    (hQtQ : Q.transpose * Q = 1)
    (hQQt : Q * Q.transpose = 1)
    (hSpectral : S * A * S = Q * Matrix.diagonal lambda * Q.transpose) :
    let X := p40WeightedPsdProjection Sinv Q lambda
    X.PosSemidef ∧
      (∀ Z : Matrix (Fin n) (Fin n) ℝ,
        Z.PosSemidef →
          p40WeightedFrobeniusSq S (A - X) ≤
            p40WeightedFrobeniusSq S (A - Z)) ∧
      ∀ i, A i i ≤ X i i := by
  -- PROOF_START P40-T3-H001
  dsimp only
  let Dplus : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let P : Matrix (Fin n) (Fin n) ℝ := Q * Dplus * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * P * Sinv
  have hDplus : Dplus.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right _ _
  have hP : P.PosSemidef := by
    have h := hDplus.mul_mul_conjTranspose_same Q
    simpa [P, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hX : X.PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same Sinv
    simpa [X, Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using h
  have hproj : p40WeightedPsdProjection Sinv Q lambda = X := by
    rfl
  rw [hproj]
  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    have hSZ : (S * Z * S).PosSemidef := by
      have h := hZ.mul_mul_conjTranspose_same S
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hSsymm] using h
    have hR : (Q.transpose * (S * Z * S) * Q).PosSemidef := by
      have h := hSZ.mul_mul_conjTranspose_same Q.transpose
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
    have hSX : S * X * S = P := by
      calc
        S * X * S = (S * Sinv) * P * (Sinv * S) := by
          simp only [X]
          noncomm_ring
        _ = P := by rw [hSInv, hInvS]; simp
    have hAX :
        S * (A - X) * S =
          Q * (Matrix.diagonal lambda - Dplus) * Q.transpose := by
      calc
        S * (A - X) * S = S * A * S - S * X * S := by
          noncomm_ring
        _ = Q * Matrix.diagonal lambda * Q.transpose - P := by
          rw [hSpectral, hSX]
        _ = Q * (Matrix.diagonal lambda - Dplus) * Q.transpose := by
          simp only [P]
          noncomm_ring
    have hAZ :
        Q.transpose * (S * (A - Z) * S) * Q =
          Matrix.diagonal lambda - Q.transpose * (S * Z * S) * Q := by
      calc
        Q.transpose * (S * (A - Z) * S) * Q =
            Q.transpose * (S * A * S - S * Z * S) * Q := by
              congr 2
              noncomm_ring
        _ = Q.transpose *
            (Q * Matrix.diagonal lambda * Q.transpose - S * Z * S) * Q := by
              rw [hSpectral]
        _ = (Q.transpose * Q) * Matrix.diagonal lambda *
              (Q.transpose * Q) - Q.transpose * (S * Z * S) * Q := by
              noncomm_ring
        _ = Matrix.diagonal lambda - Q.transpose * (S * Z * S) * Q := by
              rw [hQtQ]
              simp
    have hObjX :
        p40WeightedFrobeniusSq S (A - X) =
          p40FrobeniusSq (Matrix.diagonal lambda - Dplus) := by
      rw [p40WeightedFrobeniusSq, hAX]
      have h := p40FrobeniusSq_orthogonal_conjugation
        Q.transpose (Matrix.diagonal lambda - Dplus) hQQt hQtQ
      simpa using h
    have hObjZ :
        p40WeightedFrobeniusSq S (A - Z) =
          p40FrobeniusSq
            (Matrix.diagonal lambda - Q.transpose * (S * Z * S) * Q) := by
      rw [p40WeightedFrobeniusSq]
      calc
        p40FrobeniusSq (S * (A - Z) * S) =
            p40FrobeniusSq (Q.transpose * (S * (A - Z) * S) * Q) := by
              symm
              exact p40FrobeniusSq_orthogonal_conjugation Q _ hQtQ hQQt
        _ = p40FrobeniusSq
            (Matrix.diagonal lambda - Q.transpose * (S * Z * S) * Q) := by
              rw [hAZ]
    rw [hObjX, hObjZ]
    exact p40FrobeniusSq_diagonal_positive_part_min lambda
      (Q.transpose * (S * Z * S) * Q) (fun i => hR.diag_nonneg)
  · have hAeq : A = Sinv * (S * A * S) * Sinv := by
      calc
        A = (Sinv * S) * A * (S * Sinv) := by
          rw [hInvS, hSInv]
          simp
        _ = Sinv * (S * A * S) * Sinv := by
          noncomm_ring
    have hDiagSub :
        Dplus - Matrix.diagonal lambda =
          Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Dplus]
      · simp [Dplus, hij]
    have hPSub :
        P - S * A * S =
          Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
            Q.transpose := by
      calc
        P - S * A * S =
            Q * Dplus * Q.transpose -
              Q * Matrix.diagonal lambda * Q.transpose := by
                rw [hSpectral]
        _ = Q * (Dplus - Matrix.diagonal lambda) * Q.transpose := by
              noncomm_ring
        _ = Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
              Q.transpose := by rw [hDiagSub]
    have hDiff :
        X - A = Sinv *
          (Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
            Q.transpose) * Sinv := by
      calc
        X - A = X - Sinv * (S * A * S) * Sinv :=
          congrArg (fun M => X - M) hAeq
        _ = Sinv * P * Sinv - Sinv * (S * A * S) * Sinv := by rfl
        _ = Sinv * (P - S * A * S) * Sinv := by
          noncomm_ring
        _ = Sinv *
            (Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
              Q.transpose) * Sinv := by rw [hPSub]
    have hDiagDiff :
        (Matrix.diagonal (fun i => max (lambda i) 0 - lambda i)).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      exact sub_nonneg.mpr (le_max_left _ _)
    have hInnerDiff :
        (Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
          Q.transpose).PosSemidef := by
      have h := hDiagDiff.mul_mul_conjTranspose_same Q
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
    have hDiffPsd : (X - A).PosSemidef := by
      rw [hDiff]
      have h := hInnerDiff.mul_mul_conjTranspose_same Sinv
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using h
    intro i
    have hii := hDiffPsd.diag_nonneg (i := i)
    change 0 ≤ X i i - A i i at hii
    linarith

end HighamBench
