import HighamBench.P40Definitions

namespace HighamBench

private lemma p40_frobeniusSq_eq_trace {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    p40FrobeniusSq M = Matrix.trace (M.transpose * M) := by
  classical
  simp only [p40FrobeniusSq, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  rw [Finset.sum_comm]

private lemma p40_frobeniusSq_orthogonal_conjugation {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQQt : Q * Q.transpose = 1) :
    p40FrobeniusSq (Q.transpose * M * Q) = p40FrobeniusSq M := by
  rw [p40_frobeniusSq_eq_trace, p40_frobeniusSq_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    Matrix.trace ((Q.transpose * (M.transpose * Q)) * (Q.transpose * M * Q)) =
        Matrix.trace (Q.transpose * (M.transpose * M) * Q) := by
          congr 1
          calc
            Q.transpose * (M.transpose * Q) * (Q.transpose * M * Q) =
                Q.transpose * M.transpose * (Q * Q.transpose) * M * Q := by
                  noncomm_ring
            _ = Q.transpose * (M.transpose * M) * Q := by
                  rw [hQQt]
                  noncomm_ring
    _ = Matrix.trace (Q * Q.transpose * (M.transpose * M)) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (M.transpose * M) := by rw [hQQt, Matrix.one_mul]

private lemma p40_scalar_positive_part_best (a y : ℝ) (hy : 0 ≤ y) :
    (a - max a 0) ^ 2 ≤ (a - y) ^ 2 := by
  by_cases ha : a ≤ 0
  · rw [max_eq_right ha]
    nlinarith [sq_nonneg (a - y)]
  · rw [max_eq_left (le_of_not_ge ha)]
    nlinarith [sq_nonneg (a - y)]

private lemma p40_diagonal_positive_part_best {n : ℕ}
    (lambda : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y.PosSemidef) :
    p40FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - Y) := by
  classical
  unfold p40FrobeniusSq
  simp only [Matrix.sub_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  have hii :
      (lambda i - max (lambda i) 0) ^ 2 ≤
        (Matrix.diagonal lambda i i - Y i i) ^ 2 := by
    simpa using p40_scalar_positive_part_best (lambda i) (Y i i) hY.diag_nonneg
  calc
    ∑ j, (Matrix.diagonal lambda i j -
          Matrix.diagonal (fun k => max (lambda k) 0) i j) ^ 2 =
        (lambda i - max (lambda i) 0) ^ 2 := by
          trans ∑ j, if i = j then (lambda i - max (lambda i) 0) ^ 2 else 0
          · apply Finset.sum_congr rfl
            intro j _
            by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
          · simp
    _ ≤ (Matrix.diagonal lambda i i - Y i i) ^ 2 := hii
    _ ≤ ∑ j, (Matrix.diagonal lambda i j - Y i j) ^ 2 := by
          exact Finset.single_le_sum (fun j _ => sq_nonneg
            (Matrix.diagonal lambda i j - Y i j)) (Finset.mem_univ i)

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
  classical
  dsimp only
  have hDpos :
      (Matrix.diagonal (fun i => max (lambda i) 0) :
        Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
    exact Matrix.PosSemidef.diagonal (fun i => le_max_right (lambda i) 0)
  have hPpos :
      (Q * Matrix.diagonal (fun i => max (lambda i) 0) * Q.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hDpos.mul_mul_conjTranspose_same Q
  have hXpos : (p40WeightedPsdProjection Sinv Q lambda).PosSemidef := by
    unfold p40WeightedPsdProjection p40SpectralPositivePart
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using
      hPpos.mul_mul_conjTranspose_same Sinv
  refine ⟨hXpos, ?_, ?_⟩
  · intro Z hZ
    have hSX :
        S * p40WeightedPsdProjection Sinv Q lambda * S =
          Q * Matrix.diagonal (fun i => max (lambda i) 0) * Q.transpose := by
      unfold p40WeightedPsdProjection p40SpectralPositivePart
      calc
        S * (Sinv * (Q * Matrix.diagonal (fun i => max (lambda i) 0) *
              Q.transpose) * Sinv) * S =
            (S * Sinv) * (Q * Matrix.diagonal (fun i => max (lambda i) 0) *
              Q.transpose) * (Sinv * S) := by noncomm_ring
        _ = Q * Matrix.diagonal (fun i => max (lambda i) 0) * Q.transpose := by
              rw [hSInv, hInvS]
              simp
    have hCandidateTransform :
        S * (A - p40WeightedPsdProjection Sinv Q lambda) * S =
          Q * (Matrix.diagonal lambda -
            Matrix.diagonal (fun i => max (lambda i) 0)) * Q.transpose := by
      calc
        S * (A - p40WeightedPsdProjection Sinv Q lambda) * S =
            S * A * S - S * p40WeightedPsdProjection Sinv Q lambda * S := by
              noncomm_ring
        _ = Q * Matrix.diagonal lambda * Q.transpose -
            Q * Matrix.diagonal (fun i => max (lambda i) 0) * Q.transpose := by
              rw [hSpectral, hSX]
        _ = Q * (Matrix.diagonal lambda -
            Matrix.diagonal (fun i => max (lambda i) 0)) * Q.transpose := by
              noncomm_ring
    have hSZS : (S * Z * S).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSsymm] using
        hZ.mul_mul_conjTranspose_same S
    have hY : (Q.transpose * (S * Z * S) * Q).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hSZS.conjTranspose_mul_mul_same Q
    have hZTransform :
        Q.transpose * (S * (A - Z) * S) * Q =
          Matrix.diagonal lambda - Q.transpose * (S * Z * S) * Q := by
      calc
        Q.transpose * (S * (A - Z) * S) * Q =
            Q.transpose * (S * A * S) * Q -
              Q.transpose * (S * Z * S) * Q := by noncomm_ring
        _ = Q.transpose * (Q * Matrix.diagonal lambda * Q.transpose) * Q -
              Q.transpose * (S * Z * S) * Q := by rw [hSpectral]
        _ = (Q.transpose * Q) * Matrix.diagonal lambda * (Q.transpose * Q) -
              Q.transpose * (S * Z * S) * Q := by congr 1 <;> noncomm_ring
        _ = Matrix.diagonal lambda - Q.transpose * (S * Z * S) * Q := by
              rw [hQtQ]
              simp
    calc
      p40WeightedFrobeniusSq S
          (A - p40WeightedPsdProjection Sinv Q lambda) =
          p40FrobeniusSq
            (Q * (Matrix.diagonal lambda -
              Matrix.diagonal (fun i => max (lambda i) 0)) * Q.transpose) := by
                rw [p40WeightedFrobeniusSq, hCandidateTransform]
      _ = p40FrobeniusSq
            (Matrix.diagonal lambda -
              Matrix.diagonal (fun i => max (lambda i) 0)) := by
                simpa only [Matrix.transpose_transpose] using
                  p40_frobeniusSq_orthogonal_conjugation Q.transpose
                    (Matrix.diagonal lambda -
                      Matrix.diagonal (fun i => max (lambda i) 0)) hQtQ
      _ ≤ p40FrobeniusSq
            (Matrix.diagonal lambda - Q.transpose * (S * Z * S) * Q) :=
                p40_diagonal_positive_part_best lambda
                  (Q.transpose * (S * Z * S) * Q) hY
      _ = p40FrobeniusSq (Q.transpose * (S * (A - Z) * S) * Q) := by
                rw [hZTransform]
      _ = p40FrobeniusSq (S * (A - Z) * S) :=
                p40_frobeniusSq_orthogonal_conjugation Q
                  (S * (A - Z) * S) hQQt
      _ = p40WeightedFrobeniusSq S (A - Z) := rfl
  · have hDdiff :
        (Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) :
          Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
      exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (le_max_left _ _))
    have hQdiff :
        (Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
          Q.transpose).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hDdiff.mul_mul_conjTranspose_same Q
    have hCongDiff :
        (Sinv * (Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
          Q.transpose) * Sinv).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using
        hQdiff.mul_mul_conjTranspose_same Sinv
    have hAreconstruct :
        A = Sinv * (Q * Matrix.diagonal lambda * Q.transpose) * Sinv := by
      calc
        A = (Sinv * S) * A * (S * Sinv) := by rw [hInvS, hSInv]; simp
        _ = Sinv * (S * A * S) * Sinv := by noncomm_ring
        _ = Sinv * (Q * Matrix.diagonal lambda * Q.transpose) * Sinv := by
              rw [hSpectral]
    have hdiagDiff :
        Matrix.diagonal (fun i => max (lambda i) 0) - Matrix.diagonal lambda =
          Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    have hProjectionDiff :
        p40WeightedPsdProjection Sinv Q lambda - A =
          Sinv * (Q * Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) *
            Q.transpose) * Sinv := by
      rw [hAreconstruct]
      unfold p40WeightedPsdProjection p40SpectralPositivePart
      calc
        Sinv * (Q * Matrix.diagonal (fun i => max (lambda i) 0) * Q.transpose) *
              Sinv - Sinv * (Q * Matrix.diagonal lambda * Q.transpose) * Sinv =
            Sinv * (Q * (Matrix.diagonal (fun i => max (lambda i) 0) -
              Matrix.diagonal lambda) * Q.transpose) * Sinv := by noncomm_ring
        _ = Sinv * (Q * Matrix.diagonal
              (fun i => max (lambda i) 0 - lambda i) * Q.transpose) * Sinv := by
                rw [hdiagDiff]
    have hProjectionDiffPos :
        (p40WeightedPsdProjection Sinv Q lambda - A).PosSemidef := by
      rw [hProjectionDiff]
      exact hCongDiff
    intro i
    exact sub_nonneg.mp hProjectionDiffPos.diag_nonneg

end HighamBench
