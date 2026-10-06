import HighamBench.P40Definitions

namespace HighamBench

private lemma p40FrobeniusSq_eq_trace {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    p40FrobeniusSq M = Matrix.trace (M.transpose * M) := by
  classical
  simp only [p40FrobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp [pow_two]

private lemma p40FrobeniusSq_orthogonal_conj {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    p40FrobeniusSq (Q * M * Q.transpose) = p40FrobeniusSq M := by
  rw [p40FrobeniusSq_eq_trace, p40FrobeniusSq_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hmul :
      (Q * (M.transpose * Q.transpose)) * (Q * M * Q.transpose) =
        Q * (M.transpose * (Q.transpose * Q) * M) * Q.transpose := by
    noncomm_ring
  rw [hmul, hQtQ]
  simp only [Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.trace_mul_cycle]
  rw [hQtQ]
  simp

private lemma p40_diagonal_positive_part_min {n : ℕ}
    (lambda : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hCdiag : ∀ i, 0 ≤ C i i) :
    p40FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i ↦ max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - C) := by
  classical
  unfold p40FrobeniusSq
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq]
    by_cases hlambda : 0 ≤ lambda i
    · rw [max_eq_left hlambda]
      nlinarith [sq_nonneg (lambda i - C i i)]
    · rw [max_eq_right (le_of_not_ge hlambda)]
      have hci := hCdiag i
      nlinarith
  · simp [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sq_nonneg]

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
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let Dp : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i ↦ max (lambda i) 0)
  let P : Matrix (Fin n) (Fin n) ℝ := Q * Dp * Q.transpose
  have hDp : Dp.PosSemidef := by
    dsimp [Dp]
    exact Matrix.PosSemidef.diagonal (fun i ↦ le_max_right (lambda i) 0)
  have hP : P.PosSemidef := by
    dsimp [P]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hDp.mul_mul_conjTranspose_same Q
  have hXeq :
      p40WeightedPsdProjection Sinv Q lambda = Sinv * P * Sinv := by
    rfl
  have hX : (p40WeightedPsdProjection Sinv Q lambda).PosSemidef := by
    rw [hXeq]
    have h := hP.mul_mul_conjTranspose_same Sinv
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using h

  have hDdiff :
      Dp - D = Matrix.diagonal (fun i ↦ max (lambda i) 0 - lambda i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Dp]
    · simp [D, Dp, Matrix.diagonal_apply_ne _ hij]
  have hDdiffPos :
      (Dp - D).PosSemidef := by
    rw [hDdiff]
    exact Matrix.PosSemidef.diagonal
      (fun i ↦ sub_nonneg.mpr (le_max_left (lambda i) 0))
  have hPdiff : (P - Q * D * Q.transpose).PosSemidef := by
    have h := hDdiffPos.mul_mul_conjTranspose_same Q
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (show P - Q * D * Q.transpose = Q * (Dp - D) * Q.transpose by
        dsimp [P]
        noncomm_ring) ▸ h
  have hAback : Sinv * (S * A * S) * Sinv = A := by
    calc
      Sinv * (S * A * S) * Sinv = (Sinv * S) * A * (S * Sinv) := by
        noncomm_ring
      _ = A := by rw [hInvS, hSInv]; simp
  have hXsubAeq :
      p40WeightedPsdProjection Sinv Q lambda - A =
        Sinv * (P - Q * D * Q.transpose) * Sinv := by
    rw [hXeq, ← hAback, hSpectral]
    change Sinv * P * Sinv - Sinv * (Q * D * Q.transpose) * Sinv = _
    noncomm_ring
  have hXsubA :
      (p40WeightedPsdProjection Sinv Q lambda - A).PosSemidef := by
    rw [hXsubAeq]
    have h := hPdiff.mul_mul_conjTranspose_same Sinv
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using h

  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let Y : Matrix (Fin n) (Fin n) ℝ := S * Z * S
    have hY : Y.PosSemidef := by
      have h := hZ.mul_mul_conjTranspose_same S
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSsymm] using h
    let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * Y * Q
    have hC : C.PosSemidef := by
      dsimp [C]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hY.conjTranspose_mul_mul_same Q
    have hCdiag : ∀ i, 0 ≤ C i i := fun i ↦ hC.diag_nonneg
    have hSXS :
        S * p40WeightedPsdProjection Sinv Q lambda * S = P := by
      rw [hXeq]
      calc
        S * (Sinv * P * Sinv) * S = (S * Sinv) * P * (Sinv * S) := by
          noncomm_ring
        _ = P := by rw [hSInv, hInvS]; simp
    have hleft :
        S * (A - p40WeightedPsdProjection Sinv Q lambda) * S =
          Q * (D - Dp) * Q.transpose := by
      calc
        S * (A - p40WeightedPsdProjection Sinv Q lambda) * S =
            S * A * S - S * p40WeightedPsdProjection Sinv Q lambda * S := by
          noncomm_ring
        _ = Q * D * Q.transpose - P := by rw [hSpectral, hSXS]
        _ = Q * (D - Dp) * Q.transpose := by
          dsimp [P]
          noncomm_ring
    have hright :
        S * (A - Z) * S = Q * (D - C) * Q.transpose := by
      calc
        S * (A - Z) * S = S * A * S - Y := by
          dsimp [Y]
          noncomm_ring
        _ = Q * D * Q.transpose - Y := by rw [hSpectral]
        _ = Q * D * Q.transpose - (Q * Q.transpose) * Y * (Q * Q.transpose) := by
          rw [hQQt]
          simp
        _ = Q * (D - C) * Q.transpose := by
          dsimp [C]
          noncomm_ring
    unfold p40WeightedFrobeniusSq
    rw [hleft, hright,
      p40FrobeniusSq_orthogonal_conj Q (D - Dp) hQtQ,
      p40FrobeniusSq_orthogonal_conj Q (D - C) hQtQ]
    exact p40_diagonal_positive_part_min lambda C hCdiag
  · intro i
    have hii := hXsubA.diag_nonneg (i := i)
    simpa [Matrix.sub_apply] using hii

end HighamBench
