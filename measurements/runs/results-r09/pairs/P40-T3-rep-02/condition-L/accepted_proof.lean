import HighamBench.P40Definitions

namespace HighamBench

private lemma p40FrobeniusSq_eq_trace {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    p40FrobeniusSq M = Matrix.trace (M.transpose * M) := by
  classical
  simp only [p40FrobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma p40FrobeniusSq_orthogonal_conj {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    p40FrobeniusSq (Q * M * Q.transpose) = p40FrobeniusSq M := by
  classical
  rw [p40FrobeniusSq_eq_trace, p40FrobeniusSq_eq_trace]
  have hprod :
      (Q * M * Q.transpose).transpose * (Q * M * Q.transpose) =
        Q * (M.transpose * M) * Q.transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Q * (M.transpose * Q.transpose) * (Q * M * Q.transpose) =
          Q * M.transpose * (Q.transpose * Q) * M * Q.transpose := by
            noncomm_ring
      _ = Q * (M.transpose * M) * Q.transpose := by
            rw [hQtQ]
            simp [Matrix.mul_assoc]
  rw [hprod, Matrix.trace_mul_cycle]
  simp [Matrix.mul_assoc, hQtQ]

private lemma p40_diagonal_positive_part_best {n : ℕ}
    (lambda : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hCdiag : ∀ i, 0 ≤ C i i) :
    p40FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - C) := by
  classical
  unfold p40FrobeniusSq
  calc
    ∑ i, ∑ j,
        ((Matrix.diagonal lambda - Matrix.diagonal (fun k => max (lambda k) 0)) i j) ^ 2 =
        ∑ i, (lambda i - max (lambda i) 0) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            have hij : i ≠ j := Ne.symm hji
            simp [Matrix.diagonal_apply, hij]
          · simp
    _ ≤ ∑ i, (lambda i - C i i) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          by_cases h : 0 ≤ lambda i
          · rw [max_eq_left h]
            nlinarith [sq_nonneg (lambda i - C i i)]
          · rw [max_eq_right (le_of_not_ge h)]
            nlinarith [hCdiag i]
    _ ≤ ∑ i, ∑ j, ((Matrix.diagonal lambda - C) i j) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          calc
            (lambda i - C i i) ^ 2 =
                ((Matrix.diagonal lambda - C) i i) ^ 2 := by simp
            _ ≤ ∑ j, ((Matrix.diagonal lambda - C) i j) ^ 2 := by
              exact Finset.single_le_sum (fun j _ => sq_nonneg ((Matrix.diagonal lambda - C) i j))
                (Finset.mem_univ i)

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
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let Dp : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let P : Matrix (Fin n) (Fin n) ℝ := Q * Dp * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * P * Sinv
  have hDp : Dp.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right _ _
  have hP : P.PosSemidef := by
    have h := hDp.mul_mul_conjTranspose_same Q
    simpa [P, Matrix.conjTranspose] using h
  have hX : X.PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same Sinv
    simpa [X, Matrix.conjTranspose, hSinvSymm] using h
  have hXdef : X = p40WeightedPsdProjection Sinv Q lambda := by
    rfl
  subst X
  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let Y : Matrix (Fin n) (Fin n) ℝ := S * Z * S
    let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * Y * Q
    have hY : Y.PosSemidef := by
      have h := hZ.mul_mul_conjTranspose_same S
      simpa [Y, Matrix.conjTranspose, hSsymm] using h
    have hC : C.PosSemidef := by
      have h := hY.conjTranspose_mul_mul_same Q
      simpa [C, Matrix.conjTranspose] using h
    have hAX :
        S * (A - p40WeightedPsdProjection Sinv Q lambda) * S =
          Q * (D - Dp) * Q.transpose := by
      change S * (A - Sinv * P * Sinv) * S = Q * (D - Dp) * Q.transpose
      rw [Matrix.mul_sub, Matrix.sub_mul, hSpectral]
      have hcancel : S * (Sinv * P * Sinv) * S = P := by
        calc
          S * (Sinv * P * Sinv) * S = (S * Sinv) * P * (Sinv * S) := by
            noncomm_ring
          _ = P := by rw [hSInv, hInvS]; simp
      rw [hcancel]
      simp only [P]
      noncomm_ring
    have hAZ : S * (A - Z) * S = Q * (D - C) * Q.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hSpectral]
      have hYC : Q * C * Q.transpose = Y := by
        calc
          Q * C * Q.transpose = (Q * Q.transpose) * Y * (Q * Q.transpose) := by
            simp only [C]
            noncomm_ring
          _ = Y := by rw [hQQt]; simp
      rw [show S * Z * S = Y from rfl, ← hYC]
      change Q * D * Q.transpose - Q * C * Q.transpose = Q * (D - C) * Q.transpose
      noncomm_ring
    rw [p40WeightedFrobeniusSq, p40WeightedFrobeniusSq, hAX, hAZ,
      p40FrobeniusSq_orthogonal_conj Q (D - Dp) hQtQ,
      p40FrobeniusSq_orthogonal_conj Q (D - C) hQtQ]
    exact p40_diagonal_positive_part_best lambda C (fun i => hC.diag_nonneg)
  · intro i
    have hdiffDiag : 0 ≤
        (p40WeightedPsdProjection Sinv Q lambda - A) i i := by
      have hDdiff : (Dp - D).PosSemidef := by
        rw [show Dp - D = Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) by
          ext i j
          by_cases hij : i = j <;> simp [D, Dp, Matrix.diagonal_apply, hij]]
        apply Matrix.PosSemidef.diagonal
        intro j
        exact sub_nonneg.mpr (le_max_left _ _)
      have hPdiff : (P - Q * D * Q.transpose).PosSemidef := by
        rw [show P - Q * D * Q.transpose = Q * (Dp - D) * Q.transpose by
          simp [P, Matrix.mul_sub, Matrix.sub_mul]]
        have h := hDdiff.mul_mul_conjTranspose_same Q
        simpa [Matrix.conjTranspose] using h
      have hdiff :
          (p40WeightedPsdProjection Sinv Q lambda - A).PosSemidef := by
        have hcong := hPdiff.mul_mul_conjTranspose_same Sinv
        have hAform : A = Sinv * (Q * D * Q.transpose) * Sinv := by
          calc
            A = (Sinv * S) * A * (S * Sinv) := by simp [hInvS, hSInv]
            _ = Sinv * (S * A * S) * Sinv := by
              simp [Matrix.mul_assoc]
            _ = Sinv * (Q * D * Q.transpose) * Sinv := by
              rw [hSpectral]
        simpa [p40WeightedPsdProjection, p40SpectralPositivePart, P, Dp,
          Matrix.conjTranspose, hSinvSymm, hAform, Matrix.mul_sub, Matrix.sub_mul] using hcong
      exact hdiff.diag_nonneg
    simpa [Matrix.sub_apply] using hdiffDiag

end HighamBench
