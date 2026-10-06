import HighamBench.P40Definitions
import NumStability.Analysis.MatrixAlgebra

namespace HighamBench

open scoped BigOperators

private lemma p40_sq_sub_max_le_sq_sub_of_nonneg (a c : ℝ) (hc : 0 ≤ c) :
    (a - max a 0) ^ 2 ≤ (a - c) ^ 2 := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha]
    nlinarith
  · rw [max_eq_left ha]
    nlinarith

private lemma p40_diagonal_positive_part_minimal
    {n : ℕ} (lambda : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) :
    p40FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - C) := by
  unfold p40FrobeniusSq
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa [Matrix.sub_apply] using
      p40_sq_sub_max_le_sq_sub_of_nonneg (lambda i) (C i i) hC.diag_nonneg
  · simp [Matrix.sub_apply, Matrix.diagonal, hij, sq_nonneg]

private lemma p40_frobeniusSq_orthogonal_left
    {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQ : NumStability.IsOrthogonal n Q) :
    p40FrobeniusSq (Q * M) = p40FrobeniusSq M := by
  simpa [p40FrobeniusSq, NumStability.frobNormSq,
    NumStability.matMul, Matrix.mul_apply] using
    (NumStability.frobNormSq_orthogonal_left Q M hQ)

private lemma p40_frobeniusSq_orthogonal_right
    {n : ℕ} (M Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : NumStability.IsOrthogonal n Q) :
    p40FrobeniusSq (M * Q) = p40FrobeniusSq M := by
  simpa [p40FrobeniusSq, NumStability.frobNormSq,
    NumStability.matMul, Matrix.mul_apply] using
    (NumStability.frobNormSq_orthogonal_right M Q hQ)

private lemma p40_spectral_positive_part_minimal
    {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (lambda : Fin n → ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1)
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Y.PosSemidef) :
    p40FrobeniusSq
        (Q * Matrix.diagonal lambda * Q.transpose -
          p40SpectralPositivePart Q lambda) ≤
      p40FrobeniusSq (Q * Matrix.diagonal lambda * Q.transpose - Y) := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let Dp : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * Y * Q
  have hQ : NumStability.IsOrthogonal n Q := by
    constructor
    · intro i j
      have h := congrFun (congrFun hQtQ i) j
      simpa [NumStability.matTranspose, Matrix.mul_apply] using h
    · intro i j
      have h := congrFun (congrFun hQQt i) j
      simpa [NumStability.matTranspose, Matrix.mul_apply] using h
  have hC : C.PosSemidef := by
    have hc := hY.conjTranspose_mul_mul_same Q
    simpa [C] using hc
  have hdiag :
      p40FrobeniusSq (D - Dp) ≤ p40FrobeniusSq (D - C) := by
    simpa [D, Dp] using p40_diagonal_positive_part_minimal lambda C hC
  have hleft :
      Q * Matrix.diagonal lambda * Q.transpose -
          p40SpectralPositivePart Q lambda = Q * (D - Dp) * Q.transpose := by
    simp only [p40SpectralPositivePart, D, Dp]
    noncomm_ring
  have hright :
      Q.transpose * (Q * Matrix.diagonal lambda * Q.transpose - Y) * Q =
        D - C := by
    calc
      Q.transpose * (Q * Matrix.diagonal lambda * Q.transpose - Y) * Q =
          (Q.transpose * Q) * Matrix.diagonal lambda * (Q.transpose * Q) -
            Q.transpose * Y * Q := by noncomm_ring
      _ = D - C := by simp [hQtQ, D, C]
  rw [hleft]
  calc
    p40FrobeniusSq (Q * (D - Dp) * Q.transpose) =
        p40FrobeniusSq ((D - Dp) * Q.transpose) :=
      by simpa [Matrix.mul_assoc] using
        p40_frobeniusSq_orthogonal_left Q ((D - Dp) * Q.transpose) hQ
    _ = p40FrobeniusSq (D - Dp) :=
      p40_frobeniusSq_orthogonal_right (D - Dp) Q.transpose hQ.transpose
    _ ≤ p40FrobeniusSq (D - C) := hdiag
    _ = p40FrobeniusSq
          (Q.transpose * (Q * Matrix.diagonal lambda * Q.transpose - Y) * Q) := by
      rw [hright]
    _ = p40FrobeniusSq
          (Q.transpose * (Q * Matrix.diagonal lambda * Q.transpose - Y)) :=
      p40_frobeniusSq_orthogonal_right
        (Q.transpose * (Q * Matrix.diagonal lambda * Q.transpose - Y)) Q hQ
    _ = p40FrobeniusSq (Q * Matrix.diagonal lambda * Q.transpose - Y) :=
      p40_frobeniusSq_orthogonal_left Q.transpose
        (Q * Matrix.diagonal lambda * Q.transpose - Y) hQ.transpose

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
  let B : Matrix (Fin n) (Fin n) ℝ := Q * D * Q.transpose
  let P : Matrix (Fin n) (Fin n) ℝ := p40SpectralPositivePart Q lambda
  let X : Matrix (Fin n) (Fin n) ℝ := p40WeightedPsdProjection Sinv Q lambda
  change X.PosSemidef ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
      p40WeightedFrobeniusSq S (A - X) ≤
        p40WeightedFrobeniusSq S (A - Z)) ∧
    ∀ i, A i i ≤ X i i
  have hDp : Dp.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right (lambda i) 0
  have hP : P.PosSemidef := by
    have hp := hDp.mul_mul_conjTranspose_same Q
    simpa [P, Dp, p40SpectralPositivePart] using hp
  have hX : X.PosSemidef := by
    have hx := hP.mul_mul_conjTranspose_same Sinv
    simpa [X, P, p40WeightedPsdProjection, hSinvSymm] using hx
  have hSX : S * X * S = P := by
    calc
      S * X * S = (S * Sinv) * P * (Sinv * S) := by
        simp only [X, P, p40WeightedPsdProjection]
        noncomm_ring
      _ = P := by rw [hSInv, hInvS]; simp
  have hobjective : ∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
      p40WeightedFrobeniusSq S (A - X) ≤
        p40WeightedFrobeniusSq S (A - Z) := by
    intro Z hZ
    let Y : Matrix (Fin n) (Fin n) ℝ := S * Z * S
    have hY : Y.PosSemidef := by
      have hy := hZ.mul_mul_conjTranspose_same S
      simpa [Y, hSsymm] using hy
    have hAX :
        S * (A - X) * S = Q * Matrix.diagonal lambda * Q.transpose - P := by
      calc
        S * (A - X) * S = S * A * S - S * X * S := by noncomm_ring
        _ = Q * Matrix.diagonal lambda * Q.transpose - P := by
          rw [hSpectral, hSX]
    have hAZ :
        S * (A - Z) * S = Q * Matrix.diagonal lambda * Q.transpose - Y := by
      calc
        S * (A - Z) * S = S * A * S - S * Z * S := by noncomm_ring
        _ = Q * Matrix.diagonal lambda * Q.transpose - Y := by
          rw [hSpectral]
    have hmin := p40_spectral_positive_part_minimal
      Q lambda hQtQ hQQt Y hY
    rw [p40WeightedFrobeniusSq, p40WeightedFrobeniusSq, hAX, hAZ]
    simpa [P] using hmin
  let Dn : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0 - lambda i)
  have hDn : Dn.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (le_max_left (lambda i) 0)
  have hDn_eq : Dn = Dp - D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Dn, Dp, D, Matrix.sub_apply]
    · simp [Dn, Dp, D, Matrix.sub_apply, Matrix.diagonal, hij]
  have hPB : (P - B).PosSemidef := by
    have hp := hDn.mul_mul_conjTranspose_same Q
    rw [hDn_eq] at hp
    have hp' : (Q * (Dp - D) * Q.transpose).PosSemidef := by
      simpa using hp
    have heq : Q * (Dp - D) * Q.transpose = P - B := by
      simp only [P, B, Dp, D, p40SpectralPositivePart]
      noncomm_ring
    rw [heq] at hp'
    exact hp'
  have hArep : A = Sinv * B * Sinv := by
    calc
      A = 1 * A * 1 := by simp
      _ = (Sinv * S) * A * (S * Sinv) := by rw [hInvS, hSInv]
      _ = Sinv * (S * A * S) * Sinv := by noncomm_ring
      _ = Sinv * B * Sinv := by rw [hSpectral]
  have hXAeq : X - A = Sinv * (P - B) * Sinv := by
    rw [hArep]
    simp only [X, P, p40WeightedPsdProjection]
    noncomm_ring
  have hXA : (X - A).PosSemidef := by
    have hcong := hPB.mul_mul_conjTranspose_same Sinv
    have hcong' : (Sinv * (P - B) * Sinv).PosSemidef := by
      simpa [hSinvSymm] using hcong
    rw [hXAeq]
    exact hcong'
  refine ⟨hX, hobjective, ?_⟩
  intro i
  have hi := hXA.diag_nonneg (i := i)
  simpa [Matrix.sub_apply] using hi

end HighamBench
