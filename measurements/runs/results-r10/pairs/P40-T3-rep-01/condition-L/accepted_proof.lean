import HighamBench.P40Definitions
import NumStability.Analysis.MatrixAlgebra

namespace HighamBench

private lemma p40FrobeniusSq_orthogonal_left {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℝ)
    (hU : NumStability.IsOrthogonal n U) :
    p40FrobeniusSq (U * M) = p40FrobeniusSq M := by
  simpa [p40FrobeniusSq, NumStability.frobNormSq,
    NumStability.matMul, Matrix.mul_apply] using
    NumStability.frobNormSq_orthogonal_left U M hU

private lemma p40FrobeniusSq_orthogonal_right {n : ℕ}
    (M U : Matrix (Fin n) (Fin n) ℝ)
    (hU : NumStability.IsOrthogonal n U) :
    p40FrobeniusSq (M * U) = p40FrobeniusSq M := by
  simpa [p40FrobeniusSq, NumStability.frobNormSq,
    NumStability.matMul, Matrix.mul_apply] using
    NumStability.frobNormSq_orthogonal_right M U hU

private lemma p40_diagonal_positive_part_best {n : ℕ}
    (lambda : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) :
    p40FrobeniusSq
        (Matrix.diagonal lambda -
          Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - C) := by
  classical
  unfold p40FrobeniusSq
  apply Finset.sum_le_sum
  intro i hi
  have hscalar :
      (lambda i - max (lambda i) 0) ^ 2 ≤ (lambda i - C i i) ^ 2 := by
    have hCii : 0 ≤ C i i := hC.diag_nonneg
    by_cases hli : 0 ≤ lambda i
    · rw [max_eq_left hli]
      nlinarith [sq_nonneg (lambda i - C i i)]
    · rw [max_eq_right (le_of_not_ge hli)]
      nlinarith
  calc
    (∑ j : Fin n,
        ((Matrix.diagonal lambda -
          Matrix.diagonal (fun k => max (lambda k) 0)) i j) ^ 2) =
        (lambda i - max (lambda i) 0) ^ 2 := by
          rw [Finset.sum_eq_single i]
          · simp [Matrix.sub_apply]
          · intro j hj hji
            simp [Matrix.sub_apply, Matrix.diagonal_apply, Ne.symm hji]
          · simp
    _ ≤ (lambda i - C i i) ^ 2 := hscalar
    _ ≤ ∑ j : Fin n, ((Matrix.diagonal lambda - C) i j) ^ 2 := by
      simpa [Matrix.sub_apply] using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun j : Fin n => ((Matrix.diagonal lambda - C) i j) ^ 2)
          (fun j _ => sq_nonneg ((Matrix.diagonal lambda - C) i j))
          (Finset.mem_univ i))
      

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
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let P : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let Bp : Matrix (Fin n) (Fin n) ℝ := Q * P * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * Bp * Sinv

  have hQorth : NumStability.IsOrthogonal n Q := by
    constructor
    · intro i j
      have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hQtQ
      simpa [NumStability.IsLeftInverse, NumStability.matTranspose,
        Matrix.mul_apply] using hij
    · intro i j
      have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hQQt
      simpa [NumStability.IsRightInverse, NumStability.matTranspose,
        Matrix.mul_apply] using hij
  have hQTorth : NumStability.IsOrthogonal n Q.transpose := by
    simpa [NumStability.matTranspose] using hQorth.transpose

  have hP : P.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right _ _
  have hBp : Bp.PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same Q
    simpa [Bp, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hX : X.PosSemidef := by
    have h := hBp.mul_mul_conjTranspose_same Sinv
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] at h
    exact h

  have hSX : S * X * S = Bp := by
    calc
      S * X * S = (S * Sinv) * Bp * (Sinv * S) := by
        simp only [X]
        noncomm_ring
      _ = Bp := by rw [hSInv, hInvS, one_mul, mul_one]

  have hweightedX : S * (A - X) * S =
      Q * (D - P) * Q.transpose := by
    calc
      S * (A - X) * S = S * A * S - S * X * S := by
        simp only [mul_sub, sub_mul]
      _ = Q * D * Q.transpose - Bp := by
        rw [hSpectral, hSX]
      _ = Q * (D - P) * Q.transpose := by
        simp only [Bp, mul_sub, sub_mul]

  have hobjectiveX :
      p40WeightedFrobeniusSq S (A - X) = p40FrobeniusSq (D - P) := by
    rw [p40WeightedFrobeniusSq, hweightedX]
    calc
      p40FrobeniusSq (Q * (D - P) * Q.transpose) =
          p40FrobeniusSq (Q * (D - P)) :=
        p40FrobeniusSq_orthogonal_right _ _ hQTorth
      _ = p40FrobeniusSq (D - P) :=
        p40FrobeniusSq_orthogonal_left _ _ hQorth

  have hmin : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      Z.PosSemidef →
        p40WeightedFrobeniusSq S (A - X) ≤
          p40WeightedFrobeniusSq S (A - Z) := by
    intro Z hZ
    let Y : Matrix (Fin n) (Fin n) ℝ := S * Z * S
    let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * Y * Q
    have hY : Y.PosSemidef := by
      have h := hZ.mul_mul_conjTranspose_same S
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, hSsymm] at h
      exact h
    have hC : C.PosSemidef := by
      have h := hY.conjTranspose_mul_mul_same Q
      simpa [C, Matrix.conjTranspose_eq_transpose_of_trivial] using h
    have hcoordinate : Q.transpose * (S * (A - Z) * S) * Q = D - C := by
      calc
        Q.transpose * (S * (A - Z) * S) * Q =
            Q.transpose * (S * A * S - Y) * Q := by
          simp only [Y, mul_sub, sub_mul]
        _ = Q.transpose * (Q * D * Q.transpose - Y) * Q := by
          rw [hSpectral]
        _ = D - C := by
          simp only [C, mul_sub, sub_mul]
          rw [show Q.transpose * (Q * D * Q.transpose) * Q = D by
            calc
              Q.transpose * (Q * D * Q.transpose) * Q =
                  (Q.transpose * Q) * D * (Q.transpose * Q) := by noncomm_ring
              _ = D := by rw [hQtQ, one_mul, mul_one]]
    have hrotate :
        p40FrobeniusSq (S * (A - Z) * S) = p40FrobeniusSq (D - C) := by
      rw [← hcoordinate]
      symm
      calc
        p40FrobeniusSq (Q.transpose * (S * (A - Z) * S) * Q) =
            p40FrobeniusSq (Q.transpose * (S * (A - Z) * S)) :=
          p40FrobeniusSq_orthogonal_right _ _ hQorth
        _ = p40FrobeniusSq (S * (A - Z) * S) :=
          p40FrobeniusSq_orthogonal_left _ _ hQTorth
    rw [hobjectiveX, p40WeightedFrobeniusSq, hrotate]
    exact p40_diagonal_positive_part_best lambda C hC

  have hAformula : A = Sinv * (Q * D * Q.transpose) * Sinv := by
    calc
      A = (Sinv * S) * A * (S * Sinv) := by
        rw [hInvS, hSInv, one_mul, mul_one]
      _ = Sinv * (S * A * S) * Sinv := by noncomm_ring
      _ = Sinv * (Q * D * Q.transpose) * Sinv := by rw [hSpectral]
  let R : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0 - lambda i)
  have hR : R.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (le_max_left _ _)
  have hPD : P - D = R := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [P, D, R]
    · simp [P, D, R, Matrix.diagonal_apply, hij]
  have hdiff : X - A = Sinv * (Q * R * Q.transpose) * Sinv := by
    rw [hAformula]
    simp only [X, Bp]
    calc
      Sinv * (Q * P * Q.transpose) * Sinv -
          Sinv * (Q * D * Q.transpose) * Sinv =
          Sinv * (Q * (P - D) * Q.transpose) * Sinv := by noncomm_ring
      _ = Sinv * (Q * R * Q.transpose) * Sinv := by rw [hPD]
  have hdiffPsd : (X - A).PosSemidef := by
    rw [hdiff]
    have hQR : (Q * R * Q.transpose).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hR.mul_mul_conjTranspose_same Q
    have h := hQR.mul_mul_conjTranspose_same Sinv
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] at h
    exact h
  have hdiag : ∀ i, A i i ≤ X i i := by
    intro i
    have := hdiffPsd.diag_nonneg (i := i)
    simpa [Matrix.sub_apply] using this

  change X.PosSemidef ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
      p40WeightedFrobeniusSq S (A - X) ≤
        p40WeightedFrobeniusSq S (A - Z)) ∧
    ∀ i, A i i ≤ X i i
  exact ⟨hX, hmin, hdiag⟩

end HighamBench
