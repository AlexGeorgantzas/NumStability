import HighamBench.P40Definitions

namespace HighamBench

private lemma p40FrobeniusSq_eq_trace_mul_transpose {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    p40FrobeniusSq M = Matrix.trace (M * M.transpose) := by
  simp [p40FrobeniusSq, Matrix.trace, Matrix.mul_apply, pow_two]

private lemma p40FrobeniusSq_orthogonal_conjugation {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ) (hQQt : Q * Q.transpose = 1) :
    p40FrobeniusSq (Q.transpose * M * Q) = p40FrobeniusSq M := by
  rw [p40FrobeniusSq_eq_trace_mul_transpose,
    p40FrobeniusSq_eq_trace_mul_transpose]
  have hprod :
      (Q.transpose * M * Q) * (Q.transpose * M * Q).transpose =
        Q.transpose * (M * M.transpose) * Q := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      (Q.transpose * M * Q) * (Q.transpose * (M.transpose * Q)) =
          Q.transpose * M * (Q * Q.transpose) * M.transpose * Q := by
        noncomm_ring
      _ = Q.transpose * (M * M.transpose) * Q := by rw [hQQt]; noncomm_ring
  rw [hprod]
  calc
    Matrix.trace (Q.transpose * (M * M.transpose) * Q) =
        Matrix.trace (Q * Q.transpose * (M * M.transpose)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (M * M.transpose) := by rw [hQQt, one_mul]

private lemma posSemidef_congruence {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    (B * M * B.transpose).PosSemidef := by
  simpa [Matrix.conjTranspose] using hM.mul_mul_conjTranspose_same B

private lemma spectral_positive_part_minimizes {n : ℕ}
    (lambda : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y.PosSemidef) :
    p40FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i ↦ max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - Y) := by
  have hleft :
      p40FrobeniusSq
          (Matrix.diagonal lambda - Matrix.diagonal (fun i ↦ max (lambda i) 0)) =
        ∑ i, (lambda i - max (lambda i) 0) ^ 2 := by
    classical
    simp only [p40FrobeniusSq, Matrix.sub_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Matrix.diagonal_apply, Ne.symm hji]
    · simp
  have hscalar : ∀ i,
      (lambda i - max (lambda i) 0) ^ 2 ≤ (lambda i - Y i i) ^ 2 := by
    intro i
    have hy : 0 ≤ Y i i := hY.diag_nonneg
    by_cases hl : lambda i ≤ 0
    · rw [max_eq_right hl]
      nlinarith
    · have hl' : 0 ≤ lambda i := le_of_not_ge hl
      rw [max_eq_left hl']
      simpa using sq_nonneg (lambda i - Y i i)
  have hinner : ∀ i,
      (lambda i - Y i i) ^ 2 ≤
        ∑ j, ((Matrix.diagonal lambda - Y) i j) ^ 2 := by
    intro i
    have h := Finset.single_le_sum
      (s := Finset.univ) (f := fun j ↦ ((Matrix.diagonal lambda - Y) i j) ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
    simpa [Matrix.sub_apply] using h
  rw [hleft]
  calc
    (∑ i, (lambda i - max (lambda i) 0) ^ 2) ≤
        ∑ i, (lambda i - Y i i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hscalar i
    _ ≤ ∑ i, ∑ j, ((Matrix.diagonal lambda - Y) i j) ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ hinner i
    _ = p40FrobeniusSq (Matrix.diagonal lambda - Y) := by
      rfl

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
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let Dp : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i ↦ max (lambda i) 0)
  let Bp : Matrix (Fin n) (Fin n) ℝ := Q * Dp * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * Bp * Sinv
  change X.PosSemidef ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
      p40WeightedFrobeniusSq S (A - X) ≤
        p40WeightedFrobeniusSq S (A - Z)) ∧
    ∀ i, A i i ≤ X i i

  have hDp : Dp.PosSemidef := by
    dsimp [Dp]
    exact Matrix.PosSemidef.diagonal (fun i ↦ le_max_right (lambda i) 0)
  have hBp : Bp.PosSemidef := by
    dsimp [Bp]
    exact posSemidef_congruence hDp Q
  have hX : X.PosSemidef := by
    dsimp [X]
    simpa [hSinvSymm] using posSemidef_congruence hBp Sinv

  have hSpectralD : S * A * S = Q * D * Q.transpose := by
    simpa [D] using hSpectral
  have hSXS : S * X * S = Bp := by
    dsimp [X]
    calc
      S * (Sinv * Bp * Sinv) * S =
          (S * Sinv) * Bp * (Sinv * S) := by noncomm_ring
      _ = Bp := by rw [hSInv, hInvS]; simp
  have hcoordX :
      Q.transpose * (S * (A - X) * S) * Q = D - Dp := by
    calc
      Q.transpose * (S * (A - X) * S) * Q =
          Q.transpose * ((S * A * S) - (S * X * S)) * Q := by
        noncomm_ring
      _ = Q.transpose * ((Q * D * Q.transpose) - Bp) * Q := by
        rw [hSpectralD, hSXS]
      _ = Q.transpose *
          ((Q * D * Q.transpose) - (Q * Dp * Q.transpose)) * Q := by
        rfl
      _ = (Q.transpose * Q) * (D - Dp) * (Q.transpose * Q) := by
        noncomm_ring
      _ = D - Dp := by rw [hQtQ]; simp

  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let Y : Matrix (Fin n) (Fin n) ℝ :=
      Q.transpose * (S * Z * S) * Q
    have hSZS : (S * Z * S).PosSemidef := by
      simpa [hSsymm] using posSemidef_congruence hZ S
    have hY : Y.PosSemidef := by
      dsimp [Y]
      simpa using posSemidef_congruence hSZS Q.transpose
    have hcoordZ :
        Q.transpose * (S * (A - Z) * S) * Q = D - Y := by
      calc
        Q.transpose * (S * (A - Z) * S) * Q =
            Q.transpose * ((S * A * S) - (S * Z * S)) * Q := by
          noncomm_ring
        _ = Q.transpose * ((Q * D * Q.transpose) - (S * Z * S)) * Q := by
          rw [hSpectralD]
        _ = (Q.transpose * Q) * D * (Q.transpose * Q) -
            Q.transpose * (S * Z * S) * Q := by
          noncomm_ring
        _ = D - Y := by rw [hQtQ]; simp [Y]
    have hobjX :
        p40WeightedFrobeniusSq S (A - X) =
          p40FrobeniusSq (D - Dp) := by
      calc
        p40WeightedFrobeniusSq S (A - X) =
            p40FrobeniusSq (S * (A - X) * S) := rfl
        _ = p40FrobeniusSq
            (Q.transpose * (S * (A - X) * S) * Q) :=
          (p40FrobeniusSq_orthogonal_conjugation Q
            (S * (A - X) * S) hQQt).symm
        _ = p40FrobeniusSq (D - Dp) := congrArg p40FrobeniusSq hcoordX
    have hobjZ :
        p40WeightedFrobeniusSq S (A - Z) =
          p40FrobeniusSq (D - Y) := by
      calc
        p40WeightedFrobeniusSq S (A - Z) =
            p40FrobeniusSq (S * (A - Z) * S) := rfl
        _ = p40FrobeniusSq
            (Q.transpose * (S * (A - Z) * S) * Q) :=
          (p40FrobeniusSq_orthogonal_conjugation Q
            (S * (A - Z) * S) hQQt).symm
        _ = p40FrobeniusSq (D - Y) := congrArg p40FrobeniusSq hcoordZ
    calc
      p40WeightedFrobeniusSq S (A - X) =
          p40FrobeniusSq (D - Dp) := hobjX
      _ ≤ p40FrobeniusSq (D - Y) := by
        simpa [D, Dp] using spectral_positive_part_minimizes lambda Y hY
      _ = p40WeightedFrobeniusSq S (A - Z) := hobjZ.symm
  · let Delta : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.diagonal (fun i ↦ max (lambda i) 0 - lambda i)
    have hDelta : Delta.PosSemidef := by
      dsimp [Delta]
      exact Matrix.PosSemidef.diagonal (fun i ↦ sub_nonneg.mpr (le_max_left _ _))
    have hDpD : Dp - D = Delta := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Dp, D, Delta, Matrix.sub_apply]
      · simp [Dp, D, Delta, Matrix.sub_apply, hij]
    have hbaseEq : Bp - S * A * S = Q * Delta * Q.transpose := by
      rw [hSpectralD]
      dsimp [Bp]
      calc
        Q * Dp * Q.transpose - Q * D * Q.transpose =
            Q * (Dp - D) * Q.transpose := by noncomm_ring
        _ = Q * Delta * Q.transpose := by rw [hDpD]
    have hbase : (Bp - S * A * S).PosSemidef := by
      rw [hbaseEq]
      exact posSemidef_congruence hDelta Q
    have hAinv : A = Sinv * (S * A * S) * Sinv := by
      symm
      calc
        Sinv * (S * A * S) * Sinv =
            (Sinv * S) * A * (S * Sinv) := by noncomm_ring
        _ = A := by rw [hInvS, hSInv]; simp
    have hXAeq : X - A = Sinv * (Bp - S * A * S) * Sinv := by
      calc
        X - A = X - Sinv * (S * A * S) * Sinv :=
          congrArg (fun M ↦ X - M) hAinv
        _ = Sinv * (Bp - S * A * S) * Sinv := by
          dsimp [X]
          noncomm_ring
    have hXA : (X - A).PosSemidef := by
      rw [hXAeq]
      simpa [hSinvSymm] using posSemidef_congruence hbase Sinv
    intro i
    have hi : 0 ≤ (X - A) i i := hXA.diag_nonneg
    simpa [Matrix.sub_apply] using hi

end HighamBench
