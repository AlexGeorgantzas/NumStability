import HighamBench.P40Definitions

namespace HighamBench

private lemma p40_trace_spectral_mul_psd_nonneg
    {n : ℕ} (Q Y : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hY : Y.PosSemidef) :
    0 ≤ Matrix.trace ((Q * Matrix.diagonal r * Q.transpose) * Y) := by
  let C := Q.transpose * Y * Q
  have hC : C.PosSemidef := by
    simpa [C, Matrix.conjTranspose] using hY.conjTranspose_mul_mul_same Q
  have htrace : 0 ≤ Matrix.trace (Matrix.diagonal r * C) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hr i) hC.diag_nonneg)
  rw [show (Q * Matrix.diagonal r * Q.transpose) * Y =
      Q * Matrix.diagonal r * (Q.transpose * Y) by noncomm_ring]
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  simpa [C, Matrix.mul_assoc] using htrace

private lemma p40_trace_mul_eq_frobenius_pairing
    {n : ℕ} (R K : Matrix (Fin n) (Fin n) ℝ) (hK : K.transpose = K) :
    Matrix.trace (R * K) = ∑ i, ∑ j, R i j * K i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij := congrFun (congrFun hK i) j
  simp only [Matrix.transpose_apply] at hij
  rw [hij]

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
  let p : Fin n → ℝ := fun i ↦ max (lambda i) 0
  let r : Fin n → ℝ := fun i ↦ max (lambda i) 0 - lambda i
  let P : Matrix (Fin n) (Fin n) ℝ := Q * Matrix.diagonal p * Q.transpose
  let R : Matrix (Fin n) (Fin n) ℝ := Q * Matrix.diagonal r * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * P * Sinv
  have hp : ∀ i, 0 ≤ p i := fun i ↦ by simp [p]
  have hr : ∀ i, 0 ≤ r i := fun i ↦ by simp [r]
  have hDp : (Matrix.diagonal p).PosSemidef := Matrix.PosSemidef.diagonal hp
  have hDr : (Matrix.diagonal r).PosSemidef := Matrix.PosSemidef.diagonal hr
  have hP : P.PosSemidef := by
    simpa [P, Matrix.conjTranspose] using hDp.mul_mul_conjTranspose_same Q
  have hR : R.PosSemidef := by
    simpa [R, Matrix.conjTranspose] using hDr.mul_mul_conjTranspose_same Q
  have hX : X.PosSemidef := by
    simpa [X, hSinvSymm, Matrix.conjTranspose] using hP.mul_mul_conjTranspose_same Sinv
  have hP_formula : p40SpectralPositivePart Q lambda = P := by
    rfl
  have hX_formula : p40WeightedPsdProjection Sinv Q lambda = X := by
    simp only [p40WeightedPsdProjection, hP_formula, X]
  have hB_to_P : P - S * A * S = R := by
    rw [hSpectral]
    have hdiag_sub : Matrix.diagonal p - Matrix.diagonal lambda = Matrix.diagonal r := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [p, r]
      · simp [hij]
    simp only [P, R]
    calc
      Q * Matrix.diagonal p * Q.transpose -
          Q * Matrix.diagonal lambda * Q.transpose =
          Q * (Matrix.diagonal p - Matrix.diagonal lambda) * Q.transpose := by
            noncomm_ring
      _ = Q * Matrix.diagonal r * Q.transpose := by rw [hdiag_sub]
  have hSX : S * X * S = P := by
    calc
      S * X * S = (S * Sinv) * P * (Sinv * S) := by
        simp only [X]
        noncomm_ring
      _ = P := by rw [hSInv, hInvS]; simp
  have hA_formula : A = Sinv * (S * A * S) * Sinv := by
    calc
      A = (Sinv * S) * A * (S * Sinv) := by rw [hInvS, hSInv]; simp
      _ = Sinv * (S * A * S) * Sinv := by noncomm_ring
  have hXA : X - A = Sinv * R * Sinv := by
    rw [hA_formula]
    calc
      X - Sinv * (S * A * S) * Sinv = Sinv * (P - S * A * S) * Sinv := by
        simp only [X]
        noncomm_ring
      _ = Sinv * R * Sinv := by rw [hB_to_P]
  have hXA_psd : (X - A).PosSemidef := by
    rw [hXA]
    simpa [hSinvSymm, Matrix.conjTranspose] using hR.mul_mul_conjTranspose_same Sinv
  refine hX_formula.symm ▸ ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let Y : Matrix (Fin n) (Fin n) ℝ := S * Z * S
    have hY : Y.PosSemidef := by
      simpa [Y, hSsymm, Matrix.conjTranspose] using hZ.mul_mul_conjTranspose_same S
    have hSY : S * (A - Z) * S = S * A * S - Y := by
      simp only [Y]
      noncomm_ring
    have hSP : S * (A - X) * S = S * A * S - P := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hSX]
    have horth : ∀ i, r i * p i = 0 := by
      intro i
      rcases le_total (lambda i) 0 with h | h
      · simp [r, p, max_eq_right h]
      · simp [r, p, max_eq_left h]
    have hdiag : Matrix.diagonal r * Matrix.diagonal p = 0 := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [horth]
      · simp [hij]
    have hRP : R * P = 0 := by
      simp only [R, P]
      calc
        (Q * Matrix.diagonal r * Q.transpose) *
            (Q * Matrix.diagonal p * Q.transpose) =
            Q * Matrix.diagonal r * (Q.transpose * Q) *
              Matrix.diagonal p * Q.transpose := by noncomm_ring
        _ = Q * (Matrix.diagonal r * Matrix.diagonal p) * Q.transpose := by
          rw [hQtQ]
          noncomm_ring
        _ = 0 := by rw [hdiag]; simp
    have htraceRY : 0 ≤ Matrix.trace (R * Y) := by
      exact p40_trace_spectral_mul_psd_nonneg Q Y r hr hY
    have htrace : 0 ≤ Matrix.trace (R * (Y - P)) := by
      rw [Matrix.mul_sub, Matrix.trace_sub, hRP, Matrix.trace_zero, sub_zero]
      exact htraceRY
    have hYsymm : Y.transpose = Y := by
      simpa [Matrix.conjTranspose] using hY.isHermitian.eq
    have hPsymm : P.transpose = P := by
      simpa [Matrix.conjTranspose] using hP.isHermitian.eq
    have hYPsymm : (Y - P).transpose = Y - P := by
      rw [Matrix.transpose_sub, hYsymm, hPsymm]
    have hpair : 0 ≤ ∑ i, ∑ j, R i j * (Y - P) i j := by
      rw [← p40_trace_mul_eq_frobenius_pairing R (Y - P) hYPsymm]
      exact htrace
    have hsquares : 0 ≤ p40FrobeniusSq (P - Y) := by
      exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _))
    have hexpand :
        p40FrobeniusSq (S * A * S - Y) =
          p40FrobeniusSq (S * A * S - P) + p40FrobeniusSq (P - Y) +
            2 * (∑ i, ∑ j, R i j * (Y - P) i j) := by
      simp only [p40FrobeniusSq]
      have hentry : ∀ i j,
          ((S * A * S - Y) i j) ^ 2 =
            ((S * A * S - P) i j) ^ 2 + ((P - Y) i j) ^ 2 +
              2 * (R i j * (Y - P) i j) := by
        intro i j
        have hrij := congrFun (congrFun hB_to_P i) j
        simp only [Matrix.sub_apply] at hrij ⊢
        rw [← hrij]
        ring
      have hcross :
          (∑ i, ∑ j, 2 * (R i j * (Y - P) i j)) =
            2 * (∑ i, ∑ j, R i j * (Y - P) i j) := by
        simp only [Finset.mul_sum]
      simp_rw [hentry]
      simp only [Finset.sum_add_distrib]
      rw [hcross]
    rw [p40WeightedFrobeniusSq, p40WeightedFrobeniusSq, hSP, hSY]
    rw [hexpand]
    nlinarith
  · intro i
    have hii := hXA_psd.diag_nonneg (i := i)
    simp only [Matrix.sub_apply] at hii
    linarith

end HighamBench
