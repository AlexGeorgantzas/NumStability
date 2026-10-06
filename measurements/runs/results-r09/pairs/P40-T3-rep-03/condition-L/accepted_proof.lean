import HighamBench.P40Definitions
import NumStability.Analysis.MatrixAlgebra

namespace HighamBench

open scoped BigOperators

private lemma p40_scalar_projection_sq_le (a y : ℝ) (hy : 0 ≤ y) :
    (a - max a 0) ^ 2 ≤ (a - y) ^ 2 := by
  by_cases ha : 0 ≤ a
  · simpa [max_eq_left ha] using (sq_nonneg (a - y))
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_right ha0]
    nlinarith [sq_nonneg y, mul_nonpos_of_nonpos_of_nonneg ha0 hy]

private lemma p40_diagonal_positive_part_minimizes
    {n : ℕ} (lambda : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y.PosSemidef) :
    p40FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p40FrobeniusSq (Matrix.diagonal lambda - Y) := by
  classical
  unfold p40FrobeniusSq
  rw [Matrix.diagonal_sub]
  calc
    ∑ i, ∑ j,
          (Matrix.diagonal (lambda - fun i => max (lambda i) 0) i j) ^ 2 =
        ∑ i, (lambda i - max (lambda i) 0) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Matrix.diagonal_apply, Pi.sub_apply]
    _ ≤ ∑ i, (lambda i - Y i i) ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            p40_scalar_projection_sq_le _ _ hY.diag_nonneg
    _ ≤ ∑ i, ∑ j, ((Matrix.diagonal lambda - Y) i j) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
          have hsingle := Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin n)))
            (f := fun j => ((Matrix.diagonal lambda - Y) i j) ^ 2)
            (fun j _ => sq_nonneg _) hi
          simpa [Matrix.diagonal_apply] using hsingle

private lemma p40_frobeniusSq_orthogonal_conjugation
    {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQ : NumStability.IsOrthogonal n Q) :
    p40FrobeniusSq (Q * M * Q.transpose) = p40FrobeniusSq M := by
  change NumStability.frobNormSq (Q * M * Q.transpose) =
    NumStability.frobNormSq M
  calc
    NumStability.frobNormSq (Q * M * Q.transpose) =
        NumStability.frobNormSq (Q * M) := by
          simpa [NumStability.matMul, Matrix.mul_apply,
            NumStability.matTranspose] using
            (NumStability.frobNormSq_orthogonal_right
              (n := n) (Q * M) Q.transpose hQ.transpose)
    _ = NumStability.frobNormSq M := by
          simpa [NumStability.matMul, Matrix.mul_apply] using
            (NumStability.frobNormSq_orthogonal_left
              (n := n) Q M hQ)

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
  let P : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let B : Matrix (Fin n) (Fin n) ℝ := S * A * S
  let PB : Matrix (Fin n) (Fin n) ℝ := Q * P * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * PB * Sinv
  have hQorth : NumStability.IsOrthogonal n Q := by
    constructor
    · intro i j
      have hij := congrFun (congrFun hQtQ i) j
      simpa [NumStability.matTranspose, NumStability.idMatrix,
        Matrix.mul_apply, Matrix.one_apply] using hij
    · intro i j
      have hij := congrFun (congrFun hQQt i) j
      simpa [NumStability.matTranspose, NumStability.idMatrix,
        Matrix.mul_apply, Matrix.one_apply] using hij
  have hP : P.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right _ _
  have hPB : PB.PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same Q
    simpa [PB, Matrix.conjTranspose, star_trivial] using h
  have hX : X.PosSemidef := by
    have h := hPB.mul_mul_conjTranspose_same Sinv
    simpa [X, Matrix.conjTranspose, star_trivial, hSinvSymm] using h
  have hB : B = Q * D * Q.transpose := by
    simpa [B, D] using hSpectral
  have hSXS : S * X * S = PB := by
    calc
      S * X * S = (S * Sinv) * PB * (Sinv * S) := by
        simp only [X]
        noncomm_ring
      _ = PB := by rw [hSInv, hInvS]; simp
  have hAX : S * (A - X) * S = Q * (D - P) * Q.transpose := by
    calc
      S * (A - X) * S = B - PB := by
        simp only [B]
        rw [Matrix.mul_sub, Matrix.sub_mul, hSXS]
      _ = Q * (D - P) * Q.transpose := by
        simp only [hB, PB]
        noncomm_ring
  have hA_from_B : A = Sinv * B * Sinv := by
    symm
    calc
      Sinv * B * Sinv = (Sinv * S) * A * (S * Sinv) := by
        simp only [B]
        noncomm_ring
      _ = A := by rw [hInvS, hSInv]; simp
  have hPB_sub_B : (PB - B).PosSemidef := by
    have hdiag : (P - D).PosSemidef := by
      change (Matrix.diagonal (fun i => max (lambda i) 0) -
        Matrix.diagonal lambda).PosSemidef
      rw [Matrix.diagonal_sub]
      apply Matrix.PosSemidef.diagonal
      intro i
      exact sub_nonneg.mpr (le_max_left _ _)
    have h := hdiag.mul_mul_conjTranspose_same Q
    have heq : PB - B = Q * (P - D) * Q.transpose := by
      simp only [PB, hB]
      noncomm_ring
    rw [heq]
    simpa [Matrix.conjTranspose, star_trivial] using h
  have hX_sub_A : (X - A).PosSemidef := by
    have h := hPB_sub_B.mul_mul_conjTranspose_same Sinv
    have heq : X - A = Sinv * (PB - B) * Sinv := by
      rw [hA_from_B]
      simp only [X]
      noncomm_ring
    rw [heq]
    simpa [Matrix.conjTranspose, star_trivial, hSinvSymm] using h
  have hXdef : X = p40WeightedPsdProjection Sinv Q lambda := by
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa [p40WeightedPsdProjection, p40SpectralPositivePart, X, PB, P]
      using hX
  · intro Z hZ
    let C : Matrix (Fin n) (Fin n) ℝ := S * Z * S
    let Y : Matrix (Fin n) (Fin n) ℝ := Q.transpose * C * Q
    have hC : C.PosSemidef := by
      have h := hZ.mul_mul_conjTranspose_same S
      simpa [C, Matrix.conjTranspose, star_trivial, hSsymm] using h
    have hY : Y.PosSemidef := by
      have h := hC.conjTranspose_mul_mul_same Q
      simpa [Y, Matrix.conjTranspose, star_trivial] using h
    have hAZ : S * (A - Z) * S = Q * (D - Y) * Q.transpose := by
      have hres : S * (A - Z) * S = B - C := by
        simp only [B, C]
        rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [hres, hB]
      have heq : Q * (D - Y) * Q.transpose =
          Q * D * Q.transpose - C := by
        calc
          Q * (D - Y) * Q.transpose =
              Q * D * Q.transpose -
                (Q * Q.transpose) * C * (Q * Q.transpose) := by
                  simp only [Y]
                  noncomm_ring
          _ = Q * D * Q.transpose - C := by rw [hQQt]; simp
      exact heq.symm
    rw [← hXdef]
    unfold p40WeightedFrobeniusSq
    rw [hAX, hAZ,
      p40_frobeniusSq_orthogonal_conjugation Q (D - P) hQorth,
      p40_frobeniusSq_orthogonal_conjugation Q (D - Y) hQorth]
    exact p40_diagonal_positive_part_minimizes lambda Y hY
  · intro i
    have hii := hX_sub_A.diag_nonneg (i := i)
    change A i i ≤
      p40WeightedPsdProjection Sinv Q lambda i i
    rw [← hXdef]
    simpa using hii

end HighamBench
