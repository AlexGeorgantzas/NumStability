import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational
import NumStability.Source.Higham.Chapter28.Section03.Theorem01.StewartHaar.Stewart

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Stewart under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

private local instance instMeasurableSpaceRSqMat_relocated_SingleHouseholderRankTwo (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private theorem householder_mul_apply_rectangular
    {m n : ℕ} (u : Fin m → ℝ) (beta : ℝ) (S : RMat m n)
    (i : Fin m) (j : Fin n) :
    ((show RSqMat m from householder m u beta) * S) i j =
      S i j - beta * u i * (∑ k : Fin m, u k * S k j) := by
  simp only [Matrix.mul_apply, householder, idMatrix]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  simp
  ring_nf

private theorem rectangular_mul_householder_apply
    {m n : ℕ} (S : RMat m n) (v : Fin n → ℝ) (gamma : ℝ)
    (i : Fin m) (j : Fin n) :
    (S * (show RSqMat n from householder n v gamma)) i j =
      S i j - gamma * (∑ k : Fin n, S i k * v k) * v j := by
  simp only [Matrix.mul_apply, householder, idMatrix]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp
  ring_nf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem singleHouseholder_product_factorization {m n : ℕ}
    (S : RMat m n) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (beta gamma : ℝ) :
    (show RSqMat m from householder m u beta) * S *
        (show RSqMat n from householder n v gamma) =
      S + singleHouseholderRandsvdCorrectionLeft S u v *
        singleHouseholderRandsvdCorrectionRight S u v beta gamma := by
  ext i j
  rw [rectangular_mul_householder_apply]
  simp_rw [householder_mul_apply_rectangular]
  have hsum :
      (∑ x : Fin n,
        (S i x - beta * u i * (∑ k : Fin m, u k * S k x)) * v x) =
        (∑ x : Fin n, S i x * v x) -
          beta * u i *
            (∑ x : Fin n, (∑ k : Fin m, u k * S k x) * v x) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  simp only [Matrix.add_apply, Matrix.mul_apply,
    singleHouseholderRandsvdCorrectionLeft,
    singleHouseholderRandsvdCorrectionRight]
  simp only [Fin.sum_univ_two]
  simp
  ring

/-- Higham's exact warning on p. 518: replacing each random orthogonal factor
by one Householder matrix yields the rectangular diagonal matrix plus an
explicit product through a two-dimensional space. -/
theorem singleHouseholder_randsvd_eq_diagonal_add_rankTwo {m n : ℕ}
    (sigma : ℕ → ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (beta gamma : ℝ) :
    randsvdMatrix (householder m u beta) sigma (householder n v gamma) =
      rectangularDiagonal sigma +
        singleHouseholderRandsvdCorrectionLeft (rectangularDiagonal sigma) u v *
          singleHouseholderRandsvdCorrectionRight
            (rectangularDiagonal sigma) u v beta gamma := by
  have hVsym :
      (show RSqMat n from householder n v gamma).transpose =
        (show RSqMat n from householder n v gamma) := by
    simpa [matTranspose] using householder_symmetric n v gamma
  unfold randsvdMatrix
  rw [hVsym]
  exact singleHouseholder_product_factorization
    (rectangularDiagonal sigma) u v beta gamma

/-- The correction in the preceding decomposition has matrix rank at most
two, including rectangular and degenerate dimensions. -/
theorem singleHouseholder_randsvd_correction_rank_le_two {m n : ℕ}
    (sigma : ℕ → ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (beta gamma : ℝ) :
    Matrix.rank
        (randsvdMatrix (householder m u beta) sigma (householder n v gamma) -
          rectangularDiagonal sigma) ≤ 2 := by
  have hfactor := singleHouseholder_randsvd_eq_diagonal_add_rankTwo
    sigma u v beta gamma
  have hsub :
      randsvdMatrix (householder m u beta) sigma (householder n v gamma) -
          rectangularDiagonal sigma =
        singleHouseholderRandsvdCorrectionLeft (rectangularDiagonal sigma) u v *
          singleHouseholderRandsvdCorrectionRight
            (rectangularDiagonal sigma) u v beta gamma := by
    rw [hfactor]
    abel
  rw [hsub]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width
      (singleHouseholderRandsvdCorrectionLeft
        (rectangularDiagonal sigma) u v))

end NumStability
