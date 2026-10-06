import Mathlib.Analysis.SpecialFunctions.Stirling
import NumStability.Analysis.TestMatrices.Hilbert.Asymptotics
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics.Asymptotics
import NumStability.Source.Higham.Chapter28.Section03.RandomSVD.RandsvdNorm
import NumStability.Analysis.TestMatrices.Companion.Contracts
import NumStability.Analysis.TestMatrices.Pascal.Contracts
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts
import NumStability.Source.Higham.Chapter09.Problems

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Contracts under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators

private theorem sin_neighbor_identity (x θ : ℝ) :
    Real.sin (x - θ) + Real.sin (x + θ) =
      2 * Real.cos θ * Real.sin x := by
  rw [Real.sin_sub, Real.sin_add]
  ring

private theorem toeplitzSineVector_angle
    {n : ℕ} (k i : Fin n) :
    toeplitzSineVector n k i =
      Real.sin (((i.val + 1 : ℕ) : ℝ) *
        ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) := by
  unfold toeplitzSineVector
  congr 1
  push_cast
  ring

private theorem toeplitz_sine_boundary
    {n : ℕ} (k : Fin n) :
    Real.sin (((n + 1 : ℕ) : ℝ) *
      ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) = 0 := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [show (((n + 1 : ℕ) : ℝ) *
      ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) =
      ((k.val + 1 : ℕ) : ℝ) * Real.pi by field_simp]
  exact Real.sin_nat_mul_pi (k.val + 1)

/-- Higham, p. 522: the displayed sine vector is an actual eigenvector of the
symmetric tridiagonal Toeplitz matrix.  The trigonometric recurrence and both
boundary cases are proved here, rather than supplied as a hypothesis. -/
theorem symmetricToeplitz_sine_eigenpair
    {n : ℕ} (c d : ℝ) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d c)
        (toeplitzSineVector n k) =
      symmetricToeplitzEigenvalue n c d k • toeplitzSineVector n k := by
  funext i
  rw [tridiagonalToeplitz_mulVec_apply]
  rw [show symmetricToeplitzEigenvalue n c d k =
      d + 2 * c * Real.cos
        (((k.val + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)) by rfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [toeplitzSineVector_angle]
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  let x : ℝ := ((i.val + 1 : ℕ) : ℝ) * θ
  rw [show (((k.val + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)) = θ by rfl]
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hcur : ((i.val + 1 : ℕ) : ℝ) * θ = x := rfl
      have hsucc :
          ((i.val + 1 + 1 : ℕ) : ℝ) * θ = x + θ := by
        dsimp [x]
        push_cast
        ring
      have hpred :
          ((i.val - 1 + 1 : ℕ) : ℝ) * θ = x - θ := by
        rw [Nat.sub_add_cancel hp]
        dsimp [x]
        push_cast
        ring
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val + 1 + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val - 1 + 1 : ℕ) : ℝ) * θ) =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hcur, hsucc, hpred]
      have hrec := sin_neighbor_identity x θ
      linear_combination c * hrec
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, ↓reduceDIte]
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val + 1 + 1 : ℕ) : ℝ) * θ) + 0 =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hi0]
      norm_num
      rw [show 2 * θ = θ + θ by ring, Real.sin_add]
      ring
  · have hilast : i.val + 1 = n := by omega
    by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hcur : ((i.val + 1 : ℕ) : ℝ) * θ = x := rfl
      have hpred :
          ((i.val - 1 + 1 : ℕ) : ℝ) * θ = x - θ := by
        rw [Nat.sub_add_cancel hp]
        dsimp [x]
        push_cast
        ring
      have hboundary : Real.sin (x + θ) = 0 := by
        rw [show x + θ = ((n + 1 : ℕ) : ℝ) * θ by
          dsimp [x]
          rw [show ((i.val + 1 : ℕ) : ℝ) = (n : ℝ) by exact_mod_cast hilast]
          push_cast
          ring]
        exact toeplitz_sine_boundary k
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) + 0 +
          c * Real.sin (((i.val - 1 + 1 : ℕ) : ℝ) * θ) =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hcur, hpred]
      have hrec := sin_neighbor_identity x θ
      rw [hboundary] at hrec
      linear_combination c * hrec
    · have hn1 : n = 1 := by omega
      subst n
      fin_cases i
      fin_cases k
      dsimp [θ, x]
      norm_num [toeplitzSineVector, symmetricToeplitzEigenvalue]

/-- The displayed sine eigenvector is nonzero; its first component has angle
strictly between zero and pi. -/
theorem toeplitzSineVector_ne_zero
    {n : ℕ} (k : Fin n) : toeplitzSineVector n k ≠ 0 := by
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hratio : ((k.val + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ k.isLt
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  intro hzero
  have hz := congrFun hzero i0
  have hi : toeplitzSineVector n k i0 = Real.sin θ := by
    rw [toeplitzSineVector_angle]
    simp [i0, θ]
  rw [hi] at hz
  exact (ne_of_gt hsin) hz

private theorem scaledSineColumn_eq
    {n : ℕ} (k : Fin n) :
    (fun i : Fin n => higham9_12_sineMatrix n i k) =
      Real.sqrt (2 / ((n : ℝ) + 1)) • toeplitzSineVector n k := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold higham9_12_sineMatrix toeplitzSineVector
  congr 2
  norm_num [Nat.cast_add]

/-- The normalized discrete-sine columns are eigenvectors as well. -/
theorem symmetricToeplitz_scaled_sine_eigenpair
    {n : ℕ} (c d : ℝ) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d c)
        (fun i => higham9_12_sineMatrix n i k) =
      symmetricToeplitzEigenvalue n c d k •
        (fun i => higham9_12_sineMatrix n i k) := by
  rw [scaledSineColumn_eq]
  rw [Matrix.mulVec_smul, symmetricToeplitz_sine_eigenpair]
  simp [smul_smul, mul_comm]

/-- The normalized sine matrix is orthogonal, reusing the independently
proved finite sine-product identity from Chapter 9. -/
theorem higham9_sineMatrix_isOrthogonal
    {n : ℕ} (hn : 0 < n) : IsOrthogonal n (higham9_12_sineMatrix n) := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  simpa [higham9_12_sineMatrix_symm] using
    higham9_12_sineMatrix_mul_self hn i j

/-- Exact orthogonal diagonalization of every nonempty symmetric tridiagonal
Toeplitz matrix.  This supplies the complete symmetric-family eigenvalue
multiset without an assumed component identity or independence hypothesis. -/
theorem symmetricToeplitz_orthogonal_diagonalization
    {n : ℕ} (hn : 0 < n) (c d : ℝ) :
    tridiagonalToeplitz n c d c =
      finiteMatMul (higham9_12_sineMatrix n)
        (finiteMatMul (finiteDiagonal (symmetricToeplitzEigenvalue n c d))
          (matTranspose (higham9_12_sineMatrix n))) := by
  apply finiteMatrix_eq_orthogonal_diagonalization_of_orthonormal_eigenvectors
  · intro i j
    exact (higham9_sineMatrix_isOrthogonal hn).col_orthonormal i j
  · intro k
    simpa [finiteMatVec, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
      symmetricToeplitz_scaled_sine_eigenpair c d k

end NumStability
