import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic

/-!
# NumStability Algorithms NormEstimation TwoNorm Dixon Algebra DixonCompletion

Canonical destination for material split out of
`NumStability.Algorithms.Ch15DixonClosure` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory Set

open scoped BigOperators Matrix MatrixOrder RealInnerProductSpace

set_option maxHeartbeats 800000

theorem ch15Closure_matPow_matrix_eq_pow {n : ℕ}
    (M : Fin n → Fin n → ℝ) (k : ℕ) :
    (matPow n M k : Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.of M) ^ k := by
  induction k with
  | zero =>
      ext i j
      by_cases hij : i = j <;> simp [matPow, idMatrix, hij]
  | succ k ih =>
      rw [matPow_succ, pow_succ']
      ext i j
      change (∑ p : Fin n, M i p * matPow n M k p j) =
        ∑ p : Fin n, Matrix.of M i p * (Matrix.of M ^ k) p j
      apply Finset.sum_congr rfl
      intro p _
      rw [show matPow n M k p j = (Matrix.of M ^ k) p j from
        congrFun (congrFun ih p) j]
      rfl

theorem ch15Closure_gram_symmetric {n : ℕ} (B : Fin n → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (matMul n (matTranspose B) B) := by
  intro i j
  simp only [matMul, matTranspose]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem ch15Closure_gram_pow_finitePSD {n : ℕ} (B : Fin n → Fin n → ℝ) (k : ℕ) :
    finitePSD (matPow n (matMul n (matTranspose B) B) k) := by
  let BM : Matrix (Fin n) (Fin n) ℝ := B
  let G : Fin n → Fin n → ℝ := matMul n (matTranspose B) B
  have hG : (G : Matrix (Fin n) (Fin n) ℝ) = BM.transpose * BM := by
    ext i j
    simp [G, BM, matMul, matTranspose, Matrix.mul_apply]
  have hGpos : Matrix.PosSemidef (G : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hG]
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.posSemidef_conjTranspose_mul_self BM
  let GM : Matrix (Fin n) (Fin n) ℝ := Matrix.of G
  have hGM : GM = (G : Matrix (Fin n) (Fin n) ℝ) := rfl
  have hGMpos : Matrix.PosSemidef GM := by simpa [hGM] using hGpos
  have hpow_pos : Matrix.PosSemidef (GM ^ k) := by
    induction k with
    | zero => simpa using (Matrix.PosSemidef.one :
        Matrix.PosSemidef (1 : Matrix (Fin n) (Fin n) ℝ))
    | succ k ih =>
        rw [pow_succ']
        exact (Matrix.PosSemidef.commute_iff hGMpos ih).mp
          (Commute.self_pow GM k)
  apply Matrix_posSemidef.to_finitePSD
  rw [ch15Closure_matPow_matrix_eq_pow]
  simpa [GM, G] using hpow_pos

theorem ch15Closure_matPow_symmetric {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) (k : ℕ) :
    IsSymmetricFiniteMatrix (matPow n M k) := by
  let MM : Matrix (Fin n) (Fin n) ℝ := Matrix.of M
  have hHerm : Matrix.IsHermitian MM :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  have hpHerm : Matrix.IsHermitian
      (MM ^ k) := hHerm.pow k
  intro i j
  have hij := Matrix.IsHermitian.apply hpHerm i j
  rw [show MM = Matrix.of M from rfl, ← ch15Closure_matPow_matrix_eq_pow M k] at hij
  simpa using hij.symm

theorem ch15Closure_matPow_mulVec_eigenvector {n : ℕ}
    (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (lam : ℝ)
    (hEig : matMulVec n M v = fun i => lam * v i) (k : ℕ) :
    matMulVec n (matPow n M k) v = fun i => lam ^ k * v i := by
  induction k with
  | zero =>
      funext i
      simp [matPow, matMulVec, idMatrix]
  | succ k ih =>
      funext i
      rw [matPow_succ_right]
      rw [matMulVec_matMul]
      rw [hEig]
      have hscale := congrFun
        (matMulVec_const_mul_right n (matPow n M k) lam v) i
      rw [hscale, congrFun ih i]
      ring

theorem ch15Closure_exists_gram_opNorm2_sq_unit_eigenvector (d : ℕ)
    (B : Fin (d + 1) → Fin (d + 1) → ℝ) :
    ∃ v : Fin (d + 1) → ℝ,
      (∑ i : Fin (d + 1), v i ^ 2) = 1 ∧
      matMulVec (d + 1) (matMul (d + 1) (matTranspose B) B) v =
        fun i => opNorm2 B ^ 2 * v i := by
  let n := d + 1
  let G : Fin n → Fin n → ℝ := matMul n (matTranspose B) B
  have hn : 0 < n := by omega
  have hGsym : IsSymmetricFiniteMatrix G := by
    simpa [G, n] using ch15Closure_gram_symmetric B
  let lam : ℝ := finiteMaxEigenvalue hn G hGsym
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn G hGsym
  let v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian G hGsym).eigenvectorBasis a)
  have hvnorm : (∑ i : Fin n, v i ^ 2) = 1 := by
    have h := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one G hGsym a
    simpa [finiteVecNorm2Sq, v] using h
  have hveig_lam : matMulVec n G v = fun i => lam * v i := by
    have h := finiteMatVec_finiteHermitianEigenvector_eq G hGsym a
    rw [ha] at h
    simpa [finiteMatVec, matMulVec, lam, v] using h
  have hcert : opNorm2Le B (Real.sqrt lam) := by
    have h := opNorm2Le_sqrt_maxEigenvalue_gram n hn B
      (by simpa [G, matMul, matTranspose] using hGsym)
    simpa [lam, G, matMul, matTranspose] using h
  have hlam_nonneg : 0 ≤ lam := by
    have hpsd : finitePSD G := by
      have hp := ch15Closure_gram_pow_finitePSD B 1
      simpa [G, n, matPow_one] using hp
    have heigs := (finitePSD_iff_finiteHermitianEigenvalues_nonneg G hGsym).mp hpsd a
    simpa [lam, ha] using heigs
  have hop_le_sqrt : opNorm2 B ≤ Real.sqrt lam :=
    opNorm2_le_of_opNorm2Le B (Real.sqrt_nonneg lam) hcert
  have hop_sq_le : opNorm2 B ^ 2 ≤ lam := by
    nlinarith [Real.sq_sqrt hlam_nonneg, opNorm2_nonneg B,
      Real.sqrt_nonneg lam]
  have hlam_le : lam ≤ opNorm2 B ^ 2 := by
    have h := maxEigenvalue_gram_le_sq_of_opNorm2Le n hn B
      (by simpa [G, matMul, matTranspose] using hGsym)
      (opNorm2 B) (opNorm2Le_opNorm2 B)
    simpa [lam, G, matMul, matTranspose] using h
  have hlam : lam = opNorm2 B ^ 2 := le_antisymm hlam_le hop_sq_le
  refine ⟨v, ?_, ?_⟩
  · simpa [n] using hvnorm
  · simpa [n, G, hlam] using hveig_lam

noncomputable def ch15Closure_unitSphereOfFiniteVec (d : ℕ)
    (v : Fin (d + 1) → ℝ) (hv : (∑ i, v i ^ 2) = 1) :
    OrthogonalSphere (d + 1) :=
  ⟨WithLp.toLp 2 v, by
    rw [Metric.mem_sphere, dist_zero_right]
    have hsq : ‖WithLp.toLp 2 v‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [Real.norm_eq_abs, sq_abs] using hv
    nlinarith [norm_nonneg (WithLp.toLp 2 v)]⟩

theorem ch15Closure_sqrt_inv_pow_eq_rpow_neg_half (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) :
    Real.sqrt ((θ ^ k)⁻¹) = θ ^ (-(k : ℝ) / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.inv_rpow (pow_nonneg hθ k)]
  rw [← Real.rpow_neg (pow_nonneg hθ k)]
  rw [← Real.rpow_natCast_mul hθ]
  congr 1
  ring

end NumStability
