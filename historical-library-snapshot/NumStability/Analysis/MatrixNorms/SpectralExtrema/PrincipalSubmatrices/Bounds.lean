import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Bounds

Canonical destination for 3 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Eigenvalue interlacing, lower direction** (Golub–Van Loan
Thm 8.1.7 as used in the Theorem 10.7 induction, Higham p. 200): the
minimum eigenvalue of a leading principal submatrix of a symmetric matrix
is at least the minimum eigenvalue of the full matrix.  Proof: evaluate
the full Rayleigh bound at the zero-padded minimizing eigenvector of the
submatrix. -/
theorem finiteMinEigenvalue_leading_principal_ge (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hH : IsSymmetricFiniteMatrix H)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n)
    (hHk_sym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) :
    finiteMinEigenvalue hn H hH ≤
      finiteMinEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hk0
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin k → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin k, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hpadsq : ∑ i : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) ^ 2 = 1 := by
    rw [sum_sq_zero_pad_eq k hk v, hvsq]
  have hray := finiteMinEigenvalue_rayleigh hn H hH
    (fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0)
  rw [hpadsq, mul_one] at hray
  have hpadquad : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) * H i j *
        (if h : j.val < k then v ⟨j.val, h⟩ else 0) =
      finiteMinEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
    rw [quadForm_zero_pad_eq H k hk v, ← ha, ← hq,
      finiteQuadraticForm_eq_sum_sum]
  rw [hpadquad] at hray
  exact hray

/-- **Eigenvalue interlacing, upper direction** (the dual of
    `finiteMinEigenvalue_leading_principal_ge`, completing the
    two-sided leading-block spectral envelope): the maximum eigenvalue
    of a leading principal submatrix is at most the maximum eigenvalue
    of the full matrix — evaluate the full max-Rayleigh bound at the
    zero-padded maximizing eigenvector of the submatrix. -/
theorem finiteMaxEigenvalue_leading_principal_le (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hH : IsSymmetricFiniteMatrix H)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n)
    (hHk_sym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) :
    finiteMaxEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym ≤
      finiteMaxEigenvalue hn H hH := by
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hk0
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    hHk_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin k → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin k, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hpadsq : ∑ i : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) ^ 2 = 1 := by
    rw [sum_sq_zero_pad_eq k hk v, hvsq]
  have hray := finiteMaxEigenvalue_rayleigh hn H hH
    (fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0)
  rw [hpadsq, mul_one] at hray
  have hpadquad : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) * H i j *
        (if h : j.val < k then v ⟨j.val, h⟩ else 0) =
      finiteMaxEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
    rw [quadForm_zero_pad_eq H k hk v, ← ha, ← hq,
      finiteQuadraticForm_eq_sum_sum]
  rw [hpadquad] at hray
  exact hray

/-- **Bordered Rayleigh floor from `λ_min` of the scaled matrix** (the
    per-stage floor derivation of the Theorem 10.7 success proofs,
    factored): interlacing on the bordered leading blocks and the
    substitution `z = (√b_ii·y_i, √b_kk)` convert `λ_min(H)` of the
    scaled matrix `H = D⁻¹BD⁻¹` into the bordered quadratic floor used
    by the pivot-positivity inductions. -/
theorem min_eig_scaled_bordered_floor (N : ℕ) (hN0 : 0 < N)
    (B : Fin N → Fin N → ℝ)
    (hsymB : ∀ i l : Fin N, B i l = B l i)
    (hBdiag : ∀ i : Fin N, 0 < B i i)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin N =>
      B i l / (Real.sqrt (B i i) * Real.sqrt (B l l))))
    (k : Fin N) (y : Fin k.val → ℝ) :
    finiteMinEigenvalue hN0 (fun i l : Fin N =>
        B i l / (Real.sqrt (B i i) * Real.sqrt (B l l))) hH_sym *
      ((∑ i : Fin k.val,
        B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + B k k) ≤
      (∑ i : Fin k.val, ∑ l : Fin k.val,
        y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
      2 * (∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k) + B k k := by
  have hm1n : k.val + 1 ≤ N := k.isLt
  have hHb_sym : IsSymmetricFiniteMatrix (fun i l : Fin (k.val + 1) =>
      (fun i l : Fin N => B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) :=
    fun i l => hH_sym _ _
  have hinterlace := finiteMinEigenvalue_leading_principal_ge N hN0 _
    hH_sym (k.val + 1) (Nat.succ_pos k.val) hm1n hHb_sym
  set z : Fin (k.val + 1) → ℝ := Fin.snoc
    (fun i : Fin k.val =>
      Real.sqrt (B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) * y i)
    (Real.sqrt (B k k)) with hz
  have hray := finiteMinEigenvalue_rayleigh (Nat.succ_pos k.val)
    (fun i l : Fin (k.val + 1) =>
      (fun i l : Fin N => B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) hHb_sym z
  have hlast_eq : (⟨(Fin.last k.val).val, by omega⟩ : Fin N) = k :=
    Fin.ext (by simp)
  have hcancel : ∀ (i l : Fin N) (u v : ℝ),
      (Real.sqrt (B i i) * u) *
        (B i l / (Real.sqrt (B i i) * Real.sqrt (B l l))) *
        (Real.sqrt (B l l) * v) = u * B i l * v := by
    intro i l u v
    have hi := (Real.sqrt_pos.mpr (hBdiag i)).ne'
    have hl := (Real.sqrt_pos.mpr (hBdiag l)).ne'
    field_simp
  have hnorm : ∑ i : Fin (k.val + 1), z i ^ 2 =
      (∑ i : Fin k.val,
        B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + B k k := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, mul_pow, Real.sq_sqrt (hBdiag _).le]
    · rw [hz, Fin.snoc_last, Real.sq_sqrt (hBdiag k).le]
  have hz_nonneg_sq : 0 ≤ ∑ i : Fin (k.val + 1), z i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hquad : ∑ i : Fin (k.val + 1), ∑ l : Fin (k.val + 1),
      z i * ((fun i l : Fin N =>
        B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l =
      (∑ i : Fin k.val, ∑ l : Fin k.val,
        y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
      2 * (∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k) + B k k := by
    rw [sum_sum_castSucc_split k.val]
    have hp1 : ∑ i : Fin k.val, ∑ l : Fin k.val,
        z i.castSucc * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨(i.castSucc).val, by omega⟩ ⟨(l.castSucc).val, by omega⟩) *
          z l.castSucc =
        ∑ i : Fin k.val, ∑ l : Fin k.val,
          y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hcancel _ _ (y i) (y l)
    have hp2 : ∑ i : Fin k.val,
        z i.castSucc * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨(i.castSucc).val, by omega⟩
          ⟨(Fin.last k.val).val, by omega⟩) * z (Fin.last k.val) =
        ∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel ⟨i.val, by omega⟩ k (y i) 1
      simp only [mul_one] at hthis
      exact hthis
    have hp3 : ∑ l : Fin k.val,
        z (Fin.last k.val) * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨(Fin.last k.val).val, by omega⟩
          ⟨(l.castSucc).val, by omega⟩) * z l.castSucc =
        ∑ l : Fin k.val, y l * B ⟨l.val, by omega⟩ k := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel k ⟨l.val, by omega⟩ 1 (y l)
      simp only [one_mul, mul_one] at hthis
      have hfin : Real.sqrt (B k k) *
          (B k ⟨l.val, by omega⟩ /
            (Real.sqrt (B k k) *
             Real.sqrt (B ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) *
          (Real.sqrt (B ⟨l.val, by omega⟩ ⟨l.val, by omega⟩) * y l) =
          y l * B ⟨l.val, by omega⟩ k := by
        rw [hthis, hsymB k ⟨l.val, by omega⟩]
        ring
      exact hfin
    have hp4 : z (Fin.last k.val) * ((fun i l : Fin N =>
        B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨(Fin.last k.val).val, by omega⟩
        ⟨(Fin.last k.val).val, by omega⟩) * z (Fin.last k.val) =
        B k k := by
      rw [hz, Fin.snoc_last, hlast_eq]
      have hthis := hcancel k k 1 1
      simp only [one_mul, mul_one] at hthis
      exact hthis
    rw [hp1, hp2, hp3, hp4]
    ring
  have hmono : finiteMinEigenvalue hN0 _ hH_sym *
      ∑ i : Fin (k.val + 1), z i ^ 2 ≤
      finiteMinEigenvalue (Nat.succ_pos k.val) _ hHb_sym *
      ∑ i : Fin (k.val + 1), z i ^ 2 :=
    mul_le_mul_of_nonneg_right hinterlace hz_nonneg_sq
  calc finiteMinEigenvalue hN0 _ hH_sym *
      ((∑ i : Fin k.val,
        B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + B k k)
      = finiteMinEigenvalue hN0 _ hH_sym *
        ∑ i : Fin (k.val + 1), z i ^ 2 := by rw [hnorm]
    _ ≤ finiteMinEigenvalue (Nat.succ_pos k.val) _ hHb_sym *
        ∑ i : Fin (k.val + 1), z i ^ 2 := hmono
    _ ≤ ∑ i : Fin (k.val + 1), ∑ l : Fin (k.val + 1),
        z i * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l := hray
    _ = (∑ i : Fin k.val, ∑ l : Fin k.val,
          y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k) + B k k := hquad

end NumStability
