import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model

/-!
# NumStability Analysis MatrixNorms SpectralExtrema Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Minimum eigenvalue** of a symmetric real matrix, through the
repository's `finiteHermitianEigenvalues` (Higham §10.1, the `λ_min`
of Theorem 10.7). -/
noncomputable def finiteMinEigenvalue {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)

/-- The minimum eigenvalue is a lower bound for every eigenvalue. -/
theorem finiteMinEigenvalue_le {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : Fin n) :
    finiteMinEigenvalue hn M hM ≤ finiteHermitianEigenvalues M hM a :=
  Finset.inf'_le _ (Finset.mem_univ a)

/-- The minimum eigenvalue is attained. -/
theorem exists_finiteMinEigenvalue_eq {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    ∃ a : Fin n, finiteHermitianEigenvalues M hM a =
      finiteMinEigenvalue hn M hM := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)
  exact ⟨a, ha.symm⟩

/-- **Rayleigh lower bound from `λ_min`** (Higham §10.1, the spectral
inequality behind Theorem 10.7): `λ_min(M) ‖x‖₂² ≤ xᵀMx`. -/
theorem finiteMinEigenvalue_rayleigh {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (x : Fin n → ℝ) :
    finiteMinEigenvalue hn M hM * ∑ i : Fin n, x i ^ 2 ≤
      ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
  have h := finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues
    M hM (finiteMinEigenvalue_le hn M hM) x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_eq_sum_sum] at h
  simpa [finiteVecNorm2Sq] using h

/-- **Maximum eigenvalue** of a symmetric real matrix, through the
repository's `finiteHermitianEigenvalues` (the `λ_max` of the spectral
reading of `‖·‖₂` on Gram matrices). -/
noncomputable def finiteMaxEigenvalue {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)

/-- Every eigenvalue is at most the maximum eigenvalue. -/
theorem le_finiteMaxEigenvalue {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : Fin n) :
    finiteHermitianEigenvalues M hM a ≤ finiteMaxEigenvalue hn M hM :=
  Finset.le_sup' _ (Finset.mem_univ a)

/-- The maximum eigenvalue is attained. -/
theorem exists_finiteMaxEigenvalue_eq {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    ∃ a : Fin n, finiteHermitianEigenvalues M hM a =
      finiteMaxEigenvalue hn M hM := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp hn)) (finiteHermitianEigenvalues M hM)
  exact ⟨a, ha.symm⟩

/-- **Rayleigh upper bound from `λ_max`**: `xᵀMx ≤ λ_max(M) ‖x‖₂²`. -/
theorem finiteMaxEigenvalue_rayleigh {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j ≤
      finiteMaxEigenvalue hn M hM * ∑ i : Fin n, x i ^ 2 := by
  have h := finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le
    M hM (le_finiteMaxEigenvalue hn M hM) x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_eq_sum_sum] at h
  simpa [finiteVecNorm2Sq] using h

/-- **Spectral reading of the operator-2-norm certificate**
(`‖R‖₂ ≤ √λ_max(RᵀR)`, the remaining tail of display (10.7)): the
vector-action certificate holds at the square root of the Gram matrix's
largest eigenvalue. -/
theorem opNorm2Le_sqrt_maxEigenvalue_gram (n : ℕ) (hn : 0 < n)
    (R : Fin n → Fin n → ℝ)
    (hG_sym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l)) :
    opNorm2Le R (Real.sqrt (finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym)) := by
  have hlam0 : 0 ≤ finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym := by
    obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn _ hG_sym
    have hnorm1 := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
    have hq :=
      finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
        (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
    rw [hnorm1, mul_one] at hq
    rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum,
      gram_quadForm_eq_sq_norm]
    exact vecNorm2Sq_nonneg _
  intro x
  have hray := finiteMaxEigenvalue_rayleigh hn
    (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym x
  rw [gram_quadForm_eq_sq_norm] at hray
  have hx2 : vecNorm2 x ^ 2 = ∑ i : Fin n, x i ^ 2 := vecNorm2_sq _
  have hRx2 : vecNorm2 (matMulVec n R x) ^ 2 =
      vecNorm2Sq (matMulVec n R x) := vecNorm2_sq _
  have hboth : vecNorm2 (matMulVec n R x) ^ 2 ≤
      (Real.sqrt (finiteMaxEigenvalue hn
        (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym) *
       vecNorm2 x) ^ 2 := by
    rw [hRx2, mul_pow, Real.sq_sqrt hlam0, hx2]
    exact hray
  nlinarith [vecNorm2_nonneg (matMulVec n R x),
    mul_nonneg (Real.sqrt_nonneg (finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym))
      (vecNorm2_nonneg x), hboth]

/-- **Spectral reading, converse direction**: an operator-2-norm
certificate `c` bounds the Gram matrix's largest eigenvalue by `c²` —
together with the forward direction this is the honest certificate form
of `‖RᵀR‖₂ = ‖R‖₂²`. -/
theorem maxEigenvalue_gram_le_sq_of_opNorm2Le (n : ℕ) (hn : 0 < n)
    (R : Fin n → Fin n → ℝ)
    (hG_sym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l))
    (c : ℝ) (h : opNorm2Le R c) :
    finiteMaxEigenvalue hn
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym ≤ c ^ 2 := by
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn _ hG_sym
  have hnorm1 := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym a
  rw [hnorm1, mul_one] at hq
  set v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l)
      hG_sym).eigenvectorBasis a) with hv
  have hvq : vecNorm2Sq (matMulVec n R v) =
      finiteMaxEigenvalue hn
        (fun i l : Fin n => ∑ p : Fin n, R p i * R p l) hG_sym := by
    rw [← gram_quadForm_eq_sq_norm, ← finiteQuadraticForm_eq_sum_sum,
      hq, ha]
  have hvn : vecNorm2 v = 1 := by
    unfold vecNorm2
    rw [show vecNorm2Sq v = 1 from hnorm1]
    exact Real.sqrt_one
  have hb := h v
  rw [hvn, mul_one] at hb
  have hRv0 : 0 ≤ vecNorm2 (matMulVec n R v) := vecNorm2_nonneg _
  have hsq : vecNorm2 (matMulVec n R v) ^ 2 =
      vecNorm2Sq (matMulVec n R v) := vecNorm2_sq _
  nlinarith [hb, hRv0, hvq, hsq]

/-- Every diagonal entry is a Rayleigh quotient, so bounds `λ_max`
    from below (van der Sluis engine, `λ_max(M) ≥ m_ii`). -/
lemma finiteMaxEigenvalue_ge_diag {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hSym : IsSymmetricFiniteMatrix M)
    (i : Fin n) :
    M i i ≤ finiteMaxEigenvalue hn M hSym := by
  set e : Fin n → ℝ := fun k => if k = i then 1 else 0 with he
  have hray := finiteMaxEigenvalue_rayleigh hn M hSym e
  have hquad : ∑ k : Fin n, ∑ l : Fin n, e k * M k l * e l =
      M i i := by
    simp [he, Finset.sum_ite_eq']
  have hnorm : ∑ k : Fin n, e k ^ 2 = 1 := by
    simp [he, Finset.sum_ite_eq']
  rw [hquad, hnorm, mul_one] at hray
  exact hray

/-- **Diagonal congruence bounds the smallest eigenvalue from below**
    (van der Sluis engine): if `N = E M E` with diagonal `E = diag(e)`
    and `m ≤ e_i²` throughout, then `λ_min(N) ≥ m·λ_min(M)` — evaluate
    at `N`'s bottom eigenvector and pass through the congruence. -/
lemma diag_congruence_minEigenvalue_ge {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hSymM : IsSymmetricFiniteMatrix M)
    (e : Fin n → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hme : ∀ i : Fin n, m ≤ e i ^ 2)
    (hSymN : IsSymmetricFiniteMatrix
      (fun i j : Fin n => e i * M i j * e j))
    (hminM : 0 ≤ finiteMinEigenvalue hn M hSymM) :
    m * finiteMinEigenvalue hn M hSymM ≤
      finiteMinEigenvalue hn
        (fun i j : Fin n => e i * M i j * e j) hSymN := by
  -- bottom eigenvector of N
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hn _ hSymN
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin n => e i * M i j * e j) hSymN a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin n => e i * M i j * e j) hSymN a
  rw [hnorm, mul_one] at hq
  set v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin n => e i * M i j * e j)
      hSymN).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hqv : ∑ i : Fin n, ∑ j : Fin n,
      v i * (e i * M i j * e j) * v j =
      finiteMinEigenvalue hn
        (fun i j : Fin n => e i * M i j * e j) hSymN := by
    rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
  -- pass through the congruence: quadForm N v = quadForm M (e·v)
  have hcong : ∑ i : Fin n, ∑ j : Fin n,
      v i * (e i * M i j * e j) * v j =
      ∑ i : Fin n, ∑ j : Fin n,
        (e i * v i) * M i j * (e j * v j) := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hrayM := finiteMinEigenvalue_rayleigh hn M hSymM
    (fun i => e i * v i)
  have hnorm2 : m * (∑ i : Fin n, v i ^ 2) ≤
      ∑ i : Fin n, (e i * v i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hme i
    have h2 := sq_nonneg (v i)
    calc m * v i ^ 2 ≤ e i ^ 2 * v i ^ 2 :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (e i * v i) ^ 2 := by ring
  rw [hvsq, mul_one] at hnorm2
  calc m * finiteMinEigenvalue hn M hSymM
      ≤ (∑ i : Fin n, (e i * v i) ^ 2) *
          finiteMinEigenvalue hn M hSymM := by
        exact mul_le_mul_of_nonneg_right hnorm2 hminM
    _ = finiteMinEigenvalue hn M hSymM *
          ∑ i : Fin n, (e i * v i) ^ 2 := mul_comm _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          (e i * v i) * M i j * (e j * v j) := hrayM
    _ = finiteMinEigenvalue hn
          (fun i j : Fin n => e i * M i j * e j) hSymN := by
        rw [← hcong, hqv]

/-- **Max-eigenvalue monotonicity from quadratic-form ordering** (Higham
    §10.4, the Loewner→operator-norm step of the (10.29) stage
    monotonicity): if `yᵀAy ≤ yᵀBy` for all `y` (symmetric `A, B`), then
    `λ_max(A) ≤ λ_max(B)`.  Evaluate at `A`'s top unit eigenvector: it
    realizes `λ_max(A)`, and the `B`-Rayleigh bound caps it by
    `λ_max(B)`. -/
theorem finiteMaxEigenvalue_mono_of_quadForm_le {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (hA : IsSymmetricFiniteMatrix A) (hB : IsSymmetricFiniteMatrix B)
    (hle : ∀ y : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin n, y i * A i j * y j) ≤
       ∑ i : Fin n, ∑ j : Fin n, y i * B i j * y j) :
    finiteMaxEigenvalue hn A hA ≤ finiteMaxEigenvalue hn B hB := by
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn A hA
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one A hA a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      A hA a
  rw [hnorm, mul_one] at hq
  set v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian A hA).eigenvectorBasis a)
    with hv
  have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
    have := hnorm; unfold finiteVecNorm2Sq at this; exact this
  have hvA : (∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j) =
      finiteMaxEigenvalue hn A hA := by
    rw [← finiteQuadraticForm_eq_sum_sum, hq, ha]
  have hvB := finiteMaxEigenvalue_rayleigh hn B hB v
  rw [hvsq, mul_one] at hvB
  calc finiteMaxEigenvalue hn A hA
      = ∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j := hvA.symm
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, v i * B i j * v j := hle v
    _ ≤ finiteMaxEigenvalue hn B hB := hvB

/-- **Trailing-block eigenvalue interlacing** (Higham §10.4, the
    `‖Q₂₂‖₂ ≤ ‖Q‖₂` half of the (10.29) Schur monotonicity): the maximum
    eigenvalue of the trailing `m × m` principal submatrix (drop row/column
    0) is at most that of the full `(m+1) × (m+1)` matrix — evaluate the
    full max-Rayleigh bound at the eigenvector padded with a leading zero
    (`Fin.cons 0 v`). -/
theorem finiteMaxEigenvalue_trailing_principal_le (m : ℕ) (hm : 0 < m)
    (M : Fin (m + 1) → Fin (m + 1) → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (hMsub_sym : IsSymmetricFiniteMatrix
      (fun i j : Fin m => M i.succ j.succ)) :
    finiteMaxEigenvalue hm
        (fun i j : Fin m => M i.succ j.succ) hMsub_sym ≤
      finiteMaxEigenvalue (Nat.succ_pos m) M hM := by
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hm
    (fun i j : Fin m => M i.succ j.succ) hMsub_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin m => M i.succ j.succ) hMsub_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin m => M i.succ j.succ) hMsub_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin m → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin m => M i.succ j.succ) hMsub_sym).eigenvectorBasis a)
    with hv
  have hvsq : ∑ i : Fin m, v i ^ 2 = 1 := by
    have := hnorm; unfold finiteVecNorm2Sq at this; exact this
  set w : Fin (m + 1) → ℝ := Fin.cons 0 v with hw
  have hwsq : ∑ i : Fin (m + 1), w i ^ 2 = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [hw, Fin.cons_zero, Fin.cons_succ]
    rw [hvsq]; ring
  have hray := finiteMaxEigenvalue_rayleigh (Nat.succ_pos m) M hM w
  rw [hwsq, mul_one] at hray
  have hquad : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), w i * M i j * w j =
      finiteMaxEigenvalue hm
        (fun i j : Fin m => M i.succ j.succ) hMsub_sym := by
    rw [Fin.sum_univ_succ]
    have hzero_row : (∑ j : Fin (m + 1), w 0 * M 0 j * w j) = 0 := by
      simp only [hw, Fin.cons_zero, zero_mul, Finset.sum_const_zero]
    rw [hzero_row, zero_add]
    have hinner : ∀ i : Fin m,
        (∑ j : Fin (m + 1), w i.succ * M i.succ j * w j) =
        ∑ j : Fin m, v i * M i.succ j.succ * v j := by
      intro i
      rw [Fin.sum_univ_succ]
      simp only [hw, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add]
    rw [Finset.sum_congr rfl fun i _ => hinner i]
    rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
  rw [hquad] at hray
  exact hray

/-- **Operator-norm stage monotonicity `λ_max(Q̂) ≤ λ_max(Q₂₂)`**
    (Higham §10.4, the (10.29) stage step packaged at the eigenvalue
    level).  Given only the per-stage quadratic-form inequality
    `(Ŝy)ᵀĤ⁻¹(Ŝy) ≤ (S·(0,y))ᵀH⁻¹(S·(0,y))` for all `y`, the stage Gram
    `Q̂ = ŜᵀĤ⁻¹Ŝ` has maximum eigenvalue at most that of the trailing
    block `Q₂₂` of the parent Gram `Q = SᵀH⁻¹S`.  Combines
    `quadForm_gram_conj` (both sides), `trailing_block_quadForm`, and
    `finiteMaxEigenvalue_mono_of_quadForm_le`. -/
theorem stage_maxEigenvalue_le {m : ℕ} (hm : 0 < m)
    (S Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Shat Hhatinv : Fin m → Fin m → ℝ)
    (hHinvSym : ∀ i j : Fin (m + 1), Hinv i j = Hinv j i)
    (hHhatinvSym : ∀ i j : Fin m, Hhatinv i j = Hhatinv j i)
    (hstage : ∀ y : Fin m → ℝ,
      (∑ p : Fin m, matMulVec m Shat y p *
          matMulVec m Hhatinv (matMulVec m Shat y) p) ≤
        ∑ p : Fin (m + 1),
          matMulVec (m + 1) S (Fin.cons 0 y) p *
          matMulVec (m + 1) Hinv (matMulVec (m + 1) S (Fin.cons 0 y)) p) :
    finiteMaxEigenvalue hm
        (matMul m (matMul m (fun a b => Shat b a) Hhatinv) Shat)
        (gram_conj_isSymm Hhatinv Shat hHhatinvSym) ≤
      finiteMaxEigenvalue hm
        (fun i j : Fin m =>
          matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S
            i.succ j.succ)
        (fun i j => gram_conj_isSymm Hinv S hHinvSym i.succ j.succ) := by
  refine finiteMaxEigenvalue_mono_of_quadForm_le hm _ _ _ _ ?_
  intro y
  -- bridge ∑∑ y·A·y = ∑ y·(A y) for both matrices
  have hbridge : ∀ (A : Fin m → Fin m → ℝ),
      (∑ i : Fin m, ∑ j : Fin m, y i * A i j * y j) =
      ∑ i : Fin m, y i * matMulVec m A y i := by
    intro A
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold matMulVec
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- LHS = (Ŝy)ᵀĤ⁻¹(Ŝy)
  rw [hbridge, quadForm_gram_conj Hhatinv Shat y]
  -- RHS: trailing block → padded → (S(0,y))ᵀH⁻¹(S(0,y))
  have hRHS : (∑ i : Fin m, ∑ j : Fin m, y i *
        (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
          i.succ j.succ * y j) =
      ∑ p : Fin (m + 1),
        matMulVec (m + 1) S (Fin.cons 0 y) p *
        matMulVec (m + 1) Hinv (matMulVec (m + 1) S (Fin.cons 0 y)) p := by
    rw [← trailing_block_quadForm
      (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S) y]
    rw [show (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (Fin.cons (0 : ℝ) y : Fin (m + 1) → ℝ) i *
        (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S) i j *
        (Fin.cons (0 : ℝ) y : Fin (m + 1) → ℝ) j) =
        ∑ i : Fin (m + 1),
          (Fin.cons (0 : ℝ) y : Fin (m + 1) → ℝ) i *
          matMulVec (m + 1)
            (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
            (Fin.cons (0 : ℝ) y) i from by
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold matMulVec
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring]
    exact quadForm_gram_conj Hinv S (Fin.cons 0 y)
  rw [hRHS]
  exact hstage y

end NumStability
