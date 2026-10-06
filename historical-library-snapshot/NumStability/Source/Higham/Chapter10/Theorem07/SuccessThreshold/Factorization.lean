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
import NumStability.Analysis.MatrixNorms.SpectralExtrema.PrincipalSubmatrices.Bounds
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.Endpoints
import NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic
import NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic
import NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SuccessfulRun.StageBounds

/-!
# Factorization

Canonical destination for 5 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.7**, success as genuine factorization existence.

    Strengthens `higham10_7_success_condition` from the sign consequence
    `0 < lam_min` to the actual conclusion of Theorem 10.7: when the scaled
    matrix `H` has Rayleigh lower bound `lam` exceeding the scaled backward-error
    quadratic-form bound `t`, the perturbed scaled matrix `D (H + E) D` is SPD
    and has a genuine Cholesky factorization — Cholesky succeeds. The
    "min-eigenvalue → PD" step is now proved (`quadForm_add_pos_of_perturbation`,
    `isSymPosDef_diagCongr`), not assumed. -/
theorem higham10_7_success_factorization (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : ∀ i j, H i j = H j i)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam : ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        lam * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R :=
  cholesky_succeeds_of_scaled_perturbation n D H E lam t hD_pos hH_sym hE_sym
    hlam hE hlt

/-- **Theorem 10.7, spectral success form** (Higham §10.1): if the minimum
eigenvalue of the symmetric scaled matrix `H` — stated through the
repository's `finiteHermitianEigenvalues` — exceeds the scaled
backward-error quadratic-form bound `t`, then the perturbed scaled matrix
`D (H + E) D` has a genuine Cholesky factorization: the algorithm
succeeds.  This replaces the Rayleigh-quotient hypothesis of
`higham10_7_success_factorization` with the source's spectral `λ_min`
framing. -/
theorem higham10_7_success_factorization_spectral (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam_le : ∀ a : Fin n, lam ≤ finiteHermitianEigenvalues H hH_sym a)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R := by
  refine higham10_7_success_factorization n D H E lam t hD_pos
    (fun i j => hH_sym i j) hE_sym ?_ hE hlt
  intro x _hx
  have h := finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues
    H hH_sym hlam_le x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_eq_sum_sum] at h
  simpa [finiteVecNorm2Sq] using h

/-- **Theorem 10.7 success threshold, `λ_min` form** (Higham §10.1): if
`λ_min(H) > t`, the perturbed scaled matrix `D (H + E) D` has a genuine
Cholesky factorization. -/
theorem higham10_7_success_factorization_min_eig (n : ℕ) (hn : 0 < n)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE_sym : ∀ i j, E i j = E j i)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < finiteMinEigenvalue hn H hH_sym) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R :=
  higham10_7_success_factorization_spectral n D H E
    (finiteMinEigenvalue hn H hH_sym) t hD_pos hH_sym hE_sym
    (finiteMinEigenvalue_le hn H hH_sym) hE hlt

/-- **Theorem 10.7 (Demmel), success direction for the concrete
Algorithm 10.2** (Higham p. 200): if the minimum eigenvalue of the scaled
matrix `H = D⁻¹AD⁻¹` (`D = diag(√a_ii)`) exceeds
`(2n+3)·γ_{n+1}/(1−γ_{n+1})`, the concrete floating-point Cholesky
algorithm runs to completion: every rounded pivot is positive.  Per-stage
Rayleigh floors come from `λ_min(H)` by interlacing on the bordered
leading blocks and the substitution `z = (√a_i·y_i, √a_jj)`.  The
threshold constant is coarser than the source `n·γ_{n+1}/(1−γ_{n+1})`;
sharpening is open. -/
theorem higham10_7_fl_cholesky_success (fp : FPModel) (n : ℕ)
    (hn0 : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin n =>
      A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hthresh : (2 * (n : ℝ) + 3) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) <
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  apply fl_cholesky_pivots_pos fp A hsym hAdiag hn1 hγ1
    (finiteMinEigenvalue hn0 _ hH_sym) _ hthresh
  intro j y
  have hm1n : j.val + 1 ≤ n := j.isLt
  have hHb_sym : IsSymmetricFiniteMatrix (fun i l : Fin (j.val + 1) =>
      (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) :=
    fun i l => hH_sym _ _
  have hinterlace := finiteMinEigenvalue_leading_principal_ge n hn0 _
    hH_sym (j.val + 1) (Nat.succ_pos j.val) hm1n hHb_sym
  set z : Fin (j.val + 1) → ℝ := Fin.snoc
    (fun i : Fin j.val =>
      Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) * y i)
    (Real.sqrt (A j j)) with hz
  have hray := finiteMinEigenvalue_rayleigh (Nat.succ_pos j.val)
    (fun i l : Fin (j.val + 1) =>
      (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) hHb_sym z
  have hlast_eq : (⟨(Fin.last j.val).val, by omega⟩ : Fin n) = j :=
    Fin.ext (by simp)
  have hcancel : ∀ (i l : Fin n) (u v : ℝ),
      (Real.sqrt (A i i) * u) *
        (A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) *
        (Real.sqrt (A l l) * v) = u * A i l * v := by
    intro i l u v
    have hi := (Real.sqrt_pos.mpr (hAdiag i)).ne'
    have hl := (Real.sqrt_pos.mpr (hAdiag l)).ne'
    field_simp
  have hnorm : ∑ i : Fin (j.val + 1), z i ^ 2 =
      (∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, mul_pow, Real.sq_sqrt (hAdiag _).le]
    · rw [hz, Fin.snoc_last, Real.sq_sqrt (hAdiag j).le]
  have hz_nonneg_sq : 0 ≤ ∑ i : Fin (j.val + 1), z i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hquad : ∑ i : Fin (j.val + 1), ∑ l : Fin (j.val + 1),
      z i * ((fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l =
      (∑ i : Fin j.val, ∑ l : Fin j.val,
        y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
      2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j := by
    rw [sum_sum_castSucc_split j.val]
    have hp1 : ∑ i : Fin j.val, ∑ l : Fin j.val,
        z i.castSucc * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(i.castSucc).val, by omega⟩ ⟨(l.castSucc).val, by omega⟩) *
          z l.castSucc =
        ∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hcancel _ _ (y i) (y l)
    have hp2 : ∑ i : Fin j.val,
        z i.castSucc * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(i.castSucc).val, by omega⟩
          ⟨(Fin.last j.val).val, by omega⟩) * z (Fin.last j.val) =
        ∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel ⟨i.val, by omega⟩ j (y i) 1
      simp only [mul_one] at hthis
      exact hthis
    have hp3 : ∑ l : Fin j.val,
        z (Fin.last j.val) * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(Fin.last j.val).val, by omega⟩
          ⟨(l.castSucc).val, by omega⟩) * z l.castSucc =
        ∑ l : Fin j.val, y l * A ⟨l.val, by omega⟩ j := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel j ⟨l.val, by omega⟩ 1 (y l)
      simp only [one_mul, mul_one] at hthis
      have hfin : Real.sqrt (A j j) *
          (A j ⟨l.val, by omega⟩ /
            (Real.sqrt (A j j) *
             Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) *
          (Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩) * y l) =
          y l * A ⟨l.val, by omega⟩ j := by
        rw [hthis, hsym j ⟨l.val, by omega⟩]
        ring
      exact hfin
    have hp4 : z (Fin.last j.val) * ((fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨(Fin.last j.val).val, by omega⟩
        ⟨(Fin.last j.val).val, by omega⟩) * z (Fin.last j.val) =
        A j j := by
      rw [hz, Fin.snoc_last, hlast_eq]
      have hthis := hcancel j j 1 1
      simp only [one_mul, mul_one] at hthis
      exact hthis
    rw [hp1, hp2, hp3, hp4]
    ring
  have hmono : finiteMinEigenvalue hn0 _ hH_sym *
      ∑ i : Fin (j.val + 1), z i ^ 2 ≤
      finiteMinEigenvalue (Nat.succ_pos j.val) _ hHb_sym *
      ∑ i : Fin (j.val + 1), z i ^ 2 :=
    mul_le_mul_of_nonneg_right hinterlace hz_nonneg_sq
  calc finiteMinEigenvalue hn0 _ hH_sym *
      ((∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j)
      = finiteMinEigenvalue hn0 _ hH_sym *
        ∑ i : Fin (j.val + 1), z i ^ 2 := by rw [hnorm]
    _ ≤ finiteMinEigenvalue (Nat.succ_pos j.val) _ hHb_sym *
        ∑ i : Fin (j.val + 1), z i ^ 2 := hmono
    _ ≤ ∑ i : Fin (j.val + 1), ∑ l : Fin (j.val + 1),
        z i * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l := hray
    _ = (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j := hquad

/-- **Theorem 10.7 success direction at the source-shaped threshold,
    hypothesis-light** (Higham §10.1, p. 200): the `r = n` instance of
    the display-(10.21) assembly — if
    `λ_min(H) > n·γ_{n+1}/(1−γ_{n+1}) + 2γ_{n+1}` for the scaled matrix
    `H = D⁻¹AD⁻¹` (and `λ_min(H)` dominates twice the mass constant),
    the concrete Algorithm 10.2 run completes: every rounded pivot is
    positive.  This replaces the coarser `(2n+3)`-constant of
    `higham10_7_fl_cholesky_success` and assumes no run-level
    certificates, unlike `fl_cholesky_pivots_pos_sharp_certified`. -/
theorem higham10_7_fl_cholesky_success_sharp (fp : FPModel) (n : ℕ)
    (hn0 : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin n =>
      A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hlam2ε : 2 * ((n : ℝ) *
        (gamma fp (n + 1) / (1 - gamma fp (n + 1)))) ≤
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym)
    (hthresh : (n : ℝ) * (gamma fp (n + 1) / (1 - gamma fp (n + 1))) +
        2 * gamma fp (n + 1) <
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  intro j
  exact higham10_21_fl_cholesky_success fp A hsym hAdiag hn1 hγ1
    n hn0 le_rfl hH_sym hlam2ε hthresh j j.isLt

end NumStability
