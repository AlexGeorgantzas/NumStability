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
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
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

/-!
# Chapter10 Theorem07 FailureVacuity Endpoints

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.7**, success-threshold consequence for the scaled Cholesky
analysis. -/
theorem higham10_7_success_condition (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (hD_pos : ∀ i : Fin n, 0 < D i)
    (hDHD : ∀ i j : Fin n, A i j = D i * H i j * D j)
    (lam_min : ℝ)
    (hH_diag : ∀ i : Fin n, H i i = 1)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    (hlam_min : lam_min > ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))
    (hLam_bound : ∀ x : Fin n → ℝ,
      (∃ i, x i ≠ 0) →
      lam_min * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) :
    0 < lam_min :=
  cholesky_success_condition n fp A D H hD_pos hDHD lam_min hH_diag
    hn1 hγ_lt hlam_min hLam_bound

/-- **Theorem 10.7**, failure-threshold consequence. -/
theorem higham10_7_failure_condition (n : ℕ) (fp : FPModel)
    (lam_min : ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    (hLam_neg : lam_min < -(↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))) :
    lam_min < 0 :=
  cholesky_failure_condition n fp lam_min hn1 hγ_lt hLam_neg

/-- **Theorem 10.7**, failure as genuine non-factorizability.

    Strengthens `higham10_7_failure_condition` from the sign consequence
    `lam_min < 0` to the actual failure conclusion: when `H` has a
    Rayleigh upper witness `lam` for its minimum eigenvalue below `-t`
    (with `t` the scaled backward-error quadratic-form bound), the scaled
    perturbed matrix `H + E` has a strictly negative curvature direction and
    therefore admits no Cholesky factorization — the algorithm fails. -/
theorem higham10_7_failure_no_factorization (n : ℕ)
    (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hlam_dir : ∃ x : Fin n → ℝ, (∃ i, x i ≠ 0) ∧
        (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) ≤ lam * ∑ i : Fin n, x i ^ 2)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : lam < -t) :
    ¬ ∃ R : Fin n → Fin n → ℝ,
        CholeskyFactSpec n (fun i j => H i j + E i j) R := by
  obtain ⟨x, hx, hxneg⟩ :=
    quadForm_add_neg_of_perturbation n H E lam t hlam_dir hE hlt
  exact no_choleskyFactSpec_of_neg_quadForm n (fun i j => H i j + E i j) x hxneg

/-- **Equation (10.7), normwise backward error in certificate form**
(Higham §10.1, p. 198): from the componentwise Theorem 10.3 certificate
and an operator-norm certificate `‖R̂‖₂ ≤ c`, the residual
`ΔA = R̂ᵀR̂ − A` satisfies `‖ΔA‖₂ ≤ ε n c²`.  The source display continues
`≤ γ_{3n+1} n (1 − nγ_{n+1})^{-1} ‖A‖₂` by converting `c²` to `‖A‖₂`
through the spectral identity `‖R̂ᵀR̂‖₂ = ‖R̂‖₂²`, which remains open. -/
theorem higham10_7_normwise_backward_error (n : ℕ)
    (A R : Fin n → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R ε)
    (c : ℝ) (hc : 0 ≤ c) (hR : opNorm2Le R c) :
    opNorm2Le
      (fun i j => (∑ k : Fin n, R k i * R k j) - A i j)
      (ε * ((n : ℝ) * c ^ 2)) := by
  apply opNorm2Le_of_abs_le n _
    (fun i j => ε * matMul n (fun i' j' => |R j' i'|)
      (fun i' j' => |R i' j'|) i j)
  · intro i j
    have hcert := hChol.backward_bound i j
    have hmm : matMul n (fun i' j' => |R j' i'|)
        (fun i' j' => |R i' j'|) i j =
        ∑ k : Fin n, |R k i| * |R k j| := rfl
    rw [hmm]
    exact hcert
  · exact opNorm2Le_smul n _ _ ε hε
      (higham10_7_absRT_absR_opNorm2Le n R c hc hR)

/-- **Theorem 10.7, spectral failure form** (Higham §10.1): if some
eigenvalue of the symmetric scaled matrix `H` is at most `lam < −t`, then
the perturbed scaled matrix `H + E` has a strictly negative curvature
direction (the corresponding eigenvector) and admits no Cholesky
factorization: the algorithm must fail. -/
theorem higham10_7_failure_no_factorization_spectral (n : ℕ)
    (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (a : Fin n)
    (hlam_le : finiteHermitianEigenvalues H hH_sym a ≤ lam)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : lam < -t) :
    ¬ ∃ R : Fin n → Fin n → ℝ,
        CholeskyFactSpec n (fun i j => H i j + E i j) R := by
  refine higham10_7_failure_no_factorization n H E lam t ?_ hE hlt
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one H hH_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      H hH_sym a
  rw [hnorm, mul_one] at hq
  refine ⟨⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
      hH_sym).eigenvectorBasis a), ?_, ?_⟩
  · by_contra hall
    push_neg at hall
    have hzero : finiteVecNorm2Sq
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) = 0 := by
      unfold finiteVecNorm2Sq
      exact Finset.sum_eq_zero fun i _ => by rw [hall i]; ring
    rw [hzero] at hnorm
    exact zero_ne_one hnorm
  · have hqs : ∑ i : Fin n, ∑ j : Fin n,
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) i * H i j *
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) j =
        finiteHermitianEigenvalues H hH_sym a := by
      rw [← finiteQuadraticForm_eq_sum_sum]
      exact hq
    rw [hqs]
    have hsum : ∑ i : Fin n,
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
          hH_sym).eigenvectorBasis a)) i ^ 2 = 1 := by
      have := hnorm
      unfold finiteVecNorm2Sq at this
      exact this
    rw [hsum, mul_one]
    exact hlam_le

/-- **Theorem 10.7 failure threshold, `λ_min` form** (Higham §10.1): if
`λ_min(H) < −t`, the perturbed scaled matrix `H + E` admits no Cholesky
factorization. -/
theorem higham10_7_failure_no_factorization_min_eig (n : ℕ) (hn : 0 < n)
    (H E : Fin n → Fin n → ℝ) (t : ℝ)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : finiteMinEigenvalue hn H hH_sym < -t) :
    ¬ ∃ R : Fin n → Fin n → ℝ,
        CholeskyFactSpec n (fun i j => H i j + E i j) R := by
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hn H hH_sym
  exact higham10_7_failure_no_factorization_spectral n H E
    (finiteMinEigenvalue hn H hH_sym) t hH_sym a (le_of_eq ha) hE hlt

/-- **Display (10.7) closed by self-bounding** (the recorded open tail):
    from the componentwise certificate and the spectral reading of the
    Gram norm, the residual obeys the source display
    `‖ΔA‖₂ ≤ εn/(1−εn) ‖A‖₂` with no free factor certificate: taking
    `c² = λ_max(R̂ᵀR̂)` and evaluating the Gram quadratic form at the top
    eigenvector gives `λ_max ≤ ‖A‖₂ + εn λ_max`, so `λ_max` self-bounds
    by `‖A‖₂/(1−εn)`. -/
theorem higham10_7_normwise_backward_error_selfbound (n : ℕ)
    (hn : 0 < n) (A R : Fin n → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R ε)
    (hG_sym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => ∑ p : Fin n, R p i * R p l))
    (cA : ℝ) (hcA : opNorm2Le A cA)
    (hsmall : ε * (n : ℝ) < 1) :
    opNorm2Le
      (fun i j => (∑ k : Fin n, R k i * R k j) - A i j)
      (ε * (n : ℝ) * cA / (1 - ε * (n : ℝ))) := by
  set G : Fin n → Fin n → ℝ :=
    fun i l => ∑ p : Fin n, R p i * R p l with hG
  set lam : ℝ := finiteMaxEigenvalue hn G hG_sym with hlam
  have h1εn : (0:ℝ) < 1 - ε * (n : ℝ) := by linarith
  -- λ_max ≥ 0 via the top eigenvector and the Gram form
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn G hG_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    G hG_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      G hG_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin n → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian G
      hG_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hqv : ∑ i : Fin n, ∑ j : Fin n, v i * G i j * v j = lam := by
    rw [hlam, ← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
  have hlam0 : 0 ≤ lam := by
    rw [← hqv, hG]
    rw [gram_quadForm_eq_sq_norm]
    exact vecNorm2Sq_nonneg _
  -- residual certificate at c = √λ_max
  have hR := opNorm2Le_sqrt_maxEigenvalue_gram n hn R hG_sym
  have hΔ := higham10_7_normwise_backward_error n A R ε hε hChol
    (Real.sqrt lam) (Real.sqrt_nonneg _) hR
  rw [Real.sq_sqrt hlam0] at hΔ
  -- self-bounding: λ_max ≤ cA + εn·λ_max
  have hsplit : ∑ i : Fin n, ∑ j : Fin n, v i * G i j * v j =
      (∑ i : Fin n, ∑ j : Fin n, v i * A i j * v j) +
      ∑ i : Fin n, ∑ j : Fin n,
        v i * (G i j - A i j) * v j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hA_abs := quadForm_abs_le_of_opNorm2Le n A cA hcA v
  have hΔ_abs := quadForm_abs_le_of_opNorm2Le n
    (fun i j => G i j - A i j) (ε * ((n : ℝ) * lam)) hΔ v
  rw [hvsq, mul_one] at hA_abs hΔ_abs
  have hlam_le : lam ≤ cA + ε * (n : ℝ) * lam := by
    have h1 := (abs_le.mp hA_abs).2
    have h2 := (abs_le.mp hΔ_abs).2
    have := hqv
    rw [hsplit] at this
    nlinarith
  have hlam_bound : lam ≤ cA / (1 - ε * (n : ℝ)) := by
    rw [le_div_iff₀ h1εn]
    nlinarith
  -- upgrade the certificate constant
  intro x
  calc vecNorm2 (matMulVec n
        (fun i j => (∑ k : Fin n, R k i * R k j) - A i j) x)
      ≤ ε * ((n : ℝ) * lam) * vecNorm2 x := hΔ x
    _ ≤ ε * (n : ℝ) * cA / (1 - ε * (n : ℝ)) * vecNorm2 x := by
        refine mul_le_mul_of_nonneg_right ?_ (vecNorm2_nonneg x)
        have hεn : (0:ℝ) ≤ ε * (n : ℝ) :=
          mul_nonneg hε (Nat.cast_nonneg n)
        rw [le_div_iff₀ h1εn] at hlam_bound
        rw [le_div_iff₀ h1εn]
        nlinarith [hεn, hlam_bound]

end NumStability
