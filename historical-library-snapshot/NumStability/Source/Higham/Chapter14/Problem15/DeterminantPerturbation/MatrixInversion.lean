import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Problem13.GEJBound.MatrixInversion

/-!
# Chapter14 Problem15 DeterminantPerturbation MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.15, Appendix A support:
    after the singular-value argument has produced scalar factors
    `1 + theta_i` with `|theta_i| <= eps`, Lemma 3.1 gives the determinant
    perturbation product radius `n*eps/(1-n*eps)`.

The guard is stated as `n*eps < 1`; it is the positivity condition needed for
the displayed denominator in the printed bound. -/
theorem higham14_problem14_15_theta_product_bound {n : ℕ} (hnpos : 0 < n)
    {eps : ℝ} (heps0 : 0 ≤ eps)
    (hsmall : (n : ℝ) * eps < (1 : ℝ)) (theta : Fin n → ℝ)
    (htheta : ∀ i : Fin n, |theta i| ≤ eps) :
    |(∏ i : Fin n, (1 + theta i)) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) :=
  prod_one_add_delta_abs_sub_one_le_gamma_radius n hnpos heps0 hsmall theta htheta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    a supplied all-index singular-value perturbation certificate reduces the
    absolute determinant relative-change bound to the scalar theta-product
    bound.  The still-open source work is to derive `htheta_sv` from the
    matrix perturbation hypotheses. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_singularValue_theta
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (theta : Fin n → ℝ)
    (hdetA_pos : 0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|)
    (htheta_sv : ∀ i : Fin n,
      complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i =
        complexMatrixSingularValue (realRectToCMatrix A) i * (1 + theta i))
    (htheta : ∀ i : Fin n, |theta i| ≤ eps) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ)| /
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  let B : Fin n → Fin n → ℝ := fun r c => A r c + Delta r c
  let sigmaA : Fin n → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix A) i
  have hdetB_prod :
      |Matrix.det (B : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, sigmaA i * (1 + theta i) := by
    rw [higham14_problem14_13_abs_det_eq_prod_complex_singularValue B]
    apply Finset.prod_congr rfl
    intro i _
    simpa [B, sigmaA] using htheta_sv i
  have hdetA_prod :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, sigmaA i := by
    simpa [sigmaA] using
      higham14_problem14_13_abs_det_eq_prod_complex_singularValue A
  have hprod_ne : (∏ i : Fin n, sigmaA i) ≠ 0 := by
    rw [← hdetA_prod]
    exact ne_of_gt hdetA_pos
  have hrel_eq :
      |Matrix.det (B : Matrix (Fin n) (Fin n) ℝ)| /
          |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| - 1 =
        (∏ i : Fin n, (1 + theta i)) - 1 := by
    rw [hdetB_prod, hdetA_prod, Finset.prod_mul_distrib]
    field_simp [hprod_ne]
  rw [show (fun r c => A r c + Delta r c) = B by rfl]
  rw [hrel_eq]
  exact higham14_problem14_15_theta_product_bound hnpos heps0 hsmall theta htheta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed relative determinant-change form, obtained from the absolute-value
    determinant bridge when both determinants are positive. -/
theorem higham14_problem14_15_det_add_rel_le_of_singularValue_theta_of_det_pos
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (theta : Fin n → ℝ)
    (hdetA_pos : 0 < Matrix.det (A : Matrix (Fin n) (Fin n) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ))
    (htheta_sv : ∀ i : Fin n,
      complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i =
        complexMatrixSingularValue (realRectToCMatrix A) i * (1 + theta i))
    (htheta : ∀ i : Fin n, |theta i| ≤ eps) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ) /
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  have hAbs :=
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_theta
      hnpos A Delta heps0 hsmall theta (abs_pos.mpr hdetA_pos.ne')
      htheta_sv htheta
  simpa [abs_of_pos hdetA_pos, abs_of_pos hdetB_pos] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    an all-index absolute singular-value perturbation bound, scaled by a
    positive lower bound for the singular values of `A`, supplies the
    determinant relative-change estimate.

This is a dependency bridge toward the source theorem.  It does not prove the
Weyl/Mirsky all-index singular-value perturbation inequality; that remains the
missing spectral input. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_singularValue_abs_sub_bound
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps delta lower : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (hlower_pos : 0 < lower)
    (hlower : ∀ i : Fin n,
      lower ≤ complexMatrixSingularValue (realRectToCMatrix A) i)
    (habs : ∀ i : Fin n,
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ delta)
    (hscale : delta ≤ eps * lower)
    (hdetA_pos : 0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ)| /
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  have hbase_pos :
      ∀ i : Fin n,
        0 < complexMatrixSingularValue (realRectToCMatrix A) i := by
    intro i
    exact lt_of_lt_of_le hlower_pos (hlower i)
  have hrel :
      ∀ i : Fin n,
        |complexMatrixSingularValue
            (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
          complexMatrixSingularValue (realRectToCMatrix A) i| ≤
          eps * complexMatrixSingularValue (realRectToCMatrix A) i := by
    intro i
    calc
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ delta :=
          habs i
      _ ≤ eps * lower := hscale
      _ ≤ eps * complexMatrixSingularValue (realRectToCMatrix A) i :=
          mul_le_mul_of_nonneg_left (hlower i) heps0
  obtain ⟨theta, htheta_sv, htheta_bound⟩ :=
    exists_relative_theta_of_abs_sub_le_mul_pos
      (fun i : Fin n => complexMatrixSingularValue (realRectToCMatrix A) i)
      (fun i : Fin n =>
        complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i)
      hbase_pos hrel
  exact
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_theta
      hnpos A Delta heps0 hsmall theta hdetA_pos htheta_sv htheta_bound

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed determinant relative-change form of the all-index absolute
    singular-value perturbation bridge, under positive determinants. -/
theorem higham14_problem14_15_det_add_rel_le_of_singularValue_abs_sub_bound_of_det_pos
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps delta lower : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (hlower_pos : 0 < lower)
    (hlower : ∀ i : Fin n,
      lower ≤ complexMatrixSingularValue (realRectToCMatrix A) i)
    (habs : ∀ i : Fin n,
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ delta)
    (hscale : delta ≤ eps * lower)
    (hdetA_pos : 0 < Matrix.det (A : Matrix (Fin n) (Fin n) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ) /
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  have hAbs :=
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_abs_sub_bound
      hnpos A Delta heps0 hsmall hlower_pos hlower habs hscale
      (abs_pos.mpr hdetA_pos.ne')
  simpa [abs_of_pos hdetA_pos, abs_of_pos hdetB_pos] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    a certified right inverse makes the last ordered singular value positive
    in every nonzero dimension. -/
theorem higham14_problem14_15_last_singularValue_pos_of_isRightInverse
    {k : ℕ} (A Ainv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    0 <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  have hNormPos : 0 < opNorm2 Ainv :=
    opNorm2_pos_of_right_inverse_at (Fin.last k) A Ainv hRight
  have hInvEq :=
    higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue
      A Ainv hRight
  have hInvPos :
      0 <
        (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k))⁻¹ := by
    simpa [hInvEq] using hNormPos
  exact inv_pos.mp hInvPos

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    the last ordered singular value is a lower bound for all ordered singular
    values. -/
theorem higham14_problem14_15_last_singularValue_le_singularValue
    {k : ℕ} (A : Fin (k + 1) → Fin (k + 1) → ℝ) :
    ∀ i : Fin (k + 1),
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) ≤
        complexMatrixSingularValue (realRectToCMatrix A) i := by
  intro i
  exact complexMatrixSingularValue_antitone (realRectToCMatrix A) (Fin.le_last i)

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    with a certified right inverse, the source scaling
    `κ₂(A) * ||ΔA||₂ / ||A||₂` is exactly `||ΔA||₂ / σ_n(A)`, hence
    supplies the lower-scale premise needed by the determinant bridge. -/
theorem higham14_problem14_15_opNorm2_le_kappa2_scaled_last_singularValue
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    opNorm2 Delta ≤
      (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) *
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  let top : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  let last : Fin (k + 1) := Fin.last k
  let sigma : Fin (k + 1) → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix A) i
  have hlast_pos : 0 < sigma last := by
    simpa [sigma, last] using
      higham14_problem14_15_last_singularValue_pos_of_isRightInverse
        A Ainv hRight
  have hlast_le_top : sigma last ≤ sigma top := by
    simpa [sigma, top, last] using
      higham14_problem14_15_last_singularValue_le_singularValue A top
  have htop_pos : 0 < sigma top := lt_of_lt_of_le hlast_pos hlast_le_top
  have hlast_ne : sigma last ≠ 0 := ne_of_gt hlast_pos
  have htop_ne : sigma top ≠ 0 := ne_of_gt htop_pos
  have hkappa :
      kappa2 A Ainv = sigma top / sigma last := by
    simpa [sigma, top, last] using
      higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
        A Ainv hRight
  have hop : opNorm2 A = sigma top := by
    simpa [sigma, top] using
      higham14_problem14_13_opNorm2_eq_complex_top_singularValue
        (Nat.succ_pos k) A
  have hscale_eq :
      (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) * sigma last =
        opNorm2 Delta := by
    calc
      (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) * sigma last
          = ((sigma top / sigma last) * opNorm2 Delta / sigma top) *
              sigma last := by
                rw [hkappa, hop]
      _ = opNorm2 Delta := by
            field_simp [hlast_ne, htop_ne]
  simp [sigma, last, hscale_eq]

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    source-scaled determinant perturbation bridge.  If the still-open
    all-index singular-value perturbation inequality supplies
    `|σ_i(A+ΔA)-σ_i(A)| <= ||ΔA||₂`, then the matrix-specific
    `κ₂(A)||ΔA||₂/||A||₂` scaling and determinant product argument give the
    printed relative-change radius, under the necessary `n*eps < 1` guard. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)| /
        |Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)|) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  let top : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  let last : Fin (k + 1) := Fin.last k
  let sigma : Fin (k + 1) → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix A) i
  have hlast_pos : 0 < sigma last := by
    simpa [sigma, last] using
      higham14_problem14_15_last_singularValue_pos_of_isRightInverse
        A Ainv hRight
  have hlast_le_top : sigma last ≤ sigma top := by
    simpa [sigma, top, last] using
      higham14_problem14_15_last_singularValue_le_singularValue A top
  have htop_pos : 0 < sigma top := lt_of_lt_of_le hlast_pos hlast_le_top
  have hop : opNorm2 A = sigma top := by
    simpa [sigma, top] using
      higham14_problem14_13_opNorm2_eq_complex_top_singularValue
        (Nat.succ_pos k) A
  have hOpA_pos : 0 < opNorm2 A := by
    rw [hop]
    exact htop_pos
  have hkappa_nonneg : 0 ≤ kappa2 A Ainv := by
    unfold kappa2
    exact mul_nonneg (opNorm2_nonneg A) (opNorm2_nonneg Ainv)
  have heps0 :
      0 ≤ kappa2 A Ainv * opNorm2 Delta / opNorm2 A := by
    exact div_nonneg
      (mul_nonneg hkappa_nonneg (opNorm2_nonneg Delta)) hOpA_pos.le
  exact
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_abs_sub_bound
      (Nat.succ_pos k) A Delta heps0 hsmall hlast_pos
      (by
        intro i
        simpa [sigma, last] using
          higham14_problem14_15_last_singularValue_le_singularValue A i)
      habs
      (higham14_problem14_15_opNorm2_le_kappa2_scaled_last_singularValue
        A Ainv Delta hRight)
      (higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight)

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed determinant version of the source-scaled conditional bridge, when
    both determinants are positive. -/
theorem higham14_problem14_15_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_of_det_pos
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta)
    (hdetA_pos : 0 < Matrix.det
      (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) /
        Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  have hAbs :=
    higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound
      A Ainv Delta hRight hsmall habs
  simpa [abs_of_pos hdetA_pos, abs_of_pos hdetB_pos] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 side-condition audit:
    the product-radius denominator is positive under the corrected guard
    `eps < 1/n`, because then `n*eps < 1`.

The determinant perturbation wrappers use the stronger `n*eps < 1` guard
directly; this lemma records the equivalent small-parameter form for positive
dimension. -/
theorem higham14_problem14_15_product_guard_of_lt_inv_card {n : ℕ}
    (hnpos : 0 < n) {eps : ℝ}
    (hsmall : eps < ((n : ℝ)⁻¹)) :
    (n : ℝ) * eps < (1 : ℝ) := by
  have hnreal_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  calc
    (n : ℝ) * eps < (n : ℝ) * ((n : ℝ)⁻¹) := by
      exact mul_lt_mul_of_pos_left hsmall hnreal_pos
    _ = (1 : ℝ) := by
      field_simp [ne_of_gt hnreal_pos]

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 side-condition audit:
    the weaker-looking hypothesis `eps < 1` does not imply the denominator
    guard `n*eps < 1` once `n > 1`.  For `n = 2`, `eps = 3/4` is already a
    counterexample. -/
theorem higham14_problem14_15_eps_lt_one_not_sufficient_for_product_guard :
    ∃ eps : ℝ, 0 ≤ eps ∧ eps < 1 ∧ ¬ ((2 : ℝ) * eps < 1) := by
  refine ⟨(3 : ℝ) / 4, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    source-scaled determinant perturbation bridge with the corrected
    small-parameter guard `eps < 1/(k+1)`.  It is a source-side-condition
    wrapper around the existing `n*eps < 1` determinant bridge.

The remaining spectral input is still the all-index absolute singular-value
perturbation bound supplied by `habs`. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_inv_card_guard
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A <
        (((k + 1 : ℕ) : ℝ)⁻¹))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)| /
        |Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)|) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  have hguard :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ) :=
    higham14_problem14_15_product_guard_of_lt_inv_card (Nat.succ_pos k) hsmall
  exact
    higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound
      A Ainv Delta hRight hguard habs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed determinant companion of the corrected `eps < 1/(k+1)` guard
    wrapper, under positive determinant signs. -/
theorem higham14_problem14_15_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_inv_card_guard_of_det_pos
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A <
        (((k + 1 : ℕ) : ℝ)⁻¹))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta)
    (hdetA_pos : 0 < Matrix.det
      (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) /
        Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  have hguard :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ) :=
    higham14_problem14_15_product_guard_of_lt_inv_card (Nat.succ_pos k) hsmall
  exact
    higham14_problem14_15_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_of_det_pos
      A Ainv Delta hRight hguard habs hdetA_pos hdetB_pos

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    the smallest ordered singular value of a perturbed square matrix is bounded
    below by `sigma_min(A) - delta` whenever `delta` bounds `B - A` in
    operator 2-norm.  This is the extremal singular-value perturbation line
    reused from the Chapter 20 Wedin infrastructure. -/
theorem higham14_problem14_15_sigmaMin_sub_le_sigmaMin_of_sub_rectOpNorm2Le
    {k : ℕ} (A B : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) - delta ≤
      complexMatrixSingularValue (realRectToCMatrix B) (Fin.last k) := by
  simpa [wedinLemma20_11_sigmaMinCol] using
    wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
      A B hDelta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    additive perturbation form of the smallest-singular-value lower bound. -/
theorem higham14_problem14_15_sigmaMin_sub_le_sigmaMin_add_of_rectOpNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le Delta delta) :
    complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) - delta ≤
      complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k) := by
  have hSub :
      rectOpNorm2Le
        (fun i j => (A i j + Delta i j) - A i j) delta := by
    convert hDelta using 1
    ext i j
    ring
  exact
    higham14_problem14_15_sigmaMin_sub_le_sigmaMin_of_sub_rectOpNorm2Le
      A (fun i j => A i j + Delta i j) hSub

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    a perturbation smaller than `sigma_min(A)` keeps the perturbed smallest
    singular value positive. -/
theorem higham14_problem14_15_sigmaMin_add_pos_of_rectOpNorm2Le_lt
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le Delta delta)
    (hsmall :
      delta <
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)) :
    0 <
      complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k) := by
  have hSub :
      rectOpNorm2Le
        (fun i j => (A i j + Delta i j) - A i j) delta := by
    convert hDelta using 1
    ext i j
    ring
  simpa [wedinLemma20_11_sigmaMinCol] using
    wedinLemma20_11_sigmaMinCol_pos_of_sub_rectOpNorm2Le_lt
      A (fun i j => A i j + Delta i j) hSub
      (by simpa [wedinLemma20_11_sigmaMinCol] using hsmall)

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    rectangular operator-2 certificates are stable under negating the matrix.
    This lets extremal singular-value perturbation estimates be applied in
    both additive directions. -/
theorem higham14_problem14_15_rectOpNorm2Le_neg
    {m n : Nat} {M : Fin m -> Fin n -> Real} {c : Real}
    (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le (fun i j => -M i j) c := by
  intro x
  have hmul :
      rectMatMulVec (fun i j => -M i j) x =
        fun i => -rectMatMulVec M x i := by
    ext i
    unfold rectMatMulVec
    calc
      (Finset.univ.sum fun j : Fin n => (-M i j) * x j)
          = Finset.univ.sum fun j : Fin n => -(M i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = -(Finset.univ.sum fun j : Fin n => M i j * x j) := by
            rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hM x

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    absolute perturbation bound for the smallest ordered singular value.
    This closes the last-index extremal case of the all-index Weyl/Mirsky
    inequality still needed for the full determinant perturbation theorem. -/
theorem higham14_problem14_15_sigmaMin_abs_sub_le_of_rectOpNorm2Le
    {k : Nat} (A Delta : Fin (k + 1) -> Fin (k + 1) -> Real) {delta : Real}
    (hDelta : rectOpNorm2Le Delta delta) :
    |complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k) -
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)| <= delta := by
  let sigmaA : Real := complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)
  let sigmaB : Real :=
    complexMatrixSingularValue
      (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k)
  have hLower : sigmaA - delta <= sigmaB := by
    simpa [sigmaA, sigmaB] using
      higham14_problem14_15_sigmaMin_sub_le_sigmaMin_add_of_rectOpNorm2Le
        A Delta hDelta
  have hNeg : rectOpNorm2Le (fun i j => -Delta i j) delta :=
    higham14_problem14_15_rectOpNorm2Le_neg hDelta
  have hReverseRaw :
      sigmaB - delta <=
        complexMatrixSingularValue
          (realRectToCMatrix
            (fun i j => (A i j + Delta i j) + -Delta i j)) (Fin.last k) := by
    simpa [sigmaB] using
      higham14_problem14_15_sigmaMin_sub_le_sigmaMin_add_of_rectOpNorm2Le
        (fun i j => A i j + Delta i j) (fun i j => -Delta i j) hNeg
  have hReverse : sigmaB - delta <= sigmaA := by
    simpa [sigmaA] using hReverseRaw
  have hRight : sigmaB - sigmaA <= delta := by linarith
  have hLeft : -delta <= sigmaB - sigmaA := by linarith
  have hAbs : |sigmaB - sigmaA| <= delta :=
    abs_le.mpr (And.intro hLeft hRight)
  simpa [sigmaA, sigmaB] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    operator 2-norm triangle inequality for an additive perturbation. -/
theorem higham14_problem14_15_opNorm2_add_le_of_opNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : opNorm2Le Delta delta) :
    opNorm2 (fun i j => A i j + Delta i j) ≤ opNorm2 A + delta := by
  have hdelta_nonneg : 0 ≤ delta :=
    opNorm2Le_radius_nonneg Delta hDelta
  refine opNorm2_le_of_opNorm2Le
    (fun i j => A i j + Delta i j)
    (add_nonneg (opNorm2_nonneg A) hdelta_nonneg) ?_
  intro x
  rw [matMulVec_add_left]
  calc
    vecNorm2 (fun i => matMulVec (k + 1) A x i + matMulVec (k + 1) Delta x i)
        ≤ vecNorm2 (matMulVec (k + 1) A x) +
            vecNorm2 (matMulVec (k + 1) Delta x) :=
          vecNorm2_add_le _ _
    _ ≤ opNorm2 A * vecNorm2 x + delta * vecNorm2 x :=
          add_le_add (opNorm2Le_opNorm2 A x) (hDelta x)
    _ = (opNorm2 A + delta) * vecNorm2 x := by
          ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    largest-singular-value additive perturbation bound, expressed through the
    Chapter 14 ordered-singular-value bridge. -/
theorem higham14_problem14_15_top_singularValue_add_le_of_opNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : opNorm2Le Delta delta) :
    complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j))
        ⟨0, Nat.succ_pos k⟩ ≤
      complexMatrixSingularValue (realRectToCMatrix A)
          ⟨0, Nat.succ_pos k⟩ + delta := by
  rw [← higham14_problem14_13_opNorm2_eq_complex_top_singularValue
      (Nat.succ_pos k) (fun i j => A i j + Delta i j),
    ← higham14_problem14_13_opNorm2_eq_complex_top_singularValue
      (Nat.succ_pos k) A]
  exact higham14_problem14_15_opNorm2_add_le_of_opNorm2Le A Delta hDelta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    square operator 2-norm certificates are stable under negating the matrix.
    This local helper lets the largest-singular-value perturbation bound be
    applied in both directions without importing the QR-specific wrapper. -/
theorem higham14_problem14_15_opNorm2Le_neg
    {n : ℕ} {M : Fin n → Fin n → ℝ} {c : ℝ}
    (hM : opNorm2Le M c) :
    opNorm2Le (fun i j => -M i j) c := by
  intro x
  have hmul :
      matMulVec n (fun i j => -M i j) x =
        fun i => -matMulVec n M x i := by
    ext i
    unfold matMulVec
    calc
      (Finset.univ.sum fun j : Fin n => (-M i j) * x j)
          = Finset.univ.sum fun j : Fin n => -(M i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = -(Finset.univ.sum fun j : Fin n => M i j * x j) := by
            rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hM x

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    absolute perturbation bound for the largest ordered singular value.  This
    is only the top-index case of the all-index Weyl/Mirsky inequality still
    needed to close the full determinant perturbation theorem. -/
theorem higham14_problem14_15_top_singularValue_abs_sub_le_of_opNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : opNorm2Le Delta delta) :
    |complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j))
        ⟨0, Nat.succ_pos k⟩ -
      complexMatrixSingularValue (realRectToCMatrix A)
        ⟨0, Nat.succ_pos k⟩| ≤ delta := by
  let top : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  have hUpper :
      complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top ≤
        complexMatrixSingularValue (realRectToCMatrix A) top + delta := by
    simpa [top] using
      higham14_problem14_15_top_singularValue_add_le_of_opNorm2Le
        A Delta hDelta
  have hNeg : opNorm2Le (fun i j => -Delta i j) delta :=
    higham14_problem14_15_opNorm2Le_neg hDelta
  have hLowerRaw :
      complexMatrixSingularValue
          (realRectToCMatrix
            (fun i j => (A i j + Delta i j) + -Delta i j)) top ≤
        complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top + delta := by
    simpa [top] using
      higham14_problem14_15_top_singularValue_add_le_of_opNorm2Le
        (fun i j => A i j + Delta i j) (fun i j => -Delta i j) hNeg
  have hLower :
      complexMatrixSingularValue (realRectToCMatrix A) top ≤
        complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top + delta := by
    simpa [top] using hLowerRaw
  have hRight :
      complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top -
        complexMatrixSingularValue (realRectToCMatrix A) top ≤ delta := by
    linarith
  have hLeft :
      -delta ≤
        complexMatrixSingularValue
            (realRectToCMatrix (fun i j => A i j + Delta i j)) top -
          complexMatrixSingularValue (realRectToCMatrix A) top := by
    linarith
  simpa [top] using abs_le.mpr ⟨hLeft, hRight⟩

end NumStability
