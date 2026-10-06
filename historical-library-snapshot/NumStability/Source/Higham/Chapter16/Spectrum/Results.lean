import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.SpectralSolvability
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Source.Higham.Chapter16.Foundations.Core
import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.API
import NumStability.Analysis.MatrixEquations.SylvesterExistence
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.ComplexSolvability.SpectralCriterion
import NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.Spectrum
import NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.Equation29Extensions.Spectrum

/-!
# Algorithms.Sylvester.Higham16Spectrum

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

-- Algorithms/Sylvester/Higham16Spectrum.lean
--
-- Constructive spectral directions for the vec/Kronecker Sylvester
-- coefficient (Higham, Accuracy and Stability of Numerical Algorithms,
-- 2nd ed., Chapter 16.1, equation (16.3)) and the Bartels-Stewart
-- supplied-triangular column recurrence (Higham, 2nd ed., Chapter 16.2,
-- equations (16.4)-(16.8)).  This file complements `Higham16.lean`, whose
-- namespace and matrix conventions it follows exactly; it adds the general
-- (non-diagonal) constructive halves of those two source rows:
--
-- * every pairwise difference of supplied real eigenpairs of `A` and `B^T`
--   is an eigenvalue of `I_n kron A - B^T kron I_m`, and a shared eigenvalue
--   makes the coefficient singular (the constructive directions of (16.3));
-- * with a SUPPLIED upper-triangular `T`, the transformed equation
--   `AX - XT = C` decouples column by column into
--   `(A - t_kk I) x_k = c_k + sum_{j<k} t_jk x_j`, and per-column
--   nonsingularity of the shifted matrices gives a unique exact solution by
--   forward substitution over columns; this is the (16.5)/(16.6)
--   Bartels-Stewart existence statement at the supplied-factor level.
--
-- Honest scope:
-- * The complex Schur route is imported to prove determinant nonsingularity
--   of the real vec/Kronecker coefficient from a supplied no-common complex
--   right-eigenpair hypothesis on the entrywise complexifications of `A` and
--   `B`.  The complex coefficient now also has the shifted determinant form of
--   the full spectrum-characterization statement: a scalar shift is singular
--   exactly when it is a difference `lambda(A) - mu(B)`.
-- * The quasi-triangular (2x2 diagonal block, real-Schur) Bartels-Stewart
--   route behind equations (16.4), (16.7), and (16.8) is represented by an
--   imported real quasi-Schur existence wrapper plus supplied adjacent
--   two-column exact block-equation lemmas; the full block solver and
--   floating-point error propagation remain open.
-- * No floating-point rounding analysis: triangular and eigenpair data in the
--   solver wrappers are supplied hypotheses, exactly as in the supplied-factor
--   diagonal case of `Higham16.lean`.






namespace NumStability

open scoped BigOperators

-- ============================================================
-- (16.4): real quasi-Schur factors for both Sylvester sides
-- ============================================================




























































































































































































































































































































































-- ============================================================
-- (16.3): constructive spectral directions
-- ============================================================























































































































































































































































































































































































-- ============================================================
-- (16.4)-(16.8): Bartels-Stewart supplied-triangular column solve
-- ============================================================




























































































private theorem triangular_column_sum_split (m n : Nat) (T : RMatFn n n)
    (hT : IsUpperTriangularFn n T) (X : RMatFn m n) (i : Fin m) (k : Fin n) :
    (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) =
      T k k * X i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  have hsub : Finset.sum (Finset.filter (fun j => j <= k) Finset.univ)
        (fun j => X i j * T j k) =
      Finset.sum Finset.univ fun j : Fin n => X i j * T j k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hjnot
    have hnot : Not (j <= k) := by
      intro hle
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
    have hkj : k < j := not_le.mp hnot
    rw [hT j k hkj, mul_zero]
  rw [← hsub]
  have hset : Finset.filter (fun j => j <= k) Finset.univ =
      insert k (Finset.filter (fun j => j < k) Finset.univ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl heq
    · intro h
      rcases h with heq | hlt
      · exact le_of_eq heq
      · exact le_of_lt hlt
  have hknotmem : k ∉ Finset.filter (fun j => j < k) Finset.univ := by
    intro hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl k)
  rw [hset, Finset.sum_insert hknotmem, mul_comm (X i k) (T k k)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring



































































































































































































private theorem two_column_block_sum_split (m n : Nat) (T : RMatFn n n)
    (X : RMatFn m n) (i : Fin m) (p q k : Fin n)
    (hpq : q.val = p.val + 1)
    (hbelow : ∀ j : Fin n, q < j → T j k = 0) :
    (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) =
      T p k * X i p + T q k * X i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j k * X i j) := by
  have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
  have hsub : Finset.sum (Finset.filter (fun j => j <= q) Finset.univ)
        (fun j => X i j * T j k) =
      Finset.sum Finset.univ fun j : Fin n => X i j * T j k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hjnot
    have hnot : Not (j <= q) := by
      intro hle
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
    have hqj : q < j := not_le.mp hnot
    rw [hbelow j hqj, mul_zero]
  rw [← hsub]
  have hset : Finset.filter (fun j => j <= q) Finset.univ =
      insert q (insert p (Finset.filter (fun j => j < p) Finset.univ)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hjle
      by_cases hjq : j = q
      · exact Or.inl hjq
      · right
        by_cases hjp : j = p
        · exact Or.inl hjp
        · right
          apply Fin.lt_def.mpr
          have hjleNat : j.val <= q.val := Fin.le_def.mp hjle
          have hjqNat : j.val ≠ q.val := by
            intro hval
            exact hjq (Fin.ext hval)
          have hjpNat : j.val ≠ p.val := by
            intro hval
            exact hjp (Fin.ext hval)
          omega
    · intro h
      rcases h with heq | heq | hlt
      · exact le_of_eq heq
      · rw [heq]
        exact le_of_lt hpq_lt
      · exact le_trans (le_of_lt hlt) (le_of_lt hpq_lt)
  have hpnotmem : p ∉ Finset.filter (fun j => j < p) Finset.univ := by
    intro hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl p)
  have hqnotmem :
      q ∉ insert p (Finset.filter (fun j => j < p) Finset.univ) := by
    intro hmem
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rcases hmem with hqp | hqprev
    · exact (ne_of_gt hpq_lt) hqp
    · exact (not_lt_of_ge (le_of_lt hpq_lt)) hqprev
  rw [hset, Finset.sum_insert hqnotmem, Finset.sum_insert hpnotmem]
  have hprev : Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
        (fun j => X i j * T j k) =
      Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
        (fun j => T j k * X i j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hprev]
  ring


























































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), complex form:
    the complex vec/Kronecker Sylvester coefficient is nonsingular iff `A` and
    `B` have no common complex right eigenvalue. -/
theorem complexSylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue
    {m n : Nat}
    (A : Matrix (Fin m) (Fin m) Complex)
    (B : Matrix (Fin n) (Fin n) Complex) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 ↔
      NoCommonComplexRightEigenvalue A B := by
  constructor
  · intro hdet mu hcommon
    exact hdet (complexSylvesterVecCoeff_singular_of_common_right_eigenvalue
      A B mu hcommon.1 hcommon.2)
  · intro hno
    exact complexSylvesterVecCoeff_det_ne_zero_of_no_common_eigenpair A B hno

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), complex shifted spectrum
    characterization in determinant form: a scalar `theta` makes the shifted
    vec/Kronecker Sylvester coefficient singular iff `theta = lambda - mu` for
    supplied complex right eigenvalues `lambda` of `A` and `mu` of `B`. -/
theorem complexSylvesterVecCoeff_shifted_det_eq_zero_iff_exists_eigenvalue_difference
    {m n : Nat}
    (A : Matrix (Fin m) (Fin m) Complex)
    (B : Matrix (Fin n) (Fin n) Complex) (theta : Complex) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) theta) = 0 ↔
      ∃ lam : Complex, ∃ mu : Complex,
        HasComplexRightEigenvalue A lam ∧
        HasComplexRightEigenvalue B mu ∧
        lam - mu = theta := by
  classical
  constructor
  · intro hzero
    have hzero' :
        Matrix.det (complexSylvesterVecCoeff
          (A - Matrix.scalar (Fin m) theta) B) = 0 := by
      rw [complexSylvesterVecCoeff_left_shift_eq_shifted]
      exact hzero
    have hnotno : ¬ NoCommonComplexRightEigenvalue
        (A - Matrix.scalar (Fin m) theta) B := by
      intro hno
      have hne :=
        (complexSylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue
          (A - Matrix.scalar (Fin m) theta) B).mpr hno
      exact hne hzero'
    have hnotforall :
        ¬ (∀ mu : Complex,
          ¬ (HasComplexRightEigenvalue (A - Matrix.scalar (Fin m) theta) mu ∧
            HasComplexRightEigenvalue B mu)) := by
      simpa [NoCommonComplexRightEigenvalue] using hnotno
    have hex_mu := not_forall.mp hnotforall
    let mu := Classical.choose hex_mu
    have hnn := Classical.choose_spec hex_mu
    have hcommon :
        HasComplexRightEigenvalue (A - Matrix.scalar (Fin m) theta) mu ∧
          HasComplexRightEigenvalue B mu := by
      exact not_not.mp hnn
    have hA : HasComplexRightEigenvalue A (mu + theta) :=
      (hasComplexRightEigenvalue_sub_scalar_iff A theta mu).mp hcommon.1
    refine ⟨mu + theta, mu, hA, hcommon.2, ?_⟩
    ring
  · rintro ⟨lam, mu, hA, hB, hdiff⟩
    rw [← complexSylvesterVecCoeff_left_shift_eq_shifted]
    have hlam' : lam = theta + mu :=
      sub_eq_iff_eq_add.mp hdiff
    have hlam : lam = mu + theta := by
      rw [add_comm] at hlam'
      exact hlam'
    have hA' : HasComplexRightEigenvalue A (mu + theta) := by
      rw [← hlam]
      exact hA
    have hAshift :
        HasComplexRightEigenvalue (A - Matrix.scalar (Fin m) theta) mu :=
      (hasComplexRightEigenvalue_sub_scalar_iff A theta mu).mpr hA'
    by_contra hne
    have hno :=
      (complexSylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue
        (A - Matrix.scalar (Fin m) theta) B).mp hne
    exact hno mu ⟨hAshift, hB⟩

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias for
    the complex shifted vec/Kronecker spectrum/difference characterization. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_shifted_det_eq_zero_iff_exists_eigenvalue_difference
    {m n : Nat}
    (A : Matrix (Fin m) (Fin m) Complex)
    (B : Matrix (Fin n) (Fin n) Complex) (theta : Complex) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) theta) = 0 ↔
      ∃ lam : Complex, ∃ mu : Complex,
        HasComplexRightEigenvalue A lam ∧
        HasComplexRightEigenvalue B mu ∧
        lam - mu = theta :=
  complexSylvesterVecCoeff_shifted_det_eq_zero_iff_exists_eigenvalue_difference
    A B theta


























































































/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), real source-facing
    complexified shifted spectrum characterization: a complex scalar shift makes
    the complexification of the real vec/Kronecker Sylvester coefficient
    singular iff the shift is a difference of complex right eigenvalues of the
    complexified real factors. -/
theorem sylvesterVecCoeff_complexified_shifted_det_eq_zero_iff_exists_complex_eigenvalue_difference
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (theta : Complex) :
    Matrix.det (realMatrixToComplex (sylvesterVecCoeff m n A B) -
        Matrix.scalar (Prod (Fin n) (Fin m)) theta) = 0 ↔
      ∃ lam : Complex, ∃ mu : Complex,
        HasComplexRightEigenvalue (realMatrixToComplex A) lam ∧
        HasComplexRightEigenvalue (realMatrixToComplex B) mu ∧
        lam - mu = theta := by
  rw [realMatrixToComplex_sylvesterVecCoeff]
  exact
    complexSylvesterVecCoeff_shifted_det_eq_zero_iff_exists_eigenvalue_difference
      (realMatrixToComplex A) (realMatrixToComplex B) theta

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias for
    the complexified real vec/Kronecker shifted spectrum/difference theorem. -/
theorem H16_eq16_3_sylvesterVecCoeff_complexified_shifted_det_eq_zero_iff_exists_complex_eigenvalue_difference
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (theta : Complex) :
    Matrix.det (realMatrixToComplex (sylvesterVecCoeff m n A B) -
        Matrix.scalar (Prod (Fin n) (Fin m)) theta) = 0 ↔
      ∃ lam : Complex, ∃ mu : Complex,
        HasComplexRightEigenvalue (realMatrixToComplex A) lam ∧
        HasComplexRightEigenvalue (realMatrixToComplex B) mu ∧
        lam - mu = theta :=
  sylvesterVecCoeff_complexified_shifted_det_eq_zero_iff_exists_complex_eigenvalue_difference
    m n A B theta

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), complex spectral
    nonsingularity route for the real vec/Kronecker coefficient: if the
    entrywise complexifications of the real matrices `A` and `B` have no
    common supplied complex right eigenpair, then the real coefficient
    `I_n kron A - B^T kron I_m` has nonzero determinant. -/
theorem sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 := by
  intro hdet
  have hmap :
      Matrix.det (realMatrixToComplex (sylvesterVecCoeff m n A B)) =
        Complex.ofRealHom (Matrix.det (sylvesterVecCoeff m n A B)) := by
    simpa [realMatrixToComplex] using
      (RingHom.map_det Complex.ofRealHom (sylvesterVecCoeff m n A B)).symm
  have hcomplexZero :
      Matrix.det
        (complexSylvesterVecCoeff (realMatrixToComplex A) (realMatrixToComplex B)) = 0 := by
    rw [(realMatrixToComplex_sylvesterVecCoeff m n A B).symm, hmap, hdet]
    simp
  exact
    (complexSylvesterVecCoeff_det_ne_zero_of_no_common_eigenpair
      (realMatrixToComplex A) (realMatrixToComplex B) hno) hcomplexZero

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias for
    the real vec/Kronecker determinant nonsingularity theorem obtained from no
    common supplied complex right eigenpair of the entrywise complexified
    Sylvester factors. -/
theorem H16_eq16_3_sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 :=
  sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), named spectral-separation
    form: if the entrywise complexifications of the real Sylvester factors have
    no common complex right eigenvalue, then the real vec/Kronecker Sylvester
    coefficient is nonsingular. -/
theorem sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 :=
  sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias for
    the named no-common-complex-right-eigenvalue determinant route. -/
theorem H16_eq16_3_sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 :=
  sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue m n A B hno






























/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-facing iff:
    the real vec/Kronecker Sylvester coefficient is nonsingular exactly when
    the entrywise complexifications of `A` and `B` have no common supplied
    complex right eigenvalue. -/
theorem sylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 ↔
      NoCommonComplexRightEigenvalue (realMatrixToComplex A)
        (realMatrixToComplex B) := by
  constructor
  · exact no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero m n A B
  · exact sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue m n A B

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias for
    the determinant/eigenvalue-separation iff. -/
theorem H16_eq16_3_sylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 ↔
      NoCommonComplexRightEigenvalue (realMatrixToComplex A)
        (realMatrixToComplex B) :=
  sylvesterVecCoeff_det_ne_zero_iff_no_common_complex_right_eigenvalue m n A B

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    practical endpoint: if the entrywise complexifications of `A` and `B`
    have no common supplied complex right eigenvalue, the vec/Kronecker
    coefficient is nonsingular, so the exact nonsingular inverse supplies the
    practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    no-common-spectrum practical endpoint from a supplied Schur-coordinate
    Frobenius residual bound.  The no-common complex spectrum hypothesis
    supplies the exact nonsingular-inverse budget, while the Schur residual
    transport supplies the computed-residual budget with `Rhat = 0`. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (fun _ _ => 0) (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    scalar endpoint for the practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    monotone estimator-ready endpoint: after the no-common complex spectrum
    certificate supplies the exact inverse budget, componentwise larger inverse
    and residual-budget inputs preserve the practical computed-residual bound.
    This does not prove any particular estimator. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the relative
    max-entry forward-error bound. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    absolute endpoint: the same practical budget bounds the unnormalized
    max-entry forward error, with no positive denominator hypothesis. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    absolute scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    absolute monotone endpoint: after the no-common complex spectrum
    certificate supplies the exact inverse budget, componentwise larger inverse
    and residual-budget inputs preserve the denominator-free practical bound. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    absolute monotone scalar endpoint: after componentwise estimator
    enlargement, a scalar cap on the enlarged practical budget bounds the
    unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    scalar-cap no-common-spectrum practical endpoint from a supplied
    Schur-coordinate Frobenius residual bound. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (fun _ _ => 0) (fun _ _ => rho) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      eta /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) eta hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    monotone no-common-spectrum practical endpoint from a supplied
    Schur-coordinate Frobenius residual bound and enlarged estimator data. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru' PinvAbs'
      hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    monotone scalar-cap no-common-spectrum practical endpoint from a supplied
    Schur-coordinate Frobenius residual bound and enlarged estimator data. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho eta : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      eta /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru' PinvAbs' eta
      hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    denominator-free no-common-spectrum practical endpoint from a supplied
    Schur-coordinate Frobenius residual bound. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (fun _ _ => 0) (fun _ _ => rho)) := by
  exact
    sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    scalar-cap denominator-free no-common-spectrum practical endpoint from a
    supplied Schur-coordinate Frobenius residual bound. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (fun _ _ => 0) (fun _ _ => rho) p <= eta) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
      eta := by
  exact
    sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) eta hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    denominator-free monotone no-common-spectrum practical endpoint from a
    supplied Schur-coordinate Frobenius residual bound and enlarged estimator
    data. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru' PinvAbs'
      hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hPinvAbs_le hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    denominator-free monotone scalar no-common-spectrum practical endpoint from
    a supplied Schur-coordinate Frobenius residual bound and enlarged estimator
    data. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho eta : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
      eta := by
  exact
    sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru' PinvAbs' eta
      hno hX
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hPinvAbs_le hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    raw computed-residual budget endpoint. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_budget
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
      m n A B C X Xhat Rhat Ru hno hX (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    explicit residual-error-model endpoint. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
      m n A B C X Xhat Rhat Ru hno hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation practical computed-residual certificate. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the no-common-spectrum practical endpoint from a supplied Schur
    residual bound. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the scalar no-common-spectrum practical endpoint from a supplied Schur
    residual bound. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_scalar :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the monotone no-common-spectrum practical endpoint from a supplied
    Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the monotone scalar no-common-spectrum practical endpoint from a
    supplied Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono_scalar :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the denominator-free no-common-spectrum practical endpoint from a
    supplied Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the scalar denominator-free no-common-spectrum practical endpoint from
    a supplied Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_scalar :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the monotone denominator-free no-common-spectrum practical endpoint
    from a supplied Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the monotone scalar denominator-free no-common-spectrum practical
    endpoint from a supplied Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono_scalar :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_schur_transform_residual_bound_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation scalar computed-residual certificate. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation monotone computed-residual certificate. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation monotone scalar certificate. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation absolute computed-residual certificate. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation absolute scalar certificate. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation absolute monotone computed-residual
    certificate. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation absolute monotone scalar computed-residual
    certificate. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation raw computed-residual budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_budget :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation residual-error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_error_model :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_error_model





































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): a singleton block in a
    block-triangular Schur factor inherits shifted determinant nonsingularity
    from a global no-common-complex-right-eigenvalue hypothesis. -/
theorem sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_no_common_complex_right_eigenvalue_left
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (k : Fin n)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k)
    (hnoGlobal :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (Matrix.of T))) :
    Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0) := by
  have hBT : (realMatrixToComplex (Matrix.of T)).BlockTriangular pmap := by
    intro i j hij
    simp [realMatrixToComplex, Matrix.of_apply, hzero i j hij]
  have hnoSingleton :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex (fun _ _ : Fin 1 => T k k)) := by
    simpa [Matrix.of_apply] using
      noCommonComplexRightEigenvalue_of_singletonBlock_quasiSchur
        m n A T pmap k hBT hsingle hnoGlobal
  have hdetVec :
      Matrix.det (sylvesterVecCoeff m 1 A (fun _ _ : Fin 1 => T k k)) ≠ 0 :=
    sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
      m 1 A (fun _ _ : Fin 1 => T k k) hnoSingleton
  intro hdet
  exact hdetVec
    ((sylvesterVecCoeff_one_det_eq_sylvesterTriangularShiftedCoeff_det
      m A (T k k)).trans hdet)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): a singleton block in a
    block-triangular Schur factor inherits shifted determinant nonsingularity
    from nonsingularity of the global vec/Kronecker Sylvester coefficient. -/
theorem sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_vecCoeff_det_ne_zero
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (k : Fin n)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k)
    (hdetGlobal : Not (Matrix.det (sylvesterVecCoeff m n A T) = 0)) :
    Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0) := by
  exact
    sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_no_common_complex_right_eigenvalue_left
      m n A T pmap k hzero hsingle
      (by
        simpa [Matrix.of_apply] using
          no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
            m n A T hdetGlobal)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): source-numbered alias for
    singleton shifted determinant nonsingularity from a global vec/Kronecker
    determinant certificate. -/
alias H16_eq16_6_sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_vecCoeff_det_ne_zero :=
  sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_vecCoeff_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): supplied real orthogonal
    Schur factorizations transport original-coordinate no-common-complex-right
    eigenvalue data to the Schur-coordinate singleton shifted determinant. -/
theorem sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_no_common_complex_right_eigenvalue
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n)
    (pmap : Fin n -> Nat) (k : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig)) :
    Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0) := by
  have hnoRS :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex R)
        (realMatrixToComplex S) :=
    noCommonComplexRightEigenvalue_realQuasiSchur_factors
      m n U R Aorig V S Borig hU hV hA hB hnoOrig
  exact
    sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_no_common_complex_right_eigenvalue_left
      m n R S pmap k hzero hsingle
      (by simpa [Matrix.of_apply] using hnoRS)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): supplied real orthogonal
    Schur factorizations transport original-coordinate vec/Kronecker
    determinant nonsingularity to the Schur-coordinate singleton shifted
    determinant. -/
theorem sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n)
    (pmap : Fin n -> Nat) (k : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hsingle : forall i : Fin n, pmap i = pmap k -> i = k)
    (hdetOrig :
      Not (Matrix.det (sylvesterVecCoeff m n Aorig Borig) = 0)) :
    Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0) := by
  exact
    sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_no_common_complex_right_eigenvalue
      m n U R Aorig V S Borig pmap k hU hV hA hB hzero hsingle
      (no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
        m n Aorig Borig hdetOrig)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6): source-numbered alias for
    real-Schur supplied-factor singleton shifted determinant nonsingularity
    from an original vec/Kronecker determinant certificate. -/
alias H16_eq16_6_sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero :=
  sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero
















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    quasi-triangular `2 x 2` block recurrence: if columns `p,q` form a supplied
    adjacent diagonal block of the Schur factor `T`, then any exact solution of
    `AX - XT = C` satisfies the simultaneous two-column block system used by
    the real Bartels-Stewart method.  Scope: exact supplied block algebra only;
    this does not assert a real Schur decomposition, block nonsingularity,
    a full Hessenberg-Schur solver, or any floating-point error bound. -/
theorem sylvester_quasiTriangular_two_column_block_system_of_solution
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hblock : IsAdjacentQuasiTriangularBlockFn n T p q)
    (hX : IsSylvesterSolutionRect m n A T C X) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  rcases hblock with ⟨hpq, hbelowp, hbelowq⟩
  constructor
  · funext i
    rw [sylvesterTriangularShiftedCoeff_mulVec_apply]
    have hop : sylvesterOpRect m n A T X i p =
        (Finset.sum Finset.univ fun l : Fin m => A i l * X l p) -
          (Finset.sum Finset.univ fun j : Fin n => X i j * T j p) := rfl
    have hsum := two_column_block_sum_split m n T X i p q p hpq hbelowp
    have hsol := hX i p
    rw [hop, hsum] at hsol
    show ((Finset.sum Finset.univ fun l : Fin m => A i l * X l p) -
        T p p * X i p) - T q p * X i q =
      C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p * X i j)
    rw [← hsol]
    ring
  · funext i
    rw [sylvesterTriangularShiftedCoeff_mulVec_apply]
    have hop : sylvesterOpRect m n A T X i q =
        (Finset.sum Finset.univ fun l : Fin m => A i l * X l q) -
          (Finset.sum Finset.univ fun j : Fin n => X i j * T j q) := rfl
    have hsum := two_column_block_sum_split m n T X i p q q hpq hbelowq
    have hsol := hX i q
    rw [hop, hsum] at hsol
    show ((Finset.sum Finset.univ fun l : Fin m => A i l * X l q) -
        T q q * X i q) - T p q * X i p =
      C i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j q * X i j)
    rw [← hsol]
    ring

/-- Converse column bridge for the supplied adjacent two-column recurrence:
    if the candidate columns satisfy the exact block recurrence for an
    adjacent quasi-triangular block, then both active columns satisfy the
    original Sylvester equation. -/
theorem sylvester_quasiTriangular_solution_columns_of_two_column_block_system
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hblock : IsAdjacentQuasiTriangularBlockFn n T p q)
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q) :
    (forall i : Fin m, sylvesterOpRect m n A T X i p = C i p) /\
      (forall i : Fin m, sylvesterOpRect m n A T X i q = C i q) := by
  rcases hblock with ⟨hpq, hbelowp, hbelowq⟩
  rcases hX with ⟨hp, hq⟩
  constructor
  · intro i
    have hsys := congrFun hp i
    rw [sylvesterTriangularShiftedCoeff_mulVec_apply] at hsys
    have hop : sylvesterOpRect m n A T X i p =
        (Finset.sum Finset.univ fun l : Fin m => A i l * X l p) -
          (Finset.sum Finset.univ fun j : Fin n => X i j * T j p) := rfl
    have hsum := two_column_block_sum_split m n T X i p q p hpq hbelowp
    rw [hop, hsum]
    linarith
  · intro i
    have hsys := congrFun hq i
    rw [sylvesterTriangularShiftedCoeff_mulVec_apply] at hsys
    have hop : sylvesterOpRect m n A T X i q =
        (Finset.sum Finset.univ fun l : Fin m => A i l * X l q) -
          (Finset.sum Finset.univ fun j : Fin n => X i j * T j q) := rfl
    have hsum := two_column_block_sum_split m n T X i p q q hpq hbelowq
    rw [hop, hsum]
    linarith

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), solution-facing
    real-Schur supplied-factor recurrence step: if `Y` is any exact
    Schur-coordinate solution and the earlier columns already agree, then the
    nonsingular-inverse active two-column update agrees with `Y` on the active
    block.  This packages the exact-solution-to-block-system conversion needed
    by a later block-order induction. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_solution_prev_columns_eq
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))
    (hYsol : IsSylvesterSolutionRect m n R S C Y)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hblock : IsAdjacentQuasiTriangularBlockFn n S p q :=
    IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n S pmap p q hmono hcard hzero hpq_adj hsame
  have hYblock : IsSylvesterTwoColumnBlockSystem m n R S C Y p q :=
    sylvester_quasiTriangular_two_column_block_system_of_solution
      m n R S C Y p q hblock hYsol
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_prev_columns_eq
      m n U R Aorig V S Borig C X Y pmap p q hU hV hA hB hmono hcard hzero
      hpq_adj hsame hspectral hnoOrig hXp hXq hYblock hprev

/-- Vector form of
    `sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_solution_prev_columns_eq`. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_solution_prev_columns_eq
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
          (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))
    (hYsol : IsSylvesterSolutionRect m n R S C Y)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_solution_prev_columns_eq
      m n U R Aorig V S Borig C X Y pmap p q hU hV hA hB hmono hcard hzero
      hpq_adj hsame hspectral hnoOrig hXp hXq hYsol hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5)-(16.6), pure algebra:
    for upper-triangular `T`, applying the shifted column coefficient to
    column `k` of any `X` splits the Sylvester operator column into the
    already-solved earlier columns,
    `((A - t_kk I) x_k)_i = (AX - XT)_ik + sum_{j<k} t_jk x_ij`.
    The index order and sign follow the module's `sylvesterOpRect`
    orientation `AX - XT`. -/
theorem sylvester_triangular_column_identity (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) (k : Fin n) (i : Fin m) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
        (fun i' => X i' k) i =
      sylvesterOpRect m n A T X i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  rw [sylvesterTriangularShiftedCoeff_mulVec_apply]
  show (Finset.sum Finset.univ fun l : Fin m => A i l * X l k) -
      T k k * X i k =
    sylvesterOpRect m n A T X i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * X i j)
  have hop : sylvesterOpRect m n A T X i k =
      (Finset.sum Finset.univ fun l : Fin m => A i l * X l k) -
        (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) := rfl
  rw [hop, triangular_column_sum_split m n T hT X i k]
  ring

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    if `X` solves `AX - XT = C` with `T` upper triangular, then column `k`
    of the equation reads
    `(A - t_kk I) x_k = c_k + sum_{j<k} t_jk x_j`.
    This is the Bartels-Stewart forward-substitution structure at the
    supplied-triangular level. -/
theorem sylvester_triangular_column_equation (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T)
    (hX : IsSylvesterSolutionRect m n A T C X) (k : Fin n) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
        (fun i => X i k) =
      fun i => C i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  funext i
  rw [sylvester_triangular_column_identity m n A T X hT k i, hX i k]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5)-(16.6):
    for upper-triangular `T`, solving the rectangular Sylvester equation is
    equivalent to satisfying every Bartels-Stewart column equation. -/
theorem sylvester_triangular_solution_iff_column_equations (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) :
    IsSylvesterSolutionRect m n A T C X <->
      forall k : Fin n,
        Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
            (fun i => X i k) =
          fun i => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => T j k * X i j) := by
  constructor
  case mp =>
    intro hX k
    exact sylvester_triangular_column_equation m n A T C X hT hX k
  case mpr =>
    intro h i j
    have hj := congrFun (h j) i
    rw [sylvester_triangular_column_identity m n A T X hT j i] at hj
    exact add_right_cancel hj

private theorem mulVec_injective_of_det_ne_zero {m : Nat}
    {M : Matrix (Fin m) (Fin m) Real} (hdet : Not (M.det = 0))
    {x y : Fin m -> Real}
    (hxy : Matrix.mulVec M x = Matrix.mulVec M y) : x = y := by
  have h := congrArg (Matrix.mulVec M⁻¹) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

private theorem mulVec_surjective_of_det_ne_zero {m : Nat}
    {M : Matrix (Fin m) (Fin m) Real} (hdet : Not (M.det = 0))
    (c : Fin m -> Real) :
    exists x : Fin m -> Real, Matrix.mulVec M x = c := by
  refine ⟨Matrix.mulVec M⁻¹ c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]


























/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    nonsingularity of `A - t I` makes the map
    `x |-> (A - t I) x` injective. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_injective (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    Function.Injective
      (Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t)) := by
  intro x y hxy
  exact mulVec_injective_of_det_ne_zero hdet hxy

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    nonsingularity of `A - t I` makes the map
    `x |-> (A - t I) x` surjective, so every active column right-hand side is
    reachable in exact arithmetic. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_surjective (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t)) := by
  intro c
  exact mulVec_surjective_of_det_ne_zero hdet c

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    nonsingularity of `A - t I` makes the active column solve a bijection. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_bijective (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t)) :=
  ⟨sylvesterTriangularShiftedCoeff_mulVec_injective m A t hdet,
    sylvesterTriangularShiftedCoeff_mulVec_surjective m A t hdet⟩

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    for every active column right-hand side, the shifted system
    `(A - t I) x = c` has exactly one solution. -/
theorem existsUnique_sylvesterTriangularShiftedCoeff_mulVec (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0))
    (c : Fin m -> Real) :
    ∃! x : Fin m -> Real,
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t) x = c := by
  have hinj := sylvesterTriangularShiftedCoeff_mulVec_injective m A t hdet
  have hsurj := sylvesterTriangularShiftedCoeff_mulVec_surjective m A t hdet
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column step:
    for supplied upper-triangular `T`, determinant nonsingularity of the shifted
    coefficient `A - t_kk I` gives existence and uniqueness for the exact
    single-column recurrence
    `(A - t_kk I) x_k = c_k + sum_{j<k} t_jk x_j`.
    This is only the supplied-shift column solve certificate; it does not assert
    Schur construction, quasi-triangular block assembly, or floating-point
    stability. -/
theorem existsUnique_sylvester_triangular_column_step_of_shifted_det (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) (k : Fin n)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0)) :
    ∃! x : Fin m -> Real,
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) x =
        fun i => C i k +
          Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
            (fun j => T j k * X i j) := by
  have _ : IsUpperTriangularFn n T := hT
  exact existsUnique_sylvesterTriangularShiftedCoeff_mulVec m A (T k k) hdet
    (fun i => C i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * X i j))

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column step:
    under the same shifted determinant nonsingularity, two supplied candidate
    vectors that solve the exact active column equation for the same right-hand
    side must be equal.  This is only a uniqueness consequence for the supplied
    shifted coefficient, not a full Schur assembly or floating-point result. -/
theorem sylvester_triangular_column_step_eq_of_shifted_det (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) (k : Fin n)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    {x y : Fin m -> Real}
    (hx :
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) x =
        fun i => C i k +
          Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
            (fun j => T j k * X i j))
    (hy :
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) y =
        fun i => C i k +
          Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
            (fun j => T j k * X i j)) :
    x = y := by
  obtain ⟨w, hw, huniq⟩ :=
    existsUnique_sylvester_triangular_column_step_of_shifted_det
      m n A T C X hT k hdet
  exact (huniq x hx).trans (huniq y hy).symm

private theorem column_sum_split_of_zero_below (m n : Nat)
    (T : RMatFn n n) (X : RMatFn m n) (i : Fin m) (k : Fin n)
    (hbelow : forall j : Fin n, k < j -> T j k = 0) :
    (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) =
      T k k * X i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  have hsub : Finset.sum (Finset.filter (fun j => j <= k) Finset.univ)
        (fun j => X i j * T j k) =
      Finset.sum Finset.univ fun j : Fin n => X i j * T j k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hjnot
    have hnot : Not (j <= k) := by
      intro hle
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
    have hkj : k < j := not_le.mp hnot
    rw [hbelow j hkj, mul_zero]
  rw [← hsub]
  have hset : Finset.filter (fun j => j <= k) Finset.univ =
      insert k (Finset.filter (fun j => j < k) Finset.univ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl heq
    · intro h
      rcases h with heq | hlt
      · exact le_of_eq heq
      · exact le_of_lt hlt
  have hknotmem : k ∉ Finset.filter (fun j => j < k) Finset.univ := by
    intro hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl k)
  rw [hset, Finset.sum_insert hknotmem, mul_comm (X i k) (T k k)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Column-local form of the Bartels-Stewart identity: to derive the
    one-column recurrence for column `k`, it is enough to know that entries
    strictly below that column vanish.  This is the singleton-block analogue
    of `sylvester_triangular_column_identity` for quasi-Schur traversal. -/
theorem sylvester_column_identity_of_zero_below (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (X : RMatFn m n)
    (k : Fin n)
    (hbelow : forall j : Fin n, k < j -> T j k = 0) (i : Fin m) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
        (fun i' => X i' k) i =
      sylvesterOpRect m n A T X i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  rw [sylvesterTriangularShiftedCoeff_mulVec_apply]
  show (Finset.sum Finset.univ fun l : Fin m => A i l * X l k) -
      T k k * X i k =
    sylvesterOpRect m n A T X i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * X i j)
  have hop : sylvesterOpRect m n A T X i k =
      (Finset.sum Finset.univ fun l : Fin m => A i l * X l k) -
        (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) := rfl
  rw [hop, column_sum_split_of_zero_below m n T X i k hbelow]
  ring

/-- If an exact Sylvester solution is restricted to a column whose entries
    below the diagonal vanish, that column satisfies the one-column
    Bartels-Stewart recurrence. -/
theorem sylvester_column_equation_of_solution_zero_below (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (k : Fin n)
    (hbelow : forall j : Fin n, k < j -> T j k = 0)
    (hX : IsSylvesterSolutionRect m n A T C X) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
        (fun i => X i k) =
      fun i => C i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  funext i
  rw [sylvester_column_identity_of_zero_below m n A T X k hbelow i, hX i k]

/-- Singleton-column existence bridge for the quasi-Schur traversal: if a
    column has the local zero-below property, the shifted coefficient is
    nonsingular, and the candidate column is assigned by the nonsingular
    inverse recurrence, then that candidate column satisfies the Sylvester
    equation. -/
theorem sylvester_singleton_column_solution_of_nonsingInv_zero_below
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (k : Fin n)
    (hbelow : forall j : Fin n, k < j -> T j k = 0)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    (hXk : forall i : Fin m,
      X i k =
        Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m A (T k k)))
          (fun i => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => T j k * X i j)) i) :
    forall i : Fin m, sylvesterOpRect m n A T X i k = C i k := by
  let M : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T k k)
  let rhs : Fin m -> Real := fun i => C i k +
    Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
      (fun j => T j k * X i j)
  have hRight : M * Inv.inv M = 1 := by
    dsimp [M]
    exact Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hdet)
  have hXvec : (fun i : Fin m => X i k) =
      Matrix.mulVec (Inv.inv M) rhs := by
    funext i
    dsimp [M, rhs]
    exact hXk i
  have hMX : Matrix.mulVec M (fun i : Fin m => X i k) = rhs := by
    rw [hXvec, Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]
  intro i
  have hid :=
    sylvester_column_identity_of_zero_below m n A T X k hbelow i
  have hrow := congrFun hMX i
  dsimp [M, rhs] at hid hrow
  rw [hid] at hrow
  linarith

/-- Source-facing singleton real-quasi-Schur existence wrapper: a singleton
    block-map column supplies the local zero-below-column fact, so the
    nonsingular-inverse one-column update satisfies the corresponding
    Sylvester column equation. -/
theorem sylvester_quasiSchur_singleton_column_solution_of_nonsingInv
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (k : Fin n)
    (hmono : Monotone pmap)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hnext : forall q : Fin n, q.val = k.val + 1 -> Not (pmap k = pmap q))
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    (hXk : forall i : Fin m,
      X i k =
        Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m A (T k k)))
          (fun i => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => T j k * X i j)) i) :
    forall i : Fin m, sylvesterOpRect m n A T X i k = C i k := by
  have hbelow : forall j : Fin n, k < j -> T j k = 0 :=
    quasiSchur_zero_below_of_singleton_successor
      n T pmap k hmono hzero hnext
  exact
    sylvester_singleton_column_solution_of_nonsingInv_zero_below
      m n A T C X k hbelow hdet hXk


































































































/-- Singleton-column solve/uniqueness bridge for the quasi-Schur traversal:
    if column `k` has the local zero-below property, the shifted coefficient is
    nonsingular, and `X(:,k)` is computed by the nonsingular inverse recurrence
    from previously solved columns, then it agrees with any exact solution `Y`
    once all earlier columns agree. -/
theorem sylvester_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (k : Fin n)
    (hbelow : forall j : Fin n, k < j -> T j k = 0)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    (hXk : forall i : Fin m,
      X i k =
        Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m A (T k k)))
          (fun i => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => T j k * X i j)) i)
    (hYsol : IsSylvesterSolutionRect m n A T C Y)
    (hprev : forall j : Fin n, j < k -> forall i : Fin m, X i j = Y i j) :
    forall i : Fin m, X i k = Y i k := by
  let M : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T k k)
  let rhsX : Fin m -> Real := fun i => C i k +
    Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
      (fun j => T j k * X i j)
  let rhsY : Fin m -> Real := fun i => C i k +
    Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
      (fun j => T j k * Y i j)
  have hRight : M * Inv.inv M = 1 := by
    dsimp [M]
    exact Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hdet)
  have hXvec : (fun i : Fin m => X i k) =
      Matrix.mulVec (Inv.inv M) rhsX := by
    funext i
    dsimp [M, rhsX]
    exact hXk i
  have hMX : Matrix.mulVec M (fun i : Fin m => X i k) = rhsX := by
    rw [hXvec, Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]
  have hMY : Matrix.mulVec M (fun i : Fin m => Y i k) = rhsY := by
    dsimp [M, rhsY]
    exact sylvester_column_equation_of_solution_zero_below
      m n A T C Y k hbelow hYsol
  have hrhs : rhsX = rhsY := by
    dsimp [rhsX, rhsY]
    exact sylvester_singleton_column_rhs_eq_of_prev_columns_eq
      m n T C X Y k hprev
  have hmul :
      Matrix.mulVec M (fun i : Fin m => X i k) =
        Matrix.mulVec M (fun i : Fin m => Y i k) := by
    rw [hMX, hMY]
    exact hrhs
  have hcol : (fun i : Fin m => X i k) = (fun i : Fin m => Y i k) :=
    mulVec_injective_of_det_ne_zero hdet hmul
  intro i
  exact congrFun hcol i

/-- Source-facing singleton real-quasi-Schur recurrence wrapper: a singleton
    block-map column supplies the local zero-below-column fact, so the
    nonsingular-inverse one-column update agrees with any exact solution after
    all earlier columns agree.  This is the singleton companion to the
    solution-facing adjacent two-column recurrence wrapper. -/
theorem sylvester_quasiSchur_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (k : Fin n)
    (hmono : Monotone pmap)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hnext : forall q : Fin n, q.val = k.val + 1 -> pmap k ≠ pmap q)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    (hXk : forall i : Fin m,
      X i k =
        Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m A (T k k)))
          (fun i => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => T j k * X i j)) i)
    (hYsol : IsSylvesterSolutionRect m n A T C Y)
    (hprev : forall j : Fin n, j < k -> forall i : Fin m, X i j = Y i j) :
    forall i : Fin m, X i k = Y i k := by
  have hbelow : forall j : Fin n, k < j -> T j k = 0 :=
    quasiSchur_zero_below_of_singleton_successor
      n T pmap k hmono hzero hnext
  exact
    sylvester_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq
      m n A T C X Y k hbelow hdet hXk hYsol hprev

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for the singleton zero-below column identity. -/
alias H16_eq16_6_sylvester_column_identity_of_zero_below :=
  sylvester_column_identity_of_zero_below

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for extracting the singleton column recurrence from
    an exact solution under the zero-below hypothesis. -/
alias H16_eq16_6_sylvester_column_equation_of_solution_zero_below :=
  sylvester_column_equation_of_solution_zero_below

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for the zero-below singleton nonsingular-inverse
    solution bridge. -/
alias H16_eq16_6_sylvester_singleton_column_solution_of_nonsingInv_zero_below :=
  sylvester_singleton_column_solution_of_nonsingInv_zero_below

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the quasi-Schur singleton nonsingular-inverse
    solution bridge. -/
alias H16_eq16_4_8_sylvester_quasiSchur_singleton_column_solution_of_nonsingInv :=
  sylvester_quasiSchur_singleton_column_solution_of_nonsingInv

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for singleton nonsingular-inverse column uniqueness
    from previous-column agreement. -/
alias H16_eq16_6_sylvester_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq :=
  sylvester_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the quasi-Schur singleton column uniqueness
    bridge from previous-column agreement. -/
alias H16_eq16_4_8_sylvester_quasiSchur_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq :=
  sylvester_quasiSchur_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    quasi-Schur traversal uniqueness skeleton: if every column of a supplied
    candidate `X` is covered either by the singleton one-column recurrence or
    by an adjacent same-block two-column recurrence, then `X` agrees with any
    exact Schur-coordinate solution `Y`.

    This is intentionally a step-oracle theorem, not an executable
    Bartels-Stewart traversal: it assembles the already proved local singleton
    and two-column recurrence uniqueness facts into the prefix induction that
    a later algorithmic traversal can instantiate. -/
theorem sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_step_oracle
    (m n : Nat)
    (U R Aorig : RMatFn m m) (V S Borig : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : Aorig = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : Borig = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex Aorig)
        (realMatrixToComplex Borig))
    (hstep : forall k : Fin n,
      ((forall q : Fin n, q.val = k.val + 1 -> pmap k ≠ pmap q) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0) /\
        (forall i : Fin m,
          X i k =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S k k)))
              (fun i => C i k +
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => S j k * X i j)) i)) \/
      (exists p q : Fin n,
        q.val = p.val + 1 /\
        pmap p = pmap q /\
        (k = p \/ k = q) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))))
    (hYsol : IsSylvesterSolutionRect m n R S C Y) :
    X = Y := by
  have hcol : forall N : Nat, forall k : Fin n, k.val < N ->
      forall i : Fin m, X i k = Y i k := by
    intro N
    induction N with
    | zero =>
        intro k hk
        exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        intro k hk
        by_cases hlt : k.val < N
        · exact ih k hlt
        · have hkN : k.val = N := by omega
          rcases hstep k with hsingle | hblock
          · rcases hsingle with ⟨hnext, hdet, hXk⟩
            have hprev : forall j : Fin n, j < k -> forall i : Fin m,
                X i j = Y i j := by
              intro j hjk
              have hjN : j.val < N := by
                have hjkNat : j.val < k.val := Fin.lt_def.mp hjk
                omega
              exact ih j hjN
            exact
              sylvester_quasiSchur_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq
                m n R S C X Y pmap k hmono hzero hnext hdet hXk hYsol hprev
          · rcases hblock with ⟨p, q, hpq_adj, hsame, hkblock, hXp, hXq⟩
            have hprev : forall j : Fin n, j < p -> forall i : Fin m,
                X i j = Y i j := by
              intro j hjp
              have hjN : j.val < N := by
                rcases hkblock with hkleft | hkright
                · have hjpNat : j.val < p.val := Fin.lt_def.mp hjp
                  have hpval : p.val = N := by
                    rw [← hkN]
                    exact congrArg Fin.val hkleft.symm
                  omega
                · have hjpNat : j.val < p.val := Fin.lt_def.mp hjp
                  have hqval : q.val = N := by
                    rw [← hkN]
                    exact congrArg Fin.val hkright.symm
                  omega
              exact ih j hjN
            have hcols :=
              sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left_of_solution_prev_columns_eq
                m n U R Aorig V S Borig C X Y pmap p q
                hU hV hA hB hmono hcard hzero hpq_adj hsame hspectral hnoOrig
                hXp hXq hYsol hprev
            intro i
            rcases hkblock with hkleft | hkright
            · subst k
              exact hcols.1 i
            · subst k
              exact hcols.2 i
  funext i k
  exact hcol n k k.isLt i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), scheduled
    quasi-Schur traversal uniqueness skeleton with determinant certificates:
    if a frontier schedule starts at column `0`, ends at `n`, and each step is
    justified either by the singleton recurrence or by an adjacent same-block
    two-column determinant solve, then the scheduled candidate `X` agrees with
    any exact Schur-coordinate solution `Y`.

    This is the determinant-only companion to the global real-Schur
    step-oracle theorem above.  It carries only the local nonsingularity
    certificate needed by the two-column block solve; separate adapters may
    manufacture that certificate from spectral or original-factor hypotheses. -/
theorem sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_det_frontier_step_oracle
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))))
    (hYsol : IsSylvesterSolutionRect m n R S C Y) :
    X = Y := by
  let Prefix : Nat -> Prop := fun t =>
    forall k : Fin n, k.val < frontier t -> forall i : Fin m, X i k = Y i k
  have hprefix : forall t : Nat, t <= r -> Prefix t := by
    intro t
    induction t with
    | zero =>
        intro _ k hk
        rw [hstart] at hk
        exact absurd hk (Nat.not_lt_zero _)
    | succ t ih =>
        intro ht k hk
        have htlt : t < r := Nat.lt_of_succ_le ht
        have ihprefix : Prefix t := ih (Nat.le_of_succ_le ht)
        rcases hstep t htlt with hsingle | hblock
        · rcases hsingle with ⟨p, hpval, hfront, hnext, hdet, hXp⟩
          by_cases hdone : k.val < frontier t
          · exact ihprefix k hdone
          · have hk_succ : k.val < frontier (t + 1) := by
              simpa [Nat.succ_eq_add_one] using hk
            rw [hfront] at hk_succ
            have hkval : k.val = frontier t := by omega
            have hk_eq_p : k = p := by
              apply Fin.ext
              omega
            subst k
            have hprev : forall j : Fin n, j < p -> forall i : Fin m,
                X i j = Y i j := by
              intro j hjp
              have hjpNat : j.val < p.val := Fin.lt_def.mp hjp
              have hjold : j.val < frontier t := by omega
              exact ihprefix j hjold
            exact
              sylvester_quasiSchur_singleton_column_eq_of_nonsingInv_of_solution_prev_columns_eq
                m n R S C X Y pmap p hmono hzero hnext hdet hXp hYsol hprev
        · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame, hdet, hXp, hXq⟩
          by_cases hdone : k.val < frontier t
          · exact ihprefix k hdone
          · have hk_succ : k.val < frontier (t + 1) := by
              simpa [Nat.succ_eq_add_one] using hk
            rw [hfront] at hk_succ
            have hkcases : k.val = frontier t \/ k.val = frontier t + 1 := by omega
            have hpq_adj : q.val = p.val + 1 := by omega
            have hblockAdj : IsAdjacentQuasiTriangularBlockFn n S p q :=
              IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
                n S pmap p q hmono hcard hzero hpq_adj hsame
            have hYblock : IsSylvesterTwoColumnBlockSystem m n R S C Y p q :=
              sylvester_quasiTriangular_two_column_block_system_of_solution
                m n R S C Y p q hblockAdj hYsol
            have hprev : forall j : Fin n, j < p -> forall i : Fin m,
                X i j = Y i j := by
              intro j hjp
              have hjpNat : j.val < p.val := Fin.lt_def.mp hjp
              have hjold : j.val < frontier t := by omega
              exact ihprefix j hjold
            have hcols :=
              sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
                m n R S C X Y p q hdet hXp hXq hYblock hprev
            rcases hkcases with hkp | hkq
            · have hk_eq_p : k = p := by
                apply Fin.ext
                omega
              subst k
              exact hcols.1
            · have hk_eq_q : k = q := by
                apply Fin.ext
                omega
              subst k
              exact hcols.2
  have hfinal : Prefix r := hprefix r (le_rfl)
  funext i k
  exact hfinal k (by simpa [hend] using k.isLt) i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), scheduled
    quasi-Schur traversal uniqueness skeleton with product-shift determinant
    certificates for adjacent two-column blocks.  The singleton steps use the
    usual shifted coefficient determinant; each two-column step supplies the
    product-shift determinant
    `(R - s_qq I) (R - s_pp I) - s_qp s_pq I`, which is converted internally
    to nonsingularity of the active two-column block coefficient.

    This is a certificate adapter for the real `2 x 2` block route, not a
    proof that the product-shift determinant follows automatically from
    rounded Schur arithmetic or from a generated schedule. -/
theorem sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_product_shift_det_frontier_step_oracle
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det
          (sylvesterTriangularShiftedCoeff m R (S q q) *
              sylvesterTriangularShiftedCoeff m R (S p p) -
            Matrix.scalar (Fin m) (S q p * S p q)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))))
    (hYsol : IsSylvesterSolutionRect m n R S C Y) :
    X = Y := by
  apply
    sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_det_frontier_step_oracle
      m n r R S C X Y pmap frontier hstart hend hmono hcard hzero ?_ hYsol
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hprod, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    exact
      sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_det_ne_zero
        m n R S p q hprod

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the global real-Schur traversal uniqueness
    step-oracle skeleton. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_step_oracle :=
  sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the determinant-certified scheduled traversal
    uniqueness skeleton. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_det_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the product-shift determinant scheduled
    traversal uniqueness skeleton. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_product_shift_det_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_product_shift_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), scheduled
    quasi-Schur traversal existence skeleton with determinant certificates:
    if a frontier schedule starts at column `0`, ends at `n`, and each step is
    justified by either the singleton inverse recurrence or an adjacent
    two-column determinant solve, then the scheduled candidate itself solves
    the transformed Sylvester equation.

    This is exact supplied-factor algebra. It does not assert rounded
    Bartels-Stewart arithmetic, automatic schedule generation, or LAPACK-style
    estimator bounds. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))) :
    IsSylvesterSolutionRect m n R S C X := by
  let Prefix : Nat -> Prop := fun t =>
    forall k : Fin n, k.val < frontier t ->
      forall i : Fin m, sylvesterOpRect m n R S X i k = C i k
  have hprefix : forall t : Nat, t <= r -> Prefix t := by
    intro t
    induction t with
    | zero =>
        intro _ k hk
        rw [hstart] at hk
        exact absurd hk (Nat.not_lt_zero _)
    | succ t ih =>
        intro ht k hk
        have htlt : t < r := Nat.lt_of_succ_le ht
        have ihprefix : Prefix t := ih (Nat.le_of_succ_le ht)
        rcases hstep t htlt with hsingle | hblock
        · rcases hsingle with ⟨p, hpval, hfront, hnext, hdet, hXp⟩
          by_cases hdone : k.val < frontier t
          · exact ihprefix k hdone
          · have hk_succ : k.val < frontier (t + 1) := by
              simpa [Nat.succ_eq_add_one] using hk
            rw [hfront] at hk_succ
            have hkval : k.val = frontier t := by omega
            have hk_eq_p : k = p := by
              apply Fin.ext
              omega
            subst k
            exact
              sylvester_quasiSchur_singleton_column_solution_of_nonsingInv
                m n R S C X pmap p hmono hzero hnext hdet hXp
        · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame, hdet, hXp, hXq⟩
          by_cases hdone : k.val < frontier t
          · exact ihprefix k hdone
          · have hk_succ : k.val < frontier (t + 1) := by
              simpa [Nat.succ_eq_add_one] using hk
            rw [hfront] at hk_succ
            have hkcases : k.val = frontier t \/ k.val = frontier t + 1 := by omega
            have hpq_adj : q.val = p.val + 1 := by omega
            have hblockAdj : IsAdjacentQuasiTriangularBlockFn n S p q :=
              IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
                n S pmap p q hmono hcard hzero hpq_adj hsame
            have hXblock : IsSylvesterTwoColumnBlockSystem m n R S C X p q :=
              sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
                m n R S C X p q hdet hXp hXq
            have hcols :=
              sylvester_quasiTriangular_solution_columns_of_two_column_block_system
                m n R S C X p q hblockAdj hXblock
            rcases hkcases with hkp | hkq
            · have hk_eq_p : k = p := by
                apply Fin.ext
                omega
              subst k
              exact hcols.1
            · have hk_eq_q : k = q := by
                apply Fin.ext
                omega
              subst k
              exact hcols.2
  have hfinal : Prefix r := hprefix r (le_rfl)
  intro i k
  exact hfinal k (by simpa [hend] using k.isLt) i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from a scheduled quasi-Schur traversal:
    if the Schur-coordinate candidate `X` satisfies the determinant-certified
    frontier traversal for the transformed right-hand side `Cschur`, then its
    reconstruction `U*X*V^T` agrees with any original-coordinate exact solution.

    This is still an exact-arithmetic schedule/certificate theorem.  It does
    not claim rounded Bartels-Stewart arithmetic, automatic schedule
    generation, or LAPACK-style estimator bounds. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  let Yschur : RMatFn m n :=
    rectMatMul (matTranspose U) (rectMatMul Yorig V)
  have hYexpand :
      rectMatMul U (rectMatMul Yschur (matTranspose V)) = Yorig := by
    dsimp [Yschur]
    exact rectMatMul_schur_coords_expand U V Yorig hU hV
  have hYorig_as_reconstructed :
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul Yschur (matTranspose V))) := by
    rw [hYexpand]
    exact hYorig
  have hYschur_transformed :
      IsSylvesterSolutionRect m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) Yschur :=
    (sylvester_schur_transform_solution_iff m n U R A V S B C Yschur
      hU hV hA hB).mp hYorig_as_reconstructed
  have hYschur :
      IsSylvesterSolutionRect m n R S Cschur Yschur := by
    rw [hCschur]
    exact hYschur_transformed
  have hXY :
      X = Yschur :=
    sylvester_quasiSchur_blockTraversal_columns_eq_of_solution_det_frontier_step_oracle
      m n r R S Cschur X Yschur pmap frontier
      hstart hend hmono hcard hzero hstep hYschur
  calc
    rectMatMul U (rectMatMul X (matTranspose V))
        = rectMatMul U (rectMatMul Yschur (matTranspose V)) := by
            rw [hXY]
    _ = Yorig := hYexpand

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from a scheduled determinant-
    certified quasi-Schur traversal.  The Schur-coordinate witness is the
    supplied candidate `X`, reconstructed as `U*X*V^T`.

    This theorem packages the exact schedule/certificate path for the
    Bartels-Stewart recurrence. It remains a supplied-factor exact-arithmetic
    statement: no rounded Schur solve, automatic schedule construction, or
    LAPACK-style estimator is asserted. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  let Xorig : RMatFn m n := rectMatMul U (rectMatMul X (matTranspose V))
  have hXschur :
      IsSylvesterSolutionRect m n R S Cschur X :=
    sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle
      m n r R S Cschur X pmap frontier
      hstart hend hmono hcard hzero hstep
  refine ⟨Xorig, ?_, ?_⟩
  · have hXtrans :
        IsSylvesterSolutionRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) X := by
      rw [← hCschur]
      exact hXschur
    dsimp [Xorig]
    exact
      (sylvester_schur_transform_solution_iff m n
        U R A V S B C X hU hV hA hB).mpr hXtrans
  · intro Yorig hYorig
    have hEq :
        Xorig = Yorig := by
      dsimp [Xorig]
      exact
        sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle
          m n r U R A V S B C Cschur X Yorig pmap frontier
          hU hV hA hB hCschur hstart hend hmono hcard hzero hstep hYorig
    exact hEq.symm

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), product-shift
    determinant adapter for scheduled quasi-Schur traversal exact solvability:
    each adjacent two-column step may supply the product-shift determinant
    certificate instead of the full two-column block determinant certificate. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_product_shift_det_frontier_step_oracle
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det
          (sylvesterTriangularShiftedCoeff m R (S q q) *
              sylvesterTriangularShiftedCoeff m R (S p p) -
            Matrix.scalar (Fin m) (S q p * S p q)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))) :
    IsSylvesterSolutionRect m n R S C X := by
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle
      m n r R S C X pmap frontier hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hprod, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    exact
      sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_det_ne_zero
        m n R S p q hprod

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), product-shift
    determinant adapter for original-coordinate reconstruction from a
    scheduled quasi-Schur traversal.  The adjacent two-column steps supply the
    product-shift determinant certificate, which is converted internally to the
    full two-column block determinant certificate used by the determinant
    frontier theorem. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_product_shift_det_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det
          (sylvesterTriangularShiftedCoeff m R (S q q) *
              sylvesterTriangularShiftedCoeff m R (S p p) -
            Matrix.scalar (Fin m) (S q p * S p q)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_ hYorig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hprod, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    exact
      sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_det_ne_zero
        m n R S p q hprod

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from a scheduled quasi-Schur
    traversal whose two-column steps carry product-shift determinant
    certificates.  This is a source-shaped certificate adapter over
    `existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle`. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_product_shift_det_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not (Matrix.det
          (sylvesterTriangularShiftedCoeff m R (S q q) *
              sylvesterTriangularShiftedCoeff m R (S p p) -
            Matrix.scalar (Fin m) (S q p * S p q)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hprod, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    exact
      sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_det_ne_zero
        m n R S p q hprod

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled quasi-Schur Schur-coordinate
    solvability from explicit singleton and two-column determinant steps. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate reconstruction from a
    scheduled determinant-certified quasi-Schur traversal. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate unique solvability from a
    scheduled determinant-certified quasi-Schur traversal. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled quasi-Schur Schur-coordinate
    solvability from product-shift two-column determinant steps. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_product_shift_det_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_product_shift_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate reconstruction from a
    product-shift determinant scheduled quasi-Schur traversal. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_product_shift_det_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_product_shift_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate unique solvability from a
    product-shift determinant scheduled quasi-Schur traversal. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_product_shift_det_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_product_shift_det_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from a scheduled quasi-Schur traversal whose
    same-block two-column steps use the real-Schur two-block spectral
    certificate plus a supplied shifted determinant separation for the
    constructed complex block root. Singleton steps still carry explicit
    shifted determinant certificates. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_det_separation_frontier_step_oracle
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not
          ((Matrix.det
            (realMatrixToComplex (Matrix.of R) -
              Matrix.scalar (Fin m)
                (sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                  (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))))) = 0)) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))) :
    IsSylvesterSolutionRect m n R S C X := by
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle
      m n r R S C X pmap frontier hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hdetA, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    have hpq_adj : q.val = p.val + 1 := by omega
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
        m n R S pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from a scheduled quasi-Schur traversal
    whose same-block two-column steps use real-Schur two-block spectral data
    plus supplied shifted determinant separation. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_det_separation_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not
          ((Matrix.det
            (realMatrixToComplex (Matrix.of R) -
              Matrix.scalar (Fin m)
                (sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                  (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))))) = 0)) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_ hYorig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hdetA, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    have hpq_adj : q.val = p.val + 1 := by omega
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
        m n R S pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from a scheduled quasi-Schur
    traversal whose same-block two-column steps use real-Schur two-block
    spectral data plus supplied shifted determinant separation. Singleton
    steps still carry explicit shifted determinant certificates. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_det_separation_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        Not
          ((Matrix.det
            (realMatrixToComplex (Matrix.of R) -
              Matrix.scalar (Fin m)
                (sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                  (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))))) = 0)) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hdetA, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    have hpq_adj : q.val = p.val + 1 := by omega
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
        m n R S pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from a scheduled quasi-Schur traversal whose
    same-block two-column steps supply the bundled real-quasi-Schur block
    separation certificate. Singleton steps still carry explicit shifted
    determinant certificates. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_frontier_step_oracle
    (m n r : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))) :
    IsSylvesterSolutionRect m n R S C X := by
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle
      m n r R S C X pmap frontier hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hsep, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
        m n R S pmap p q hsep).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from a scheduled quasi-Schur traversal
    whose same-block two-column steps supply the bundled real-quasi-Schur
    block separation certificate. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_block_separation_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_ hYorig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hsep, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
        m n R S pmap p q hsep).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from a scheduled quasi-Schur
    traversal whose same-block two-column steps supply the bundled
    real-quasi-Schur block separation certificate. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_block_separation_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hsep, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
        m n R S pmap p q hsep).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from a scheduled quasi-Schur traversal whose
    same-block two-column steps use the supplied real-Schur two-block spectral
    certificate plus the original-coordinate no-common-complex-right-eigenvalue
    hypothesis. Singleton steps still carry explicit shifted determinant
    certificates. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))) :
    IsSylvesterSolutionRect m n R S C X := by
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle
      m n r R S C X pmap frontier hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    have hpq_adj : q.val = p.val + 1 := by omega
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
        m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero
        hpq_adj hsame hspectral hnoOrig).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from a scheduled quasi-Schur traversal
    whose same-block two-column steps use supplied real-Schur two-block
    spectral data plus original-coordinate no-common-complex-right-eigenvalue
    data. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_ hYorig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    have hpq_adj : q.val = p.val + 1 := by omega
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
        m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero
        hpq_adj hsame hspectral hnoOrig).2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from a scheduled quasi-Schur
    traversal whose same-block two-column steps use the supplied real-Schur
    two-block spectral certificate plus the original-coordinate
    no-common-complex-right-eigenvalue hypothesis.  Singleton steps still
    carry explicit shifted determinant certificates. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) /\
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · exact Or.inl hsingle
  · rcases hblock with
      ⟨p, q, hpval, hqval, hfront, hsame, hXp, hXq⟩
    refine Or.inr ⟨p, q, hpval, hqval, hfront, hsame, ?_, hXp, hXq⟩
    have hpq_adj : q.val = p.val + 1 := by omega
    exact
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
        m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero
        hpq_adj hsame hspectral hnoOrig).2









































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from the generated quasi-Schur frontier
    schedule.  Singleton shifted determinant certificates and same-block
    shifted determinant separation certificates remain explicit mathematical
    hypotheses. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_det_separation_generated_frontier_step_oracle
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_det : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      ¬
        (Matrix.det
          (realMatrixToComplex (Matrix.of R) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))))) = 0))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_det_separation_frontier_step_oracle
      m n r R S C X pmap frontier hstart hend hmono hcard hzero hspectral
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    exact Or.inl
      ⟨p, hpval, hfront, hnext,
        hsingle_det p hprev hnext, hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr
      ⟨p, q, hpval, hqval, hfront, hsame,
        hblock_det p q hpq hsame, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from the generated quasi-Schur frontier
    schedule under explicit determinant-separation certificates. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_det_separation_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_det : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      ¬
        (Matrix.det
          (realMatrixToComplex (Matrix.of R) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))))) = 0))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_det_separation_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral
  · intro t ht
    rcases hstep t ht with hsingle | hblock
    · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
      exact Or.inl
        ⟨p, hpval, hfront, hnext,
          hsingle_det p hprev hnext, hXsingle p hprev hnext⟩
    · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
      have hpq : q.val = p.val + 1 := by omega
      rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
      exact Or.inr
        ⟨p, q, hpval, hqval, hfront, hsame,
          hblock_det p q hpq hsame, hXp, hXq⟩
  · exact hYorig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from the generated quasi-Schur
    frontier schedule under explicit determinant-separation certificates. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_det_separation_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_det : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      ¬
        (Matrix.det
          (realMatrixToComplex (Matrix.of R) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))))) = 0))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_det_separation_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    exact Or.inl
      ⟨p, hpval, hfront, hnext,
        hsingle_det p hprev hnext, hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr
      ⟨p, q, hpval, hqval, hfront, hsame,
        hblock_det p q hpq hsame, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier Schur-coordinate traversal
    from explicit determinant-separation certificates. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_det_separation_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_det_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate
    reconstruction from explicit determinant-separation certificates. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_det_separation_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_det_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate unique
    solvability from explicit determinant-separation certificates. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_det_separation_generated_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_det_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from the generated quasi-Schur frontier
    schedule when same-block two-column steps supply the bundled real-quasi-Schur
    block-separation predicate. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_generated_frontier_step_oracle
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_sep : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_frontier_step_oracle
      m n r R S C X pmap frontier hstart hend hmono hcard hzero
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    exact Or.inl
      ⟨p, hpval, hfront, hnext,
        hsingle_det p hprev hnext, hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr
      ⟨p, q, hpval, hqval, hfront, hsame,
        hblock_sep p q hpq hsame, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from the generated quasi-Schur frontier
    schedule under bundled real-quasi-Schur block-separation certificates. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_block_separation_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_sep : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_block_separation_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero
  · intro t ht
    rcases hstep t ht with hsingle | hblock
    · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
      exact Or.inl
        ⟨p, hpval, hfront, hnext,
          hsingle_det p hprev hnext, hXsingle p hprev hnext⟩
    · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
      have hpq : q.val = p.val + 1 := by omega
      rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
      exact Or.inr
        ⟨p, q, hpval, hqval, hfront, hsame,
          hblock_sep p q hpq hsame, hXp, hXq⟩
  · exact hYorig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from the generated quasi-Schur
    frontier schedule under bundled real-quasi-Schur block-separation
    certificates. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_block_separation_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_sep : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n R S pmap p q)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_block_separation_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    exact Or.inl
      ⟨p, hpval, hfront, hnext,
        hsingle_det p hprev hnext, hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr
      ⟨p, q, hpval, hqval, hfront, hsame,
        hblock_sep p q hpq hsame, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier Schur-coordinate traversal
    from bundled real-quasi-Schur block-separation certificates. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate
    reconstruction from bundled real-quasi-Schur block-separation certificates. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_block_separation_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_block_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate unique
    solvability from bundled real-quasi-Schur block-separation certificates. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_block_separation_generated_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_block_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from the generated quasi-Schur frontier
    schedule under two-block spectral data and explicit exclusion of each
    adjacent block's constructed complex root from `R`. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_noA : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))) :
    IsSylvesterSolutionRect m n R S C X := by
  exact
    sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_generated_frontier_step_oracle
      m n R S C X pmap hmono hcard hzero hsingle_det hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_complex_root_separation
          m n R S pmap p q hmono hcard hzero hpq hsame hspectral
          (hblock_noA p q hpq hsame))
      hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from the generated quasi-Schur frontier
    schedule under two-block spectral data and explicit constructed-root
    exclusions. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_noA : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  exact
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_block_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X Yorig pmap
      hU hV hA hB hCschur hmono hcard hzero hsingle_det hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_complex_root_separation
          m n R S pmap p q hmono hcard hzero hpq hsame hspectral
          (hblock_noA p q hpq hsame))
      hXblock hYorig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from the generated quasi-Schur
    frontier schedule under two-block spectral data and explicit
    constructed-root exclusions. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_noA : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_block_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X pmap
      hU hV hA hB hCschur hmono hcard hzero hsingle_det hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_complex_root_separation
          m n R S pmap p q hmono hcard hzero hpq hsame hspectral
          (hblock_noA p q hpq hsame))
      hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier Schur-coordinate traversal
    from constructed adjacent-block complex-root exclusions. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate
    reconstruction from constructed adjacent-block complex-root exclusions. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate unique
    solvability from constructed adjacent-block complex-root exclusions. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from the generated quasi-Schur frontier
    schedule when each adjacent two-column block has a local no-common
    certificate with the left Schur factor. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q)))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))) :
    IsSylvesterSolutionRect m n R S C X := by
  exact
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
      m n R S C X pmap hmono hcard hzero hspectral hsingle_det hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealSchurBlockComplexRoot_no_eigenpair_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
          m n R S pmap p q hpq hsame hspectral
          (hblock_noCommon p q hpq hsame))
      hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from generated frontier schedules and
    per-block local no-common certificates. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q)))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  exact
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X Yorig pmap hU hV hA hB hCschur
      hmono hcard hzero hspectral hsingle_det hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealSchurBlockComplexRoot_no_eigenpair_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
          m n R S pmap p q hpq hsame hspectral
          (hblock_noCommon p q hpq hsame))
      hXblock hYorig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from generated frontier schedules
    and per-block local no-common certificates. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q)))
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X pmap hU hV hA hB hCschur hmono hcard
      hzero hspectral hsingle_det hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealSchurBlockComplexRoot_no_eigenpair_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
          m n R S pmap p q hpq hsame hspectral
          (hblock_noCommon p q hpq hsame))
      hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier Schur-coordinate traversal
    from per-block local no-common certificates. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate
    reconstruction from per-block local no-common certificates. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate unique
    solvability from per-block local no-common certificates. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from the generated quasi-Schur frontier
    schedule.  A single global vec/Kronecker determinant nonsingularity
    certificate supplies the singleton shifted determinants and same-block
    two-column block determinants internally; the candidate `X` recurrence
    formulas remain explicit oracle hypotheses. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_vecCoeff_det_ne_zero_generated_frontier_step_oracle
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetGlobal : Not (Matrix.det (sylvesterVecCoeff m n R S) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_det_frontier_step_oracle
      m n r R S C X pmap frontier hstart hend hmono hcard hzero
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    have hsingleFiber : forall i : Fin n, pmap i = pmap p -> i = p :=
      quasiSchur_singleton_fiber_of_prev_next_not_same
        n pmap p hmono hprev hnext
    exact Or.inl
      ⟨p, hpval, hfront, hnext,
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_vecCoeff_det_ne_zero
          m n R S pmap p hzero hsingleFiber hdetGlobal,
        hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    have hblock_det :
        Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) :=
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_global_vecCoeff_det_ne_zero
        m n R S pmap p q hmono hcard hzero hpq hsame hspectral hdetGlobal).2
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr
      ⟨p, q, hpval, hqval, hfront, hsame, hblock_det, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from the generated quasi-Schur
    frontier schedule.  The original-coordinate vec/Kronecker determinant
    nonsingularity is transported through the supplied real Schur factors to
    produce the local singleton and same-block determinant certificates. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_det_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero
  · intro t ht
    rcases hstep t ht with hsingle | hblock
    · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
      have hsingleFiber : forall i : Fin n, pmap i = pmap p -> i = p :=
        quasiSchur_singleton_fiber_of_prev_next_not_same
          n pmap p hmono hprev hnext
      exact Or.inl
        ⟨p, hpval, hfront, hnext,
          sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero
            m n U R A V S B pmap p hU hV hA hB hzero hsingleFiber hdetOrig,
          hXsingle p hprev hnext⟩
    · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
      have hpq : q.val = p.val + 1 := by omega
      have hblock_det :
          Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) :=
        (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_vecCoeff_det_ne_zero
          m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero hpq hsame
          hspectral hdetOrig).2
      rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
      exact Or.inr
        ⟨p, q, hpval, hqval, hfront, hsame, hblock_det, hXp, hXq⟩
  · exact hYorig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from the generated quasi-Schur
    frontier schedule.  The only determinant certificate exposed to callers is
    nonsingularity of the original vec/Kronecker Sylvester coefficient; local
    shifted and two-column block determinants are derived internally. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_det_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    have hsingleFiber : forall i : Fin n, pmap i = pmap p -> i = p :=
      quasiSchur_singleton_fiber_of_prev_next_not_same
        n pmap p hmono hprev hnext
    exact Or.inl
      ⟨p, hpval, hfront, hnext,
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero
          m n U R A V S B pmap p hU hV hA hB hzero hsingleFiber hdetOrig,
        hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    have hblock_det :
        Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n R S p q) = 0) :=
      (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_vecCoeff_det_ne_zero
        m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero hpq hsame
        hspectral hdetOrig).2
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr
      ⟨p, q, hpval, hqval, hfront, hsame, hblock_det, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from the generated quasi-Schur frontier
    schedule.  A single global vec/Kronecker determinant certificate supplies
    singleton shifted determinants and same-block bundled real-quasi-Schur
    block-separation predicates internally. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetGlobal : Not (Matrix.det (sylvesterVecCoeff m n R S) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))) :
    IsSylvesterSolutionRect m n R S C X := by
  exact
    sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_generated_frontier_step_oracle
      m n R S C X pmap hmono hcard hzero
      (fun p hprev hnext =>
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_vecCoeff_det_ne_zero
          m n R S pmap p hzero
          (quasiSchur_singleton_fiber_of_prev_next_not_same
            n pmap p hmono hprev hnext)
          hdetGlobal)
      hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_global_vecCoeff_det_ne_zero
          m n R S pmap p q hmono hcard hzero hpq hsame hspectral hdetGlobal)
      hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from generated quasi-Schur frontiers.
    The original vec/Kronecker determinant certificate is transported through
    supplied real Schur factors into singleton shifted determinants and
    same-block bundled real-quasi-Schur block-separation predicates. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  exact
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_block_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X Yorig pmap hU hV hA hB hCschur
      hmono hcard hzero
      (fun p hprev hnext =>
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero
          m n U R A V S B pmap p hU hV hA hB hzero
          (quasiSchur_singleton_fiber_of_prev_next_not_same
            n pmap p hmono hprev hnext)
          hdetOrig)
      hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_realQuasiSchur_factors_twoBlockSpectral_global_vecCoeff_det_ne_zero
          m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero
          hpq hsame hspectral hdetOrig)
      hXblock hYorig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability through the generated quasi-Schur
    block-separation frontier route from one original vec/Kronecker determinant
    certificate. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_block_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X pmap hU hV hA hB hCschur hmono hcard hzero
      (fun p hprev hnext =>
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero
          m n U R A V S B pmap p hU hV hA hB hzero
          (quasiSchur_singleton_fiber_of_prev_next_not_same
            n pmap p hmono hprev hnext)
          hdetOrig)
      hXsingle
      (fun p q hpq hsame =>
        sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_realQuasiSchur_factors_twoBlockSpectral_global_vecCoeff_det_ne_zero
          m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero
          hpq hsame hspectral hdetOrig)
      hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for Schur-coordinate generated-frontier solvability
    through the bundled block-separation route from a vec/Kronecker determinant
    certificate. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_realQuasiSchur_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate generated-frontier
    reconstruction through the bundled block-separation route from an original
    vec/Kronecker determinant certificate. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate unique solvability through
    the bundled block-separation generated-frontier route from an original
    vec/Kronecker determinant certificate. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_block_separation_vecCoeff_det_ne_zero_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from a scheduled quasi-Schur traversal whose
    singleton steps supply true singleton-fiber data and whose same-block
    two-column steps use supplied real-Schur two-block spectral data plus the
    original-coordinate no-common-complex-right-eigenvalue hypothesis. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall i : Fin n, pmap i = pmap p -> i = p) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))) :
    IsSylvesterSolutionRect m n R S C X := by
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_frontier_step_oracle
      m n r U R A V S B C X pmap frontier
      hU hV hA hB hstart hend hmono hcard hzero hspectral hnoOrig ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hsingle, hXp⟩
    refine Or.inl ⟨p, hpval, hfront, ?_, ?_, hXp⟩
    · exact quasiSchur_singleton_successor_not_same_of_singleton_fiber
        n pmap p hsingle
    · exact
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_no_common_complex_right_eigenvalue
          m n U R A V S B pmap p hU hV hA hB hzero hsingle hnoOrig
  · exact Or.inr hblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from a scheduled quasi-Schur traversal
    whose singleton steps derive shifted determinants from true singleton
    fibers plus original-coordinate no-common spectrum. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall i : Fin n, pmap i = pmap p -> i = p) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral hnoOrig ?_
      hYorig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hsingle, hXp⟩
    refine Or.inl ⟨p, hpval, hfront, ?_, ?_, hXp⟩
    · exact quasiSchur_singleton_successor_not_same_of_singleton_fiber
        n pmap p hsingle
    · exact
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_no_common_complex_right_eigenvalue
          m n U R A V S B pmap p hU hV hA hB hzero hsingle hnoOrig
  · exact Or.inr hblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from a scheduled quasi-Schur
    traversal whose singleton shifted determinants are derived internally from
    true singleton-fiber data plus original-coordinate no-common spectrum. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_singleton_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall i : Fin n, pmap i = pmap p -> i = p) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral hnoOrig ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hsingle, hXp⟩
    refine Or.inl ⟨p, hpval, hfront, ?_, ?_, hXp⟩
    · exact quasiSchur_singleton_successor_not_same_of_singleton_fiber
        n pmap p hsingle
    · exact
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_no_common_complex_right_eigenvalue
          m n U R A V S B pmap p hU hV hA hB hzero hsingle hnoOrig
  · exact Or.inr hblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled Schur-coordinate traversal whose
    singleton steps derive shifted determinants from singleton-fiber data and
    the original-coordinate no-common-spectrum hypothesis. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled original-coordinate reconstruction
    with singleton-fiber determinant discharge from no-common spectrum. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled original-coordinate unique solvability
    with singleton-fiber determinant discharge from no-common spectrum. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_singleton_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_singleton_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from a scheduled quasi-Schur traversal whose
    singleton steps are certified by local predecessor/successor block-label
    separation.  The neighbor separation is converted internally to a true
    singleton fiber, so singleton shifted determinants are then derived from
    the no-common-spectrum hypothesis. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
        (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => C i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i)))) :
    IsSylvesterSolutionRect m n R S C X := by
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle
      m n r U R A V S B C X pmap frontier
      hU hV hA hB hstart hend hmono hcard hzero hspectral hnoOrig ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext, hXp⟩
    refine Or.inl ⟨p, hpval, hfront, ?_, hXp⟩
    exact quasiSchur_singleton_fiber_of_prev_next_not_same
      n pmap p hmono hprev hnext
  · exact Or.inr hblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from a scheduled quasi-Schur traversal
    whose singleton steps are certified by local neighbor block-label
    separation rather than by an explicitly supplied singleton fiber. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
        (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_singleton_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral hnoOrig ?_
      hYorig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext, hXp⟩
    refine Or.inl ⟨p, hpval, hfront, ?_, hXp⟩
    exact quasiSchur_singleton_fiber_of_prev_next_not_same
      n pmap p hmono hprev hnext
  · exact Or.inr hblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from a scheduled quasi-Schur
    traversal whose singleton steps are certified by local predecessor and
    successor block-label separation. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_neighbor_frontier_step_oracle
    (m n r : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat) (frontier : Nat -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hstart : frontier 0 = 0)
    (hend : frontier r = n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hstep : forall t : Nat, t < r ->
      (exists p : Fin n,
        p.val = frontier t /\
        frontier (t + 1) = frontier t + 1 /\
        (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) /\
        (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
              (fun i => Cschur i p +
                Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                  (fun j => S j p * X i j)) i))
      \/
      (exists p q : Fin n,
        p.val = frontier t /\
        q.val = frontier t + 1 /\
        frontier (t + 1) = frontier t + 2 /\
        pmap p = pmap q /\
        (forall i : Fin m,
          X i p =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
        (forall i : Fin m,
          X i q =
            Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
              (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_singleton_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral hnoOrig ?_
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext, hXp⟩
    refine Or.inl ⟨p, hpval, hfront, ?_, hXp⟩
    exact quasiSchur_singleton_fiber_of_prev_next_not_same
      n pmap p hmono hprev hnext
  · exact Or.inr hblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled Schur-coordinate traversal whose
    singleton steps use local predecessor/successor block-label separation
    before the no-common determinant discharge. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled original-coordinate reconstruction
    whose singleton steps use local neighbor block-label separation. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for scheduled original-coordinate unique solvability
    whose singleton steps use local neighbor block-label separation. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_neighbor_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_neighbor_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    Schur-coordinate solvability from the generated quasi-Schur frontier
    schedule.  The block-map schedule and neighbor certificates are produced
    internally; the candidate `X` column and two-column block recurrences remain
    explicit oracle hypotheses. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S C X p q) (Sum.inr i))) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle
      m n r U R A V S B C X pmap frontier
      hU hV hA hB hstart hend hmono hcard hzero hspectral hnoOrig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    exact Or.inl ⟨p, hpval, hfront, hprev, hnext, hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr ⟨p, q, hpval, hqval, hfront, hsame, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate reconstruction from the generated quasi-Schur frontier
    schedule.  The frontier and neighbor data are generated from the block map;
    the candidate `X` recurrences remain explicit oracle hypotheses. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i)))
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_neighbor_frontier_step_oracle
      m n r U R A V S B C Cschur X Yorig pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral hnoOrig
  · intro t ht
    rcases hstep t ht with hsingle | hblock
    · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
      exact Or.inl ⟨p, hpval, hfront, hprev, hnext, hXsingle p hprev hnext⟩
    · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
      have hpq : q.val = p.val + 1 := by omega
      rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
      exact Or.inr ⟨p, q, hpval, hqval, hfront, hsame, hXp, hXq⟩
  · exact hYorig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    original-coordinate unique solvability from the generated quasi-Schur
    frontier schedule.  The theorem removes supplied schedule and neighbor
    premises while retaining explicit candidate `X` recurrence oracles. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_frontier_step_oracle
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hXsingle : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> pmap q ≠ pmap p) ->
      (forall q : Fin n, q.val = p.val + 1 -> pmap p ≠ pmap q) ->
      forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTriangularShiftedCoeff m R (S p p)))
            (fun i => Cschur i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => S j p * X i j)) i)
    (hXblock : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      (forall i : Fin m,
        X i p =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inl i)) /\
      (forall i : Fin m,
        X i q =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n R S p q))
            (sylvesterTwoColumnBlockRhs m n S Cschur X p q) (Sum.inr i))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases quasiSchur_exists_frontier_schedule n pmap hcard with
    ⟨r, frontier, hstart, hend, _hfrontLt, hstep⟩
  apply
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_neighbor_frontier_step_oracle
      m n r U R A V S B C Cschur X pmap frontier
      hU hV hA hB hCschur hstart hend hmono hcard hzero hspectral hnoOrig
  intro t ht
  rcases hstep t ht with hsingle | hblock
  · rcases hsingle with ⟨p, hpval, hfront, hprev, hnext⟩
    exact Or.inl ⟨p, hpval, hfront, hprev, hnext, hXsingle p hprev hnext⟩
  · rcases hblock with ⟨p, q, hpval, hqval, hfront, hsame⟩
    have hpq : q.val = p.val + 1 := by omega
    rcases hXblock p q hpq hsame with ⟨hXp, hXq⟩
    exact Or.inr ⟨p, q, hpval, hqval, hfront, hsame, hXp, hXq⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier Schur-coordinate traversal
    under real-Schur two-block spectral data and original no-common spectrum. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate
    reconstruction under real-Schur two-block spectral data and no-common
    spectrum. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_generated_frontier_step_oracle :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_generated_frontier_step_oracle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-frontier original-coordinate unique
    solvability under real-Schur two-block spectral data and no-common
    spectrum. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_frontier_step_oracle :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_frontier_step_oracle






















































































































































































































































































































































































































































































































































/-- Predicate-packaged version of
    `sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_frontier_step_oracle`. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hXformula : IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_frontier_step_oracle
      m n U R A V S B C X pmap hU hV hA hB hmono hcard hzero hspectral
      hnoOrig hXsingle hXblock

/-- Predicate-packaged version of the generated-frontier original-coordinate
    reconstruction theorem. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap)
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_generated_frontier_step_oracle
      m n U R A V S B C Cschur X Yorig pmap hU hV hA hB hCschur
      hmono hcard hzero hspectral hnoOrig hXsingle hXblock hYorig

/-- Predicate-packaged version of the generated-frontier original-coordinate
    unique-solvability theorem. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_frontier_step_oracle
      m n U R A V S B C Cschur X pmap hU hV hA hB hCschur hmono hcard
      hzero hspectral hnoOrig hXsingle hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the global no-common generated-step Schur
    traversal solution wrapper. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_step_formula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the global no-common generated-step
    original-coordinate reconstruction wrapper. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_no_common_generated_step_formula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the global no-common generated-step
    original-coordinate unique-solvability wrapper. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_step_formula :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_step_formula

/-- Predicate-packaged version of
    `sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle`. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_step_formula
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noR : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i))
    (hXformula : IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
      m n R S C X pmap hmono hcard hzero hspectral hsingle_det
      hXsingle hblock_noR hXblock

/-- Predicate-packaged version of the generated-frontier complex-root
    exclusion original-coordinate reconstruction theorem. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noR : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap)
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X Yorig pmap
      hU hV hA hB hCschur hmono hcard hzero hspectral hsingle_det
      hXsingle hblock_noR hXblock hYorig

/-- Predicate-packaged version of the generated-frontier complex-root
    exclusion original-coordinate unique-solvability theorem. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noR : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_frontier_step_oracle
      m n U R A V S B C Cschur X pmap
      hU hV hA hB hCschur hmono hcard hzero hspectral hsingle_det
      hXsingle hblock_noR hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the complex-root-exclusion generated-step Schur
    traversal solution wrapper. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_step_formula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the complex-root-exclusion generated-step
    original-coordinate reconstruction wrapper. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_complex_root_separation_generated_step_formula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the complex-root-exclusion generated-step
    original-coordinate unique-solvability wrapper. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_step_formula :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_step_formula

/-- Predicate-packaged version of
    `sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle`. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_step_formula
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q)))
    (hXformula : IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle
      m n R S C X pmap hmono hcard hzero hspectral hsingle_det
      hXsingle hblock_noCommon hXblock

/-- Predicate-packaged version of the generated-frontier local no-common
    original-coordinate reconstruction theorem. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_local_no_common_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q)))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap)
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_local_no_common_generated_frontier_step_oracle
      m n U R A V S B C Cschur X Yorig pmap hU hV hA hB hCschur
      hmono hcard hzero hspectral hsingle_det hXsingle hblock_noCommon
      hXblock hYorig

/-- Predicate-packaged version of the generated-frontier local no-common
    original-coordinate unique-solvability theorem. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q)))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_frontier_step_oracle
      m n U R A V S B C Cschur X pmap hU hV hA hB hCschur hmono hcard
      hzero hspectral hsingle_det hXsingle hblock_noCommon hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the local no-common generated-step Schur
    solution wrapper. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_step_formula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the local no-common generated-step original
    reconstruction wrapper. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_local_no_common_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_twoBlockSpectral_local_no_common_generated_step_formula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the local no-common generated-step original
    unique-solvability wrapper. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_step_formula :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_step_formula

/-- Predicate-packaged version of
    `sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_vecCoeff_det_ne_zero_generated_frontier_step_oracle`. -/
theorem sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_vecCoeff_det_ne_zero_generated_step_formula
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetGlobal : Not (Matrix.det (sylvesterVecCoeff m n R S) = 0))
    (hXformula : IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap) :
    IsSylvesterSolutionRect m n R S C X := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_vecCoeff_det_ne_zero_generated_frontier_step_oracle
      m n R S C X pmap hmono hcard hzero hspectral hdetGlobal hXsingle hXblock

/-- Predicate-packaged version of the generated-frontier vec-determinant
    original-coordinate reconstruction theorem. -/
theorem sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X Yorig : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap)
    (hYorig : IsSylvesterSolutionRect m n A B C Yorig) :
    rectMatMul U (rectMatMul X (matTranspose V)) = Yorig := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_frontier_step_oracle
      m n U R A V S B C Cschur X Yorig pmap hU hV hA hB hCschur hmono hcard
      hzero hspectral hdetOrig hXsingle hXblock hYorig

/-- Predicate-packaged version of the generated-frontier vec-determinant
    original-coordinate unique-solvability theorem. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_step_formula
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Cschur X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hCschur : Cschur = rectMatMul (matTranspose U) (rectMatMul C V))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hdetOrig : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hXformula :
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S Cschur X pmap) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  rcases hXformula with ⟨hXsingle, hXblock⟩
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_frontier_step_oracle
      m n U R A V S B C Cschur X pmap hU hV hA hB hCschur hmono hcard hzero
      hspectral hdetOrig hXsingle hXblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered aliases for the global vec-determinant generated-step
    formula route through supplied real quasi-Schur factors. -/
alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_vecCoeff_det_ne_zero_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_vecCoeff_det_ne_zero_generated_step_formula

alias H16_eq16_4_8_sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_step_formula :=
  sylvester_quasiSchur_blockTraversal_original_solution_eq_of_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_step_formula

alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_step_formula :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_realQuasiSchur_factors_vecCoeff_det_ne_zero_generated_step_formula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    recursive-candidate witness: the automatically generated quasi-Schur
    frontier schedule constructs a Schur-coordinate candidate satisfying the
    generated-step formulas, and the existing spectral/no-common traversal
    theorem proves that this candidate solves the Sylvester equation. -/
theorem exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_no_common
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    exists X : RMatFn m n,
      IsSylvesterSolutionRect m n R S C X /\
        IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap := by
  rcases exists_isSylvesterQuasiSchurGeneratedStepFormula_of_quasiSchur_schedule
      m n R S C pmap hcard with ⟨X, hXformula⟩
  have hXsol :
      IsSylvesterSolutionRect m n R S C X :=
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_no_common_generated_step_formula
      m n U R A V S B C X pmap hU hV hA hB hmono hcard hzero
      hspectral hnoOrig hXformula
  exact ⟨X, hXsol, hXformula⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    exact recursive-candidate witness: the automatically scheduled recursive
    Schur-coordinate candidate satisfies the generated-step formulas for
    `C_s = U^T C V`, and reconstructs an original-coordinate Sylvester
    solution as `U X V^T`. -/
theorem exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_no_common
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    exists X : RMatFn m n,
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) := by
  obtain ⟨X, hXsol, hXformula⟩ :=
    exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_no_common
      m n U R A V S B
      (rectMatMul (matTranspose U) (rectMatMul C V)) pmap
      hU hV hA hB hmono hcard hzero hspectral hnoOrig
  refine ⟨X, hXformula, ?_⟩
  exact
    (sylvester_schur_transform_solution_iff m n
      U R A V S B C X hU hV hA hB).mpr hXsol

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    exact recursive-candidate unique solvability: the automatically scheduled
    recursive generated-step witness feeds the existing original-coordinate
    unique-solvability wrapper. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_no_common_generated_step_formula_witness
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  obtain ⟨X, hXformula, _hXorig⟩ :=
    exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_no_common
      m n U R A V S B C pmap hU hV hA hB hmono hcard hzero
      hspectral hnoOrig
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_step_formula
      m n U R A V S B C
      (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap
      hU hV hA hB rfl hmono hcard hzero hspectral hnoOrig hXformula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    recursive-candidate witness from generated frontier schedules, two-block
    spectral data, singleton shifted determinants, and explicit exclusions of
    the constructed adjacent-block complex roots from `R`. -/
theorem exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noR : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i)) :
    exists X : RMatFn m n,
      IsSylvesterSolutionRect m n R S C X /\
        IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap := by
  rcases exists_isSylvesterQuasiSchurGeneratedStepFormula_of_quasiSchur_schedule
      m n R S C pmap hcard with ⟨X, hXformula⟩
  have hXsol :
      IsSylvesterSolutionRect m n R S C X :=
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_complex_root_separation_generated_step_formula
      m n R S C X pmap hmono hcard hzero hspectral hsingle_det
      hblock_noR hXformula
  exact ⟨X, hXsol, hXformula⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    exact recursive-candidate witness under explicit constructed-root
    exclusions for the Schur-coordinate left factor. -/
theorem exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noR : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i)) :
    exists X : RMatFn m n,
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) := by
  obtain ⟨X, hXsol, hXformula⟩ :=
    exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation
      m n R S (rectMatMul (matTranspose U) (rectMatMul C V)) pmap
      hmono hcard hzero hspectral hsingle_det hblock_noR
  refine ⟨X, hXformula, ?_⟩
  exact
    (sylvester_schur_transform_solution_iff m n
      U R A V S B C X hU hV hA hB).mpr hXsol

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    exact recursive-candidate unique solvability under explicit constructed
    complex-root exclusions. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation_generated_step_formula_witness
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noR : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of R)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n S p q
                (Real.sqrt (-((S p p - S q q) ^ 2 + 4 * S p q * S q p))) *
                  y i)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  obtain ⟨X, hXformula, _hXorig⟩ :=
    exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation
      m n U R A V S B C pmap hU hV hA hB hmono hcard hzero
      hspectral hsingle_det hblock_noR
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_complex_root_separation_generated_step_formula
      m n U R A V S B C
      (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap
      hU hV hA hB rfl hmono hcard hzero hspectral hsingle_det
      hblock_noR hXformula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the no-common recursive Schur-coordinate
    generated-step witness. -/
alias H16_eq16_4_8_exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_no_common :=
  exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_no_common

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the no-common recursive original-coordinate
    generated-step witness. -/
alias H16_eq16_4_8_exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_no_common :=
  exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_no_common

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for no-common recursive generated-step unique
    solvability. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_no_common_generated_step_formula_witness :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_no_common_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the complex-root-separation recursive
    Schur-coordinate generated-step witness. -/
alias H16_eq16_4_8_exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation :=
  exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the complex-root-separation recursive
    original-coordinate generated-step witness. -/
alias H16_eq16_4_8_exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation :=
  exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for complex-root-separation recursive generated-step
    unique solvability. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation_generated_step_formula_witness :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_complex_root_separation_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    recursive-candidate witness from generated frontier schedules, two-block
    spectral data, singleton shifted determinants, and per-block local
    no-common certificates. -/
theorem exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common
    (m n : Nat)
    (R : RMatFn m m) (S : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q))) :
    exists X : RMatFn m n,
      IsSylvesterSolutionRect m n R S C X /\
        IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap := by
  rcases exists_isSylvesterQuasiSchurGeneratedStepFormula_of_quasiSchur_schedule
      m n R S C pmap hcard with ⟨X, hXformula⟩
  have hXsol :
      IsSylvesterSolutionRect m n R S C X :=
    sylvester_quasiSchur_blockTraversal_solution_of_twoBlockSpectral_local_no_common_generated_step_formula
      m n R S C X pmap hmono hcard hzero hspectral hsingle_det
      hblock_noCommon hXformula
  exact ⟨X, hXsol, hXformula⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    exact recursive-candidate witness under per-block local no-common
    certificates. -/
theorem exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q))) :
    exists X : RMatFn m n,
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) := by
  obtain ⟨X, hXsol, hXformula⟩ :=
    exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common
      m n R S (rectMatMul (matTranspose U) (rectMatMul C V)) pmap
      hmono hcard hzero hspectral hsingle_det hblock_noCommon
  refine ⟨X, hXformula, ?_⟩
  exact
    (sylvester_schur_transform_solution_iff m n
      U R A V S B C X hU hV hA hB).mpr hXsol

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    exact recursive-candidate unique solvability under per-block local
    no-common certificates. -/
theorem existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_local_no_common_generated_step_formula_witness
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hsingle_det : forall p : Fin n,
      (forall q : Fin n, q.val + 1 = p.val -> Not (pmap q = pmap p)) ->
      (forall q : Fin n, q.val = p.val + 1 -> Not (pmap p = pmap q)) ->
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0))
    (hblock_noCommon : forall p q : Fin n,
      q.val = p.val + 1 ->
      pmap p = pmap q ->
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of R))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n S p q))) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  obtain ⟨X, hXformula, _hXorig⟩ :=
    exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common
      m n U R A V S B C pmap hU hV hA hB hmono hcard hzero
      hspectral hsingle_det hblock_noCommon
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_local_no_common_generated_step_formula
      m n U R A V S B C
      (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap
      hU hV hA hB rfl hmono hcard hzero hspectral hsingle_det
      hblock_noCommon hXformula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the local no-common recursive Schur-coordinate
    generated-step witness. -/
alias H16_eq16_4_8_exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common :=
  exists_isSylvesterSolutionRect_and_generatedStepFormula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the local no-common recursive original-coordinate
    generated-step witness. -/
alias H16_eq16_4_8_exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common :=
  exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_local_no_common

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for local no-common recursive generated-step
    unique solvability. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_local_no_common_generated_step_formula_witness :=
  existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_local_no_common_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    recursive-candidate witness with the real quasi-Schur factors chosen
    internally.  Under the original no-common complex spectrum hypothesis, the
    constructed real quasi-Schur factors provide the block-map, zero-below, and
    adjacent two-block spectral certificates consumed by the generated
    Bartels-Stewart traversal. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_no_common
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    exists (U R : RMatFn m m) (V S : RMatFn n n)
        (pA : Fin m -> Nat) (pB : Fin n -> Nat) (X : RMatFn m n),
      IsOrthogonal m U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) /\
      (forall i j : Fin m, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) := by
  obtain
      ⟨U, R, V, S, pA, pB, hU, hV, hA, hB, hpAmono, hpAcard,
        hAzero, hAspectral, hpBmono, hpBcard, hBzero, hBspectral, _hiff⟩ :=
    sylvester_realQuasiSchur_transform_solution_iff_twoBlockSpectral
      m n A B C (fun _ _ => 0)
  obtain ⟨X, hXformula, hXorig⟩ :=
    exists_original_solution_and_generated_step_formula_of_quasiSchur_schedule_twoBlockSpectral_no_common
      m n U R A V S B C pB hU hV hA hB hpBmono hpBcard hBzero hBspectral hnoOrig
  exact
    ⟨U, R, V, S, pA, pB, X, hU, hV, hA, hB, hpAmono, hpAcard,
      hAzero, hAspectral, hpBmono, hpBcard, hBzero, hBspectral, hXformula, hXorig⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    recursive-candidate unique solvability with internally chosen real
    quasi-Schur factors.  This removes the caller-facing supplied block-map and
    two-block spectral premises from the recursive generated-step witness route,
    leaving the original no-common complex spectrum hypothesis. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_no_common_generated_step_formula_witness
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  obtain
      ⟨U, R, V, S, _pA, pB, hU, hV, hA, hB, _hpAmono, _hpAcard,
        _hAzero, _hAspectral, hpBmono, hpBcard, hBzero, hBspectral, _hiff⟩ :=
    sylvester_realQuasiSchur_transform_solution_iff_twoBlockSpectral
      m n A B C (fun _ _ => 0)
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_schedule_twoBlockSpectral_no_common_generated_step_formula_witness
      m n U R A V S B C pB hU hV hA hB hpBmono hpBcard hBzero hBspectral hnoOrig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-numbered
    alias for the internally chosen real quasi-Schur recursive generated-step
    original-coordinate witness under no common complex spectrum. -/
theorem H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_no_common
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    exists (U R : RMatFn m m) (V S : RMatFn n n)
        (pA : Fin m -> Nat) (pB : Fin n -> Nat) (X : RMatFn m n),
      IsOrthogonal m U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) /\
      (forall i j : Fin m, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_no_common
    m n A B C hnoOrig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-numbered
    alias for original-coordinate unique solvability via internally chosen real
    quasi-Schur factors and the generated recursive candidate route. -/
theorem H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_no_common
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_no_common_generated_step_formula_witness
    m n A B C hnoOrig

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    recursive-candidate witness from nonsingularity of the original
    vec/Kronecker Sylvester coefficient. -/
theorem exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0)) :
    exists (U R : RMatFn m m) (V S : RMatFn n n)
        (pA : Fin m -> Nat) (pB : Fin n -> Nat) (X : RMatFn m n),
      IsOrthogonal m U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) /\
      (forall i j : Fin m, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_no_common
    m n A B C
    (no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
      m n A B hdet)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    recursive-candidate unique solvability from nonsingularity of the original
    vec/Kronecker Sylvester coefficient. -/
theorem existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_det_ne_zero_generated_step_formula_witness
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_no_common_generated_step_formula_witness
    m n A B C
    (no_common_complex_right_eigenvalue_of_sylvesterVecCoeff_det_ne_zero
      m n A B hdet)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-numbered
    alias for the internally chosen real-Schur recursive generated-step
    witness from vec coefficient nonsingularity. -/
theorem H16_eq16_4_8_exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0)) :
    exists (U R : RMatFn m m) (V S : RMatFn n n)
        (pA : Fin m -> Nat) (pB : Fin n -> Nat) (X : RMatFn m n),
      IsOrthogonal m U /\
      IsOrthogonal n V /\
      A = rectMatMul U (rectMatMul R (matTranspose U)) /\
      B = rectMatMul V (rectMatMul S (matTranspose V)) /\
      Monotone pA /\
      (forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) /\
      (forall i j : Fin m, pA j < pA i -> R i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of R) pA /\
      Monotone pB /\
      (forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) /\
      (forall i j : Fin n, pB j < pB i -> S i j = 0) /\
      HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pB /\
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pB /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) :=
  exists_realQuasiSchur_schedule_original_solution_and_generated_step_formula_of_vecCoeff_det_ne_zero
    m n A B C hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-numbered
    alias for original-coordinate unique solvability via internally chosen
    real-Schur factors and vec coefficient nonsingularity. -/
theorem H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) :=
  existsUnique_isSylvesterSolutionRect_of_realQuasiSchur_schedule_vecCoeff_det_ne_zero_generated_step_formula_witness
    m n A B C hdet

/-- Any exact Schur-coordinate solution satisfies the generated-step formula
    oracle when the real quasi-Schur block map and original no-common spectrum
    hypotheses provide the singleton and two-column nonsingularity
    certificates.  This turns the packaged oracle into a consequence of exact
    solvability, rather than a separate formula assumption. -/
theorem isSylvesterQuasiSchurGeneratedStepFormula_of_solution_twoBlockSpectral_no_common
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B))
    (hXsol : IsSylvesterSolutionRect m n R S C X) :
    IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap := by
  constructor
  · intro p hprev hnext i
    have hsingle :
        forall q : Fin n, pmap q = pmap p -> q = p :=
      quasiSchur_singleton_fiber_of_prev_next_not_same
        n pmap p hmono hprev hnext
    have hdet :
        Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S p p)) = 0) :=
      sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_no_common_complex_right_eigenvalue
        m n U R A V S B pmap p hU hV hA hB hzero hsingle hnoOrig
    have hbelow : forall j : Fin n, p < j -> S j p = 0 :=
      quasiSchur_zero_below_of_singleton_successor
        n S pmap p hmono hzero hnext
    let M : Matrix (Fin m) (Fin m) Real :=
      sylvesterTriangularShiftedCoeff m R (S p p)
    let rhs : Fin m -> Real := fun i => C i p +
      Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
        (fun j => S j p * X i j)
    have hMx : Matrix.mulVec M (fun i : Fin m => X i p) = rhs := by
      dsimp [M, rhs]
      exact sylvester_column_equation_of_solution_zero_below
        m n R S C X p hbelow hXsol
    have hleft : Inv.inv M * M = 1 := by
      dsimp [M]
      exact sylvesterTriangularShiftedCoeff_nonsingInv_mul
        m R (S p p) hdet
    have hvec :
        (fun i : Fin m => X i p) =
          Matrix.mulVec (Inv.inv M) rhs := by
      calc
        (fun i : Fin m => X i p) =
            Matrix.mulVec (1 : Matrix (Fin m) (Fin m) Real)
              (fun i : Fin m => X i p) := by
              simp
        _ = Matrix.mulVec (Inv.inv M * M) (fun i : Fin m => X i p) := by
              rw [hleft]
        _ = Matrix.mulVec (Inv.inv M)
              (Matrix.mulVec M (fun i : Fin m => X i p)) := by
              rw [Matrix.mulVec_mulVec]
        _ = Matrix.mulVec (Inv.inv M) rhs := by
              rw [hMx]
    exact congrFun hvec i
  · intro p q hpq hsame
    have hblockdet :=
      sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_factors_twoBlockSpectral_global_no_common_complex_right_eigenvalue_left
        m n U R A V S B pmap p q hU hV hA hB hmono hcard hzero
        hpq hsame hspectral hnoOrig
    have hsystem : IsSylvesterTwoColumnBlockSystem m n R S C X p q :=
      sylvester_quasiTriangular_two_column_block_system_of_solution
        m n R S C X p q hblockdet.1 hXsol
    have hz :
        Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n R S p q)
            (Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q)) =
          sylvesterTwoColumnBlockRhs m n S C X p q := by
      have hz' :=
        (sylvester_two_column_block_system_iff_blockCoeff_mulVec
          m n R S C X p q).mp hsystem
      simpa [sylvesterTwoColumnBlockRhs] using hz'
    have hvec :=
      sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
        m n R S C X p q hblockdet.2 hz
    constructor
    · intro i
      exact congrFun hvec (Sum.inl i)
    · intro i
      exact congrFun hvec (Sum.inr i)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), exact
    generated-step witness surface: under supplied real-quasi-Schur factors,
    the two-block spectral block map, and original no-common complex spectrum,
    some exact Schur-coordinate solution satisfies the packaged generated-step
    formulas.

    Scope: this proves existence of a formula-satisfying witness by the exact
    vectorized Sylvester solve and the solution-characterization theorem above.
    It is not yet the recursive Bartels-Stewart construction of the candidate
    `X`. -/
theorem exists_isSylvesterSolutionRect_and_generatedStepFormula_of_twoBlockSpectral_no_common
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    exists X : RMatFn m n,
      IsSylvesterSolutionRect m n R S C X /\
        IsSylvesterQuasiSchurGeneratedStepFormula m n R S C X pmap := by
  have hnoRS :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex R)
        (realMatrixToComplex S) :=
    noCommonComplexRightEigenvalue_realQuasiSchur_factors
      m n U R A V S B hU hV hA hB hnoOrig
  have hdet :
      Not (Matrix.det (sylvesterVecCoeff m n R S) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
      m n R S hnoRS
  let x : Prod (Fin n) (Fin m) -> Real :=
    Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n R S)) (Matrix.vec C)
  have hx :
      Matrix.mulVec (sylvesterVecCoeff m n R S) x = Matrix.vec C := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv (sylvesterVecCoeff m n R S)
        (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  obtain ⟨X, hXvec⟩ := Matrix.vec_bijective.surjective x
  have hXsol : IsSylvesterSolutionRect m n R S C X :=
    (sylvester_vec_system_iff_solution m n R S C X).mp
      (by rw [hXvec]; exact hx)
  exact ⟨X, hXsol,
    isSylvesterQuasiSchurGeneratedStepFormula_of_solution_twoBlockSpectral_no_common
      m n U R A V S B C X pmap hU hV hA hB hmono hcard hzero
      hspectral hnoOrig hXsol⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    generated-step witness surface: the exact Schur-coordinate witness from
    `exists_isSylvesterSolutionRect_and_generatedStepFormula_of_twoBlockSpectral_no_common`
    reconstructs an exact original-coordinate solution after the standard
    `C_s = U^T C V` right-hand-side transform.

    Scope: the generated formulas are proved for the Schur-coordinate right
    hand side displayed in the theorem.  The witness is still obtained through
    the exact vec/Kronecker inverse route, not by the recursive
    Bartels-Stewart frontier recurrence. -/
theorem exists_original_solution_and_generated_step_formula_of_twoBlockSpectral_no_common
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    exists X : RMatFn m n,
      IsSylvesterQuasiSchurGeneratedStepFormula m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap /\
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul X (matTranspose V))) := by
  obtain ⟨X, hXsol, hXformula⟩ :=
    exists_isSylvesterSolutionRect_and_generatedStepFormula_of_twoBlockSpectral_no_common
      m n U R A V S B
      (rectMatMul (matTranspose U) (rectMatMul C V)) pmap
      hU hV hA hB hmono hcard hzero hspectral hnoOrig
  refine ⟨X, hXformula, ?_⟩
  exact
    (sylvester_schur_transform_solution_iff m n
      U R A V S B C X hU hV hA hB).mpr hXsol

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), source-facing
    original-coordinate unique solvability from the exact generated-formula
    witness.  This removes the caller-facing generated-formula hypothesis by
    producing such a witness from the exact vec/Kronecker solve, then feeding
    it to the generated-step unique-solvability wrapper.

    Scope: exact arithmetic only; this is not a rounded Bartels-Stewart solve
    or LAPACK estimator theorem. -/
theorem existsUnique_isSylvesterSolutionRect_of_twoBlockSpectral_no_common_generated_step_formula_witness
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C : RMatFn m n)
    (pmap : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> S i j = 0)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of S) pmap)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  obtain ⟨X, hXformula, _hXorig⟩ :=
    exists_original_solution_and_generated_step_formula_of_twoBlockSpectral_no_common
      m n U R A V S B C pmap hU hV hA hB hmono hcard hzero
      hspectral hnoOrig
  exact
    existsUnique_isSylvesterSolutionRect_of_quasiSchur_twoBlockSpectral_no_common_generated_step_formula
      m n U R A V S B C
      (rectMatMul (matTranspose U) (rectMatMul C V)) X pmap
      hU hV hA hB rfl hmono hcard hzero hspectral hnoOrig hXformula

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for generated-step characterization of exact
    Schur-coordinate solutions. -/
alias H16_eq16_4_8_isSylvesterQuasiSchurGeneratedStepFormula_of_solution_twoBlockSpectral_no_common :=
  isSylvesterQuasiSchurGeneratedStepFormula_of_solution_twoBlockSpectral_no_common

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for exact Schur-coordinate generated-step witness
    existence. -/
alias H16_eq16_4_8_exists_isSylvesterSolutionRect_and_generatedStepFormula_of_twoBlockSpectral_no_common :=
  exists_isSylvesterSolutionRect_and_generatedStepFormula_of_twoBlockSpectral_no_common

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate generated-step witness
    existence. -/
alias H16_eq16_4_8_exists_original_solution_and_generated_step_formula_of_twoBlockSpectral_no_common :=
  exists_original_solution_and_generated_step_formula_of_twoBlockSpectral_no_common

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for original-coordinate unique solvability from an
    exact generated-step witness. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_of_twoBlockSpectral_no_common_generated_step_formula_witness :=
  existsUnique_isSylvesterSolutionRect_of_twoBlockSpectral_no_common_generated_step_formula_witness

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5)-(16.6), uniqueness half:
    with upper-triangular `T` and every shifted column coefficient
    `A - t_kk I` nonsingular, two solutions of `AX - XT = C` coincide, by
    strong induction over columns using the column recurrence. -/
theorem sylvester_triangular_solution_unique (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (hT : IsUpperTriangularFn n T)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A T C X)
    (hY : IsSylvesterSolutionRect m n A T C Y) :
    X = Y := by
  have hcol : forall N : Nat, forall k : Fin n, k.val < N ->
      (fun i => X i k) = (fun i => Y i k) := by
    intro N
    induction N with
    | zero =>
        intro k hk
        exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        intro k hk
        by_cases hlt : k.val < N
        case pos => exact ih k hlt
        case neg =>
          have hXk := sylvester_triangular_column_equation m n A T C X hT hX k
          have hYk := sylvester_triangular_column_equation m n A T C Y hT hY k
          have hrhs :
              (fun i => C i k +
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * X i j)) =
              (fun i => C i k +
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * Y i j)) := by
            funext i
            have hsum : Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * X i j) =
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * Y i j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : Nat) < (k : Nat) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjN : (j : Nat) < N := by omega
              have hXY : X i j = Y i j := congrFun (ih j hjN) i
              rw [hXY]
            rw [hsum]
          have hmv :
              Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
                  (fun i => X i k) =
                Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
                  (fun i => Y i k) := by
            rw [hXk, hYk]
            exact hrhs
          exact mulVec_injective_of_det_ne_zero (hshift k) hmv
  funext i j
  exact congrFun (hcol n j j.isLt) i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), supplied-factor
    Bartels-Stewart existence and uniqueness: with SUPPLIED upper-triangular
    `T` and every shifted column coefficient `A - t_kk I` nonsingular, the
    transformed equation `AX - XT = C` has exactly one solution, built by
    strong induction over columns: column `k` is obtained from the supplied
    inverse of `A - t_kk I` applied to `c_k + sum_{j<k} t_jk x_j` after
    substituting the already-solved earlier columns.  This generalizes the
    diagonal case `existsUnique_isSylvesterSolutionRect_diagonal` of
    `Higham16.lean` to triangular `T`.
    Scope: exact arithmetic at the supplied-factor level; no Schur existence
    (the orthogonal reduction (16.4) is handled separately by
    `sylvester_schur_transform_solution_iff`), no quasi-triangular 2x2
    blocks ((16.7)-(16.8)), and no floating-point error analysis. -/
theorem sylvester_triangular_solve_exists_unique (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C : RMatFn m n)
    (hT : IsUpperTriangularFn n T)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A T C) := by
  have hpartial : forall N : Nat,
      exists x : Fin n -> Fin m -> Real,
        forall k : Fin n, k.val < N ->
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) (x k) =
            fun i => C i k +
              Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                (fun j => T j k * x j i) := by
    intro N
    induction N with
    | zero =>
        refine ⟨fun _ _ => 0, ?_⟩
        intro k hk
        exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        obtain ⟨x, hx⟩ := ih
        by_cases hN : N < n
        case neg =>
          refine ⟨x, ?_⟩
          intro k hk
          have hkN : k.val < N := by
            have hkn : k.val < n := k.isLt
            omega
          exact hx k hkN
        case pos =>
          obtain ⟨xk, hxk⟩ :=
            mulVec_surjective_of_det_ne_zero (hshift ⟨N, hN⟩)
              (fun i => C i ⟨N, hN⟩ +
                Finset.sum
                  (Finset.filter (fun j => j < (⟨N, hN⟩ : Fin n)) Finset.univ)
                  (fun j => T j ⟨N, hN⟩ * x j i))
          refine ⟨Function.update x ⟨N, hN⟩ xk, ?_⟩
          intro k hk
          have hupdate_rhs : forall k' : Fin n, k'.val <= N ->
              (fun i => C i k' +
                Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * Function.update x ⟨N, hN⟩ xk j i)) =
              (fun i => C i k' +
                Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * x j i)) := by
            intro k' hk'
            funext i
            have hsum : Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * Function.update x ⟨N, hN⟩ xk j i) =
                Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * x j i) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : Nat) < (k' : Nat) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjne : Not (j = (⟨N, hN⟩ : Fin n)) := by
                intro hje
                have hjval : (j : Nat) = N := by rw [hje]
                omega
              rw [Function.update_of_ne hjne]
            rw [hsum]
          by_cases hkval : k.val < N
          case pos =>
            have hkne : Not (k = (⟨N, hN⟩ : Fin n)) := by
              intro hke
              have hkv : (k : Nat) = N := by rw [hke]
              omega
            rw [Function.update_of_ne hkne,
              hupdate_rhs k (Nat.le_of_lt hkval)]
            exact hx k hkval
          case neg =>
            have hkeq : k = (⟨N, hN⟩ : Fin n) := by
              apply Fin.ext
              show (k : Nat) = N
              omega
            rw [hkeq, Function.update_self,
              hupdate_rhs ⟨N, hN⟩ (Nat.le_refl N)]
            exact hxk
  obtain ⟨x, hx⟩ := hpartial n
  have hsol : IsSylvesterSolutionRect m n A T C (fun i j => x j i) := by
    apply (sylvester_triangular_solution_iff_column_equations m n A T C
      (fun i j => x j i) hT).mpr
    intro k
    exact hx k k.isLt
  refine ⟨fun i j => x j i, hsol, ?_⟩
  intro Y hY
  exact sylvester_triangular_solution_unique m n A T C Y (fun i j => x j i)
    hT hshift hY hsol

private theorem rectMatMul_schur_coords_expand_for_triangular {m n : Nat}
    (U : RMatFn m m) (V : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    rectMatMul U
      (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)) = C := by
  have hUUt : rectMatMul U (matTranspose U) = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.right_inv i j
  have hVVt : rectMatMul V (matTranspose V) = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.right_inv i j
  calc
    rectMatMul U
        (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V))
        = rectMatMul (rectMatMul U
            (rectMatMul (matTranspose U) (rectMatMul C V))) (matTranspose V) := by
            exact (rectMatMul_assoc U
              (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)).symm
    _ = rectMatMul (rectMatMul (rectMatMul U (matTranspose U))
            (rectMatMul C V)) (matTranspose V) := by
            exact congrArg (fun Z => rectMatMul Z (matTranspose V))
              (rectMatMul_assoc U (matTranspose U) (rectMatMul C V)).symm
    _ = rectMatMul (rectMatMul (idMatrix m) (rectMatMul C V)) (matTranspose V) := by
            rw [hUUt]
    _ = rectMatMul (rectMatMul C V) (matTranspose V) := by
            rw [rectMatMul_id_left]
    _ = rectMatMul C (rectMatMul V (matTranspose V)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul C (idMatrix n) := by
            rw [hVVt]
    _ = C := by
            rw [rectMatMul_id_right]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), supplied Schur
    triangular solve: if orthogonal supplied factors put `A` and `B` into
    coordinates `R` and upper-triangular `S`, and every shifted column
    coefficient `R - s_kk I` is nonsingular, then the original-coordinate
    equation `AX - XB = C` has exactly one solution.  This composes the
    supplied-factor Schur equivalence `sylvester_schur_transform_solution_iff`
    with the Bartels-Stewart column solve `sylvester_triangular_solve_exists_unique`.
    Scope: exact arithmetic only; Schur existence, real quasi-triangular 2x2
    blocks, Hessenberg-Schur reductions, and floating-point stability remain
    separate open rows. -/
theorem existsUnique_isSylvesterSolutionRect_schurTriangular (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  let Cschur : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul C V)
  obtain ⟨Y, hY, hYuniq⟩ :=
    sylvester_triangular_solve_exists_unique m n R S Cschur hS hshift
  refine ⟨rectMatMul U (rectMatMul Y (matTranspose V)), ?_, ?_⟩
  · exact (sylvester_schur_transform_solution_iff m n
      U R A V S B C Y hU hV hA hB).mpr hY
  · intro X hX
    let YX : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul X V)
    have hXexpand : rectMatMul U (rectMatMul YX (matTranspose V)) = X :=
      rectMatMul_schur_coords_expand_for_triangular U V X hU hV
    have hXsol :
        IsSylvesterSolutionRect m n A B C
          (rectMatMul U (rectMatMul YX (matTranspose V))) := by
      rw [hXexpand]
      exact hX
    have hYX :
        IsSylvesterSolutionRect m n R S Cschur YX :=
      (sylvester_schur_transform_solution_iff m n
        U R A V S B C YX hU hV hA hB).mp hXsol
    have hYeq : YX = Y := hYuniq YX hYX
    calc
      X = rectMatMul U (rectMatMul YX (matTranspose V)) := hXexpand.symm
      _ = rectMatMul U (rectMatMul Y (matTranspose V)) := by rw [hYeq]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6):
    source-numbered alias for the supplied Schur-triangular exact unique-solve
    endpoint. -/
alias H16_eq16_4_6_existsUnique_isSylvesterSolutionRect_schurTriangular :=
  existsUnique_isSylvesterSolutionRect_schurTriangular

/-- Real quasi-Schur-to-triangular uniqueness bridge.  The theorem returns the
    exact real quasi-Schur factors for `A` and `B`; if the returned `B`-side
    block map is supplied to be strictly increasing down the matrix order, so
    the selected Schur factor is effectively upper triangular, and each
    shifted triangular column coefficient is nonsingular, then the original
    Sylvester equation has a unique exact solution.

    Scope: exact arithmetic and the triangular subcase only.  This deliberately
    does not claim full quasi-triangular block nonsingularity, Hessenberg-Schur
    execution, or floating-point stability. -/
theorem existsUnique_isSylvesterSolutionRect_realQuasiSchur_of_strictBlockMap
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      ((∀ i j : Fin n, j < i -> pB j < pB i) ->
        (∀ k : Fin n,
          Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) ->
        ExistsUnique (IsSylvesterSolutionRect m n A B C)) := by
  obtain ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, _hiff⟩ :=
    sylvester_realQuasiSchur_transform_solution_iff
      m n A B C (0 : RMatFn m n)
  refine ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, ?_⟩
  intro hpBstrict hshift
  have hS : IsUpperTriangularFn n S :=
    IsUpperTriangularFn.of_quasiSchur_strictBlockMap n S pB hSzero hpBstrict
  exact
    existsUnique_isSylvesterSolutionRect_schurTriangular
      m n U R A V S B C hU hV hA hB hS hshift

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: supplied orthogonal factors,
    an upper-triangular transformed `S`, and nonsingular shifted column
    coefficients make the vectorized Sylvester coefficient have trivial
    kernel.  Scope: supplied exact factors only; this does not assert Schur
    existence or floating-point stability. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_eq_zero_iff (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (X : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 <->
      X = 0 := by
  constructor
  case mp =>
    intro h
    have hsol : IsSylvesterSolutionRect m n A B (0 : RMatFn m n) X :=
      (sylvester_vec_system_iff_solution m n A B (0 : RMatFn m n) X).mp
        (by simpa using h)
    have hzero : IsSylvesterSolutionRect m n A B
        (0 : RMatFn m n) (0 : RMatFn m n) := by
      apply (sylvester_vec_system_iff_solution m n A B
        (0 : RMatFn m n) (0 : RMatFn m n)).mp
      change Matrix.mulVec (sylvesterVecCoeff m n A B)
          (0 : Prod (Fin n) (Fin m) -> Real) = 0
      exact Matrix.mulVec_zero _
    obtain ⟨Y, hY, hYuniq⟩ :=
      existsUnique_isSylvesterSolutionRect_schurTriangular m n
        U R A V S B (0 : RMatFn m n) hU hV hA hB hS hshift
    have hXY : X = Y := hYuniq X hsol
    have h0Y : (0 : RMatFn m n) = Y := hYuniq (0 : RMatFn m n) hzero
    rw [hXY, ← h0Y]
  case mpr =>
    intro hX
    rw [hX]
    change Matrix.mulVec (sylvesterVecCoeff m n A B)
        (0 : Prod (Fin n) (Fin m) -> Real) = 0
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    coefficient is injective under the exact supplied-factor assumptions. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_injective (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro x y hxy
  let P := sylvesterVecCoeff m n A B
  have hker : Matrix.mulVec P (x - y) = 0 := by
    dsimp [P]
    rw [Matrix.mulVec_sub, hxy, sub_self]
  obtain ⟨X, hXvec⟩ :=
    Matrix.vec_bijective.surjective (x - y : Prod (Fin n) (Fin m) -> Real)
  have hkerX :
      Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 := by
    dsimp [P] at hker
    rw [hXvec]
    exact hker
  have hXzero : X = 0 :=
    (sylvesterVecCoeff_schurTriangular_mulVec_eq_zero_iff
      m n U R A V S B X hU hV hA hB hS hshift).mp hkerX
  have hsub : x - y = 0 := by
    rw [← hXvec, hXzero]
    rfl
  exact sub_eq_zero.mp hsub

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    coefficient is surjective under the exact supplied-factor assumptions. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_surjective (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro y
  obtain ⟨C, hC⟩ := Matrix.vec_bijective.surjective y
  obtain ⟨X, hX, _⟩ :=
    existsUnique_isSylvesterSolutionRect_schurTriangular m n
      U R A V S B C hU hV hA hB hS hshift
  refine ⟨Matrix.vec X, ?_⟩
  rw [← hC]
  exact (sylvester_vec_system_iff_solution m n A B C X).mpr hX

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    coefficient is bijective under the exact supplied-factor assumptions. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_bijective (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) :=
  ⟨sylvesterVecCoeff_schurTriangular_mulVec_injective
      m n U R A V S B hU hV hA hB hS hshift,
    sylvesterVecCoeff_schurTriangular_mulVec_surjective
      m n U R A V S B hU hV hA hB hS hshift⟩

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    linear system has a unique solution for every vectorized right-hand side
    under the exact supplied-factor assumptions. -/
theorem existsUnique_sylvesterVecCoeff_schurTriangular_mulVec (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  have hinj :=
    sylvesterVecCoeff_schurTriangular_mulVec_injective
      m n U R A V S B hU hV hA hB hS hshift
  have hsurj :=
    sylvesterVecCoeff_schurTriangular_mulVec_surjective
      m n U R A V S B hU hV hA hB hS hshift
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for the supplied Schur-triangular vectorized
    unique-solve endpoint. -/
alias H16_eq16_2_6_existsUnique_sylvesterVecCoeff_schurTriangular_mulVec :=
  existsUnique_sylvesterVecCoeff_schurTriangular_mulVec

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vec/Kronecker Sylvester
    coefficient itself is nonsingular under the exact supplied-factor
    assumptions.  This records the determinant form corresponding to the
    bijective vectorized solve above; it is still a supplied-factor result,
    not a proof of Schur existence or floating-point stability. -/
theorem sylvesterVecCoeff_schurTriangular_det_ne_zero (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  intro hdet
  obtain ⟨x, hxne, hxzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hinj :=
    sylvesterVecCoeff_schurTriangular_mulVec_injective
      m n U R A V S B hU hV hA hB hS hshift
  have hxzero' : x = 0 := by
    apply hinj
    rw [hxzero, Matrix.mulVec_zero]
  exact hxne hxzero'

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias
    for determinant nonsingularity of the supplied Schur-triangular
    vec/Kronecker coefficient. -/
alias H16_eq16_3_sylvesterVecCoeff_schurTriangular_det_ne_zero :=
  sylvesterVecCoeff_schurTriangular_det_ne_zero













/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    `B`-side singleton-block real-quasi-Schur case: supplied orthogonal
    factors, a strictly increasing `B`-side block map, and nonsingular shifted
    column coefficients make the original vec/Kronecker Sylvester coefficient
    nonsingular.  This is the minimal strict-block-map determinant surface; no
    left block-map data is needed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBBlockMap_det_ne_zero
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  exact
    sylvesterVecCoeff_schurTriangular_det_ne_zero
      m n U R A V S B hU hV hA hB
      (isUpperTriangularFn_of_strictBlockMap n S pB hpBstrict hSstrict)
      hshift

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the minimal strict `B`-side real-quasi-Schur
    determinant route. -/
alias H16_eq16_3_sylvesterVecCoeff_realQuasiSchur_strictBBlockMap_det_ne_zero :=
  sylvesterVecCoeff_realQuasiSchur_strictBBlockMap_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: supplied real quasi-Schur factors
    whose `B`-side block map is strictly increasing reduce to the supplied
    Schur-triangular determinant theorem, so the original vec/Kronecker
    Sylvester coefficient is nonsingular. Scope: exact supplied factors only;
    this does not prove the 2-by-2 real quasi-Schur block solve or floating-
    point Bartels-Stewart stability. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  exact
    sylvesterVecCoeff_realQuasiSchur_strictBBlockMap_det_ne_zero
      m n U R A V S B pB hU hV hA hB hpBstrict hSstrict hshift

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the strict singleton-block real-quasi-Schur
    determinant route. -/
alias H16_eq16_3_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the strict supplied-factor
    determinant certificate makes the vectorized Sylvester coefficient have
    trivial kernel. Scope: exact supplied factors only; no 2-by-2 block solve
    or floating-point stability is claimed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_eq_zero_iff
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (x : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) x = 0 <-> x = 0 := by
  constructor
  · intro hx
    have hdet :=
      sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
        m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
        hpBmono hpBcard hpBstrict hSstrict hshift
    have h := congrArg
      (Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))) hx
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec] at h
    exact h
  · intro hx
    rw [hx]
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the strict supplied-factor
    determinant certificate makes the vectorized Sylvester coefficient
    injective. Scope: exact supplied factors only; no 2-by-2 block solve or
    floating-point stability is claimed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  intro x y hxy
  have h := congrArg
    (Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the strict supplied-factor
    determinant certificate makes the vectorized Sylvester coefficient
    surjective, so every vectorized right-hand side is reachable in exact
    arithmetic. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  intro c
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the vectorized Sylvester
    coefficient solve is bijective under the exact supplied-factor
    assumptions. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_bijective
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) :=
  ⟨sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift,
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift⟩

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: every vectorized right-hand side
    has a unique exact solution under the strict supplied-factor assumptions. -/
theorem existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  have hinj :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  have hsurj :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for unique vectorized solves in the strict
    singleton-block real-quasi-Schur subcase. -/
alias H16_eq16_2_6_existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec :=
  existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for the strict real-quasi-Schur vectorized
    coefficient trivial-kernel characterization. -/
alias H16_eq16_2_6_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_eq_zero_iff :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_eq_zero_iff

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for strict real-quasi-Schur vectorized coefficient
    injectivity. -/
alias H16_eq16_2_6_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for strict real-quasi-Schur vectorized coefficient
    surjectivity. -/
alias H16_eq16_2_6_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for strict real-quasi-Schur vectorized coefficient
    bijectivity. -/
alias H16_eq16_2_6_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_bijective :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_bijective

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: Mathlib's nonsingular inverse gives
    an explicit exact vectorized Sylvester coefficient solution for any right-
    hand side. Scope: supplied exact factors only; no 2-by-2 block solve or
    floating-point stability is claimed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff m n A B)
        (Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c) =
      c := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the nonsingular inverse is a left
    action on the vectorized Sylvester coefficient under the supplied exact
    factor hypotheses. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_mulVec
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (x : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))
        (Matrix.mulVec (sylvesterVecCoeff m n A B) x) =
      x := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: any exact vectorized Sylvester
    coefficient solution is the nonsingular-inverse solution. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_eq_nonsingInv_mulVec_of_mulVec_eq
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    {x c : Prod (Fin n) (Fin m) -> Real}
    (hx : Matrix.mulVec (sylvesterVecCoeff m n A B) x = c) :
    x = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
  calc
    x =
        Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))
          (Matrix.mulVec (sylvesterVecCoeff m n A B) x) := by
        symm
        exact
          sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_mulVec
            m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
            hpBmono hpBcard hpBstrict hSstrict hshift x
    _ = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
        rw [hx]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the nonsingular-inverse formula is
    the unique exact vectorized Sylvester coefficient solution for the supplied
    factors. -/
theorem existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c ∧
        x = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c, ?_, ?_⟩
  · exact
      ⟨sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution
          m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
          hpBmono hpBcard hpBstrict hSstrict hshift c,
        rfl⟩
  · intro y hy
    exact
      sylvesterVecCoeff_realQuasiSchur_strictBlockMap_eq_nonsingInv_mulVec_of_mulVec_eq
        m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
        hpBmono hpBcard hpBstrict hSstrict hshift hy.1

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for the strict real-quasi-Schur nonsingular-inverse
    vectorized Sylvester coefficient solution. -/
alias H16_eq16_2_6_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for the strict real-quasi-Schur nonsingular-inverse
    left action on the vectorized Sylvester coefficient. -/
alias H16_eq16_2_6_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_mulVec :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_mulVec

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias identifying any exact strict real-quasi-Schur
    vectorized solution with the nonsingular-inverse solution. -/
alias H16_eq16_2_6_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_eq_nonsingInv_mulVec_of_mulVec_eq :=
  sylvesterVecCoeff_realQuasiSchur_strictBlockMap_eq_nonsingInv_mulVec_of_mulVec_eq

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6):
    source-numbered alias for unique strict real-quasi-Schur vectorized
    nonsingular-inverse solves. -/
alias H16_eq16_2_6_existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution :=
  existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution

/-- Higham, 2nd ed., Chapter 16.1-16.2, equation (16.3), strict
    real-quasi-Schur singleton-block nonsingularity excludes a supplied common
    real right/transpose eigenpair of `A` and `B`. -/
theorem no_common_real_eigenpair_of_realQuasiSchur_strictBlockMap (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.mulVec (Matrix.transpose B) w = fun j => lam * w j) :
    False := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  exact hdet
    (sylvesterVecCoeff_singular_of_common_eigenvalue
      m n A B v w lam hv0 hw0 hv hw)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equation (16.3), strict
    real-quasi-Schur singleton-block nonsingularity excludes a supplied common
    real right/left eigenpair of `A` and `B`. -/
theorem no_common_real_left_eigenpair_of_realQuasiSchur_strictBlockMap
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.vecMul w B = fun j => lam * w j) :
    False := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  apply hdet
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨Matrix.vec (fun i j => v i * w j : RMatFn m n),
    vec_outer_product_ne_zero m n v w hv0 hw0, ?_⟩
  rw [sylvesterVecCoeff_eigenpair_vecMul m n A B v w lam lam hv hw]
  funext p
  simp

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for excluding supplied common real eigenpairs of
    `A` and `B^T` in the strict singleton-block real-quasi-Schur subcase. -/
alias H16_eq16_3_no_common_real_eigenpair_of_realQuasiSchur_strictBlockMap :=
  no_common_real_eigenpair_of_realQuasiSchur_strictBlockMap

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for excluding supplied common real left-eigenpair
    data in the strict singleton-block real-quasi-Schur subcase. -/
alias H16_eq16_3_no_common_real_left_eigenpair_of_realQuasiSchur_strictBlockMap :=
  no_common_real_left_eigenpair_of_realQuasiSchur_strictBlockMap

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6),
    supplied triangular Schur-coordinate case: the exact shifted-determinant
    hypotheses that make the vectorized Sylvester coefficient nonsingular also
    rule out supplied common real eigenpairs of `A` and `B^T`. -/
theorem no_common_real_eigenpair_of_schurTriangular (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.mulVec (Matrix.transpose B) w = (fun j => lam * w j)) :=
  no_common_real_eigenpair_of_sylvesterVecCoeff_det_ne_zero m n A B
    (sylvesterVecCoeff_schurTriangular_det_ne_zero
      m n U R A V S B hU hV hA hB hS hshift)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6),
    supplied triangular Schur-coordinate case in left-eigenvector form:
    exact shifted-determinant hypotheses rule out supplied nonzero real
    eigenpairs `A v = lam v` and `w^T B = lam w^T`. -/
theorem no_common_real_left_eigenpair_of_schurTriangular (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.vecMul w B = (fun j => lam * w j)) :=
  no_common_real_left_eigenpair_of_sylvesterVecCoeff_det_ne_zero m n A B
    (sylvesterVecCoeff_schurTriangular_det_ne_zero
      m n U R A V S B hU hV hA hB hS hshift)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the supplied Schur-triangular exclusion of
    common real eigenpairs of `A` and `B^T`. -/
alias H16_eq16_3_no_common_real_eigenpair_of_schurTriangular :=
  no_common_real_eigenpair_of_schurTriangular

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the supplied Schur-triangular exclusion of
    common real eigenpairs in source-facing left-eigenvector form. -/
alias H16_eq16_3_no_common_real_left_eigenpair_of_schurTriangular :=
  no_common_real_left_eigenpair_of_schurTriangular

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case: the practical componentwise error bound can use
    the actual nonsingular inverse of the vec/Kronecker Sylvester coefficient.
    The supplied Schur-triangular hypotheses prove the left-inverse condition
    for `P^{-1}`, while the residual-budget certificate remains explicit.
    Scope: exact supplied factors only; this does not assert Schur existence,
    a LAPACK estimator, or a full floating-point solution algorithm. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with componentwise larger practical-budget inputs.
    The exact nonsingular inverse is supplied by the Schur-triangular
    certificate, while `PinvAbs'`, `Rhat'`, and `Ru'` are merely larger
    estimator inputs.  Scope: exact supplied factors only; this does not assert
    Schur existence, rounded residual arithmetic, or a LAPACK estimator. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions:
    nonnegative componentwise residual tolerances and an entrywise computed
    residual error bound supply the practical componentwise error bound. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
      m n U R A V S B C X Xhat Rhat Ru hU hV hA hB hS hshift hX
      ⟨hRu, hRhat⟩ hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), real quasi-Schur
    triangular subcase: return exact real quasi-Schur factors for `A` and `B`;
    if the returned `B`-side block labels are strictly increasing below the
    diagonal and the shifted triangular column coefficients are nonsingular,
    then the raw computed-residual practical bound follows for the original
    `A` and `B`.

    Scope: this is only the strict-block-map triangular subcase, reusing the
    supplied Schur-triangular endpoint above.  It does not assert full
    quasi-triangular block nonsingularity, Hessenberg-Schur execution, rounded
    residual arithmetic, or floating-point stability. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      ((∀ i j : Fin n, j < i -> pB j < pB i) ->
        (∀ k : Fin n,
          Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) ->
        IsSylvesterSolutionRect m n A B C X ->
        (∀ i j, 0 <= Ru i j) ->
        (∀ i j,
          |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j) ->
        0 < sylvesterMaxEntryNormRect m n Xhat ->
        sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
            sylvesterMaxEntryNormRect m n Xhat <=
          sylvesterVecMaxNorm m n
            (sylvesterPracticalBudgetVec m n
              (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
            sylvesterMaxEntryNormRect m n Xhat) := by
  obtain ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, _hiff⟩ :=
    sylvester_realQuasiSchur_transform_solution_iff
      m n A B C (0 : RMatFn m n)
  refine ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, ?_⟩
  intro hpBstrict hshift hX hRu hRhat hXhat
  have hS : IsUpperTriangularFn n S :=
    IsUpperTriangularFn.of_quasiSchur_strictBlockMap n S pB hSzero hpBstrict
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget
      m n U R A V S B C X Xhat Rhat Ru hU hV hA hB hS hshift hX
      hRu hRhat hXhat


















































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with a packaged computed-residual
    certificate: the global vec/Kronecker determinant premise is discharged
    from the strict `B`-side block map and the shifted column determinant
    certificates.  This is still a supplied-factor exact certificate wrapper,
    not rounded Schur arithmetic or an estimator theorem. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  have hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB
      hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict hSstrict hshift
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate
      m n U R A V S B pA pB C X Xhat Rhat Ru
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with a scalar cap: the strict block map
    plus shifted column determinant certificates discharge the global
    vec/Kronecker determinant premise. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB
      hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict hSstrict hshift
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
      m n U R A V S B pA pB C X Xhat Rhat Ru eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with an explicit residual error model:
    the strict block-map and shifted-column certificates produce the
    vec/Kronecker determinant certificate internally. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  have hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB
      hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict hSstrict hshift
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model
      m n U R A V S B pA pB C X Xhat Rhat Ru dR
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with an explicit residual error model
    and scalar cap, deriving the global determinant certificate from shifted
    triangular column determinants. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB
      hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict hSstrict hshift
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_scalar
      m n U R A V S B pA pB C X Xhat Rhat Ru dR eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with a packaged computed-residual
    certificate and componentwise larger practical-budget inputs, deriving the
    global determinant certificate from shifted triangular column determinants. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  have hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB
      hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict hSstrict hshift
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hBudget hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with monotone supplied estimates and a
    scalar cap, deriving the global determinant certificate from shifted
    triangular column determinants. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB
      hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict hSstrict hshift
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hBudget hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with an explicit residual error model
    and componentwise larger practical-budget inputs, deriving the global
    determinant certificate from shifted triangular column determinants. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict
      hSstrict hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied strict
    real-quasi-Schur practical endpoint with an explicit residual error model
    and a monotone scalar cap on an estimated practical budget, deriving the
    global determinant certificate from shifted triangular column determinants. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono_scalar
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hpBstrict
      hSstrict hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions and
    componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hS hshift hX ⟨hRu, hRhat⟩
      hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model:
    if `Rhat = R(Xhat) + dR` and `|dR| <= Ru`, then the practical
    componentwise error bound follows using the nonsingular inverse of the
    supplied Schur-triangular vec/Kronecker coefficient. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
      m n U R A V S B C X Xhat Rhat Ru hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model and
    componentwise larger practical-budget inputs.  This remains an exact
    supplied-factor wrapper: no Schur existence, rounded residual arithmetic,
    or estimator proof is asserted. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with a scalar cap on the nonsingular-inverse
    practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with a monotone scalar cap on an estimated practical
    budget.  The exact nonsingular inverse is supplied by the Schur-triangular
    certificate, while `PinvAbs'`, `Rhat'`, and `Ru'` may be any componentwise
    larger estimator inputs. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions and a
    scalar cap on the nonsingular-inverse practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
      m n U R A V S B C X Xhat Rhat Ru eta hU hV hA hB hS hshift hX
      ⟨hRu, hRhat⟩ heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions,
    monotone supplied estimates, and a scalar cap. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hS hshift hX ⟨hRu, hRhat⟩
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model and a scalar
    cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
      m n U R A V S B C X Xhat Rhat Ru eta hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model and a monotone
    scalar cap on an estimated practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono_scalar
  all_goals assumption










































































































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_budget
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      ((∀ i j : Fin n, j < i -> pB j < pB i) ->
        (∀ k : Fin n,
          Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) ->
        IsSylvesterSolutionRect m n A B C X ->
        (∀ i j, 0 <= Ru i j) ->
        (∀ i j,
          |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j) ->
        0 < sylvesterMaxEntryNormRect m n Xhat ->
        sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
            sylvesterMaxEntryNormRect m n Xhat <=
          sylvesterVecMaxNorm m n
            (sylvesterPracticalBudgetVec m n
              (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
            sylvesterMaxEntryNormRect m n Xhat) := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget
      m n A B C X Xhat Rhat Ru






































































































































































































































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the strict real-quasi-Schur shifted determinant-discharge
    practical residual endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar strict real-quasi-Schur shifted
    determinant-discharge practical residual endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone strict real-quasi-Schur shifted
    determinant-discharge practical residual endpoint. -/
alias H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar strict real-quasi-Schur shifted
    determinant-discharge practical residual endpoint. -/
alias H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the strict real-quasi-Schur shifted determinant-discharge
    practical residual-error-model endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar strict real-quasi-Schur shifted
    determinant-discharge practical residual-error-model endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone strict real-quasi-Schur shifted
    determinant-discharge practical residual-error-model endpoint. -/
alias H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar strict real-quasi-Schur shifted
    determinant-discharge practical residual-error-model endpoint. -/
alias H16_eq16_29_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_shifted_computed_residual_error_model_mono_scalar

end NumStability
