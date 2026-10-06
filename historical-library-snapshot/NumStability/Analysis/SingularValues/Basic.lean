-- Analysis/SingularValues/Basic.lean
--
-- Singular values of finite complex matrices.

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import NumStability.Analysis.MatrixNorms.Basic

/-!
# Singular-value infrastructure

Builds singular values from positive Gram operators, relates them to operator
and Frobenius norms, and provides sorted-value and attaining-vector APIs.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Source-facing complex matrix as a linear map between Mathlib Euclidean
    spaces. This is the bridge used for the `p = 2` norm and the spectral
    `A†A` layer. -/
noncomputable def complexMatrixEuclideanLin {m n : ℕ} (A : CMatrix m n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin m) (n := Fin n))
    (A : Matrix (Fin m) (Fin n) ℂ)

/-- The Euclidean coordinate basis used to compare local `CMatrix` maps with
    Mathlib matrices. -/
noncomputable abbrev complexEuclideanBasisFin (n : ℕ) :
    Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toBasis

/-- Explicit matrix view of the source-facing `CMatrix` abbreviation.  Keeping
    this named avoids ambiguous pointwise-function operations when a proof needs
    Mathlib matrix multiplication or conjugate transpose. -/
noncomputable abbrev complexCMatrixAsMatrix {m n : ℕ}
    (A : CMatrix m n) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => A i j

/-- Matrix of the Euclidean linear-map bridge in the Euclidean coordinate
    bases. -/
theorem complexMatrixEuclideanLin_toMatrix {m n : ℕ} (A : CMatrix m n) :
    LinearMap.toMatrix (complexEuclideanBasisFin n) (complexEuclideanBasisFin m)
        (complexMatrixEuclideanLin A) =
      complexCMatrixAsMatrix A := by
  rw [complexMatrixEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearMap.toMatrix_toLin _ _ _

/-- Matrix rank for the local `CMatrix` abbreviation, using Mathlib's matrix
    rank. -/
noncomputable def complexMatrixRank {m n : ℕ} (A : CMatrix m n) : ℕ :=
  Matrix.rank (A : Matrix (Fin m) (Fin n) ℂ)

/-- The local matrix rank is the dimension of the range of its Euclidean
    linear-map interpretation. This is the rank bridge needed before
    rank-sensitive SVD/Frobenius inequalities. -/
theorem complexMatrixRank_eq_finrank_range_euclideanLin {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixRank A =
      Module.finrank ℂ (LinearMap.range (complexMatrixEuclideanLin A)) := by
  rw [complexMatrixRank, complexMatrixEuclideanLin,
    Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin
    (A : Matrix (Fin m) (Fin n) ℂ)
    (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis

/-- Gram operator `A† A` attached to a complex matrix through the Euclidean
    linear-map bridge. Its eigenvalues are the squared singular values. -/
noncomputable def complexMatrixGramLin {m n : ℕ} (A : CMatrix m n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.adjoint (complexMatrixEuclideanLin A) ∘ₗ complexMatrixEuclideanLin A

/-- Matrix of the Gram map `A†A` in Euclidean coordinates. -/
theorem complexMatrixGramLin_toMatrix {m n : ℕ} (A : CMatrix m n) :
    LinearMap.toMatrix (complexEuclideanBasisFin n) (complexEuclideanBasisFin n)
        (complexMatrixGramLin A) =
      (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A := by
  rw [complexMatrixGramLin]
  rw [LinearMap.toMatrix_comp (complexEuclideanBasisFin n)
    (complexEuclideanBasisFin m) (complexEuclideanBasisFin n)]
  rw [LinearMap.toMatrix_adjoint]
  rw [complexMatrixEuclideanLin_toMatrix]

/-- If `A†A = n I`, the local Gram operator is scalar multiplication by `n`. -/
theorem complexMatrixGramLin_eq_smul_id_of_conjTranspose_mul_self {n : ℕ}
    (A : CMatrix n n)
    (hA : (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
      ((n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) :
    complexMatrixGramLin A =
      (n : ℂ) •
        (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
  let b := complexEuclideanBasisFin n
  rw [← Matrix.toLin_toMatrix b b (complexMatrixGramLin A)]
  rw [← Matrix.toLin_toMatrix b b
    ((n : ℂ) •
      (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)))]
  congr 1
  rw [complexMatrixGramLin_toMatrix, hA]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix_apply]
  · simp [LinearMap.toMatrix_apply, hij]

theorem complexMatrixGramLin_isSymmetric {m n : ℕ} (A : CMatrix m n) :
    (complexMatrixGramLin A).IsSymmetric := by
  simpa [complexMatrixGramLin] using
    LinearMap.isSymmetric_adjoint_comp_self (complexMatrixEuclideanLin A)

theorem complexMatrixGramLin_isPositive {m n : ℕ} (A : CMatrix m n) :
    (complexMatrixGramLin A).IsPositive := by
  simpa [complexMatrixGramLin] using
    LinearMap.isPositive_adjoint_comp_self (complexMatrixEuclideanLin A)

/-- The Gram operator `A†A` has the same kernel as `A`. This is the
    rank-support bridge behind the rank-sensitive singular-value bounds. -/
theorem complexMatrixGramLin_ker_eq_ker_euclideanLin {m n : ℕ}
    (A : CMatrix m n) :
    LinearMap.ker (complexMatrixGramLin A) =
      LinearMap.ker (complexMatrixEuclideanLin A) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hinner :
        inner ℂ (complexMatrixEuclideanLin A x)
            (complexMatrixEuclideanLin A x) = 0 := by
      calc
        inner ℂ (complexMatrixEuclideanLin A x)
            (complexMatrixEuclideanLin A x)
            = inner ℂ x
                (LinearMap.adjoint (complexMatrixEuclideanLin A)
                  (complexMatrixEuclideanLin A x)) := by
              rw [LinearMap.adjoint_inner_right]
        _ = inner ℂ x ((complexMatrixGramLin A) x) := by
              rfl
        _ = 0 := by simp [hx]
    exact inner_self_eq_zero.mp hinner
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    simp [complexMatrixGramLin, hx]

/-- The range dimension of the Gram operator equals the matrix rank. This is
    the finite-dimensional rank-nullity form of `ker(A†A)=ker(A)`. -/
theorem complexMatrixGramLin_finrank_range_eq_complexMatrixRank {m n : ℕ}
    (A : CMatrix m n) :
    Module.finrank ℂ (LinearMap.range (complexMatrixGramLin A)) =
      complexMatrixRank A := by
  rw [complexMatrixRank_eq_finrank_range_euclideanLin A]
  have hG := LinearMap.finrank_range_add_finrank_ker (complexMatrixGramLin A)
  have hA := LinearMap.finrank_range_add_finrank_ker (complexMatrixEuclideanLin A)
  have hker :
      Module.finrank ℂ (LinearMap.ker (complexMatrixGramLin A)) =
        Module.finrank ℂ (LinearMap.ker (complexMatrixEuclideanLin A)) := by
    rw [complexMatrixGramLin_ker_eq_ker_euclideanLin A]
  have hEq :
      Module.finrank ℂ (LinearMap.range (complexMatrixGramLin A)) +
          Module.finrank ℂ (LinearMap.ker (complexMatrixEuclideanLin A)) =
        Module.finrank ℂ (LinearMap.range (complexMatrixEuclideanLin A)) +
          Module.finrank ℂ (LinearMap.ker (complexMatrixEuclideanLin A)) := by
    calc
      Module.finrank ℂ (LinearMap.range (complexMatrixGramLin A)) +
          Module.finrank ℂ (LinearMap.ker (complexMatrixEuclideanLin A))
          = Module.finrank ℂ (LinearMap.range (complexMatrixGramLin A)) +
              Module.finrank ℂ (LinearMap.ker (complexMatrixGramLin A)) := by
              rw [hker]
      _ = Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := hG
      _ = Module.finrank ℂ (LinearMap.range (complexMatrixEuclideanLin A)) +
          Module.finrank ℂ (LinearMap.ker (complexMatrixEuclideanLin A)) := hA.symm
  exact Nat.add_right_cancel hEq

/-- Continuous-linear-map version of the Gram bridge `A† A`. -/
theorem complexMatrixGramLin_toContinuousLinearMap {m n : ℕ}
    (A : CMatrix m n) :
    (complexMatrixGramLin A).toContinuousLinearMap =
      ContinuousLinearMap.adjoint
        ((complexMatrixEuclideanLin A).toContinuousLinearMap) ∘L
        (complexMatrixEuclideanLin A).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  change
    (LinearMap.adjoint (complexMatrixEuclideanLin A))
      ((complexMatrixEuclideanLin A) x) =
      (ContinuousLinearMap.adjoint
        ((complexMatrixEuclideanLin A).toContinuousLinearMap))
        ((complexMatrixEuclideanLin A) x)
  rw [← LinearMap.adjoint_toContinuousLinearMap (complexMatrixEuclideanLin A)]
  rfl

/-- Sorted eigenvalues of `A† A`, indexed in Lean from `0` to `n - 1`.
    These are the squared singular values in source-facing order. -/
noncomputable def complexMatrixGramEigenvalues {m n : ℕ}
    (A : CMatrix m n) : Fin n → ℝ :=
  (complexMatrixGramLin_isSymmetric A).eigenvalues
    (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n))

/-- Orthonormal eigenvector basis for the Gram operator `A† A`, sorted in the
    same decreasing order as `complexMatrixGramEigenvalues`. -/
noncomputable def complexMatrixGramEigenvectorBasis {m n : ℕ}
    (A : CMatrix m n) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  (complexMatrixGramLin_isSymmetric A).eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n))

theorem complexMatrixGramEigenvalues_nonneg {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    0 ≤ complexMatrixGramEigenvalues A i := by
  simpa [complexMatrixGramEigenvalues] using
    LinearMap.IsPositive.nonneg_eigenvalues
      (complexMatrixGramLin_isPositive A)
      (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)) i

theorem complexMatrixGramEigenvalues_antitone {m n : ℕ}
    (A : CMatrix m n) :
    Antitone (complexMatrixGramEigenvalues A) := by
  simpa [complexMatrixGramEigenvalues] using
    (complexMatrixGramLin_isSymmetric A).eigenvalues_antitone
      (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n))

/-- The matrix rank is the number of nonzero Gram eigenvalues. This is the
    support-count bridge needed for rank-sensitive singular-value estimates. -/
theorem complexMatrixRank_eq_card_nonzero_gramEigenvalues {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixRank A =
      Fintype.card {i : Fin n // complexMatrixGramEigenvalues A i ≠ 0} := by
  classical
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    complexMatrixGramLin A
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)
  have hzeroCard :
      Fintype.card {i : Fin n // complexMatrixGramEigenvalues A i = 0} =
        Module.finrank ℂ (LinearMap.ker T) := by
    by_cases h0 : Module.End.HasEigenvalue (complexMatrixGramLin A) (0 : ℂ)
    · have hfilter :
          Finset.card {i : Fin n |
              (complexMatrixGramLin_isSymmetric A).eigenvalues hn i = (0 : ℂ)} =
            Module.finrank ℂ
              (Module.End.eigenspace (complexMatrixGramLin A) (0 : ℂ)) :=
        (complexMatrixGramLin_isSymmetric A).card_filter_eigenvalues_eq hn h0
      rw [Module.End.eigenspace_zero] at hfilter
      simpa [T, complexMatrixGramEigenvalues, Fintype.card_subtype] using hfilter
    · have hker_bot : LinearMap.ker T = ⊥ := by
        have heig_bot :
            Module.End.eigenspace (complexMatrixGramLin A) (0 : ℂ) = ⊥ := by
          by_contra hne
          exact h0 hne
        simpa [T, Module.End.eigenspace_zero] using heig_bot
      have hzero_empty :
          IsEmpty {i : Fin n // complexMatrixGramEigenvalues A i = 0} := by
        refine ⟨fun i => ?_⟩
        have heig :
            Module.End.HasEigenvalue (complexMatrixGramLin A) (0 : ℂ) := by
          have hi :
              (complexMatrixGramLin_isSymmetric A).eigenvalues hn i.1 =
                (0 : ℂ) := by
            simpa [complexMatrixGramEigenvalues] using i.2
          simpa [hi] using
            (complexMatrixGramLin_isSymmetric A).hasEigenvalue_eigenvalues hn i.1
        exact h0 heig
      have hcard_zero :
          Fintype.card {i : Fin n // complexMatrixGramEigenvalues A i = 0} = 0 :=
        Fintype.card_eq_zero_iff.2 hzero_empty
      rw [hcard_zero, hker_bot]
      simp
  have hnonzeroCard :
      Fintype.card {i : Fin n // complexMatrixGramEigenvalues A i ≠ 0} =
        n - Fintype.card {i : Fin n // complexMatrixGramEigenvalues A i = 0} := by
    simpa only [Fintype.card_fin, ne_eq] using
      (Fintype.card_subtype_compl
        (fun i : Fin n => complexMatrixGramEigenvalues A i = 0))
  have hrankAdd :
      complexMatrixRank A +
          Fintype.card {i : Fin n // complexMatrixGramEigenvalues A i = 0} = n := by
    rw [hzeroCard]
    rw [← complexMatrixGramLin_finrank_range_eq_complexMatrixRank A]
    simpa [T] using LinearMap.finrank_range_add_finrank_ker T
  omega

theorem complexMatrixGramLin_apply_eigenvectorBasis {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    complexMatrixGramLin A (complexMatrixGramEigenvectorBasis A i) =
      (complexMatrixGramEigenvalues A i : ℂ) •
        complexMatrixGramEigenvectorBasis A i := by
  simp [complexMatrixGramEigenvectorBasis, complexMatrixGramEigenvalues]

theorem complexMatrixGramEigenvectorBasis_norm {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    ‖complexMatrixGramEigenvectorBasis A i‖ = 1 := by
  simp [complexMatrixGramEigenvectorBasis]

/-- Source-facing singular values, zero-based in Lean: `0` corresponds to
    Higham's `σ₁`. -/
noncomputable def complexMatrixSingularValue {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) : ℝ :=
  Real.sqrt (complexMatrixGramEigenvalues A i)

theorem complexMatrixSingularValue_nonneg {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    0 ≤ complexMatrixSingularValue A i :=
  Real.sqrt_nonneg _

theorem complexMatrixSingularValue_sq {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    complexMatrixSingularValue A i ^ 2 =
      complexMatrixGramEigenvalues A i := by
  rw [complexMatrixSingularValue,
    Real.sq_sqrt (complexMatrixGramEigenvalues_nonneg A i)]

/-- A local singular value is nonzero exactly when its squared Gram eigenvalue
    is nonzero. -/
theorem complexMatrixSingularValue_ne_zero_iff_gramEigenvalue_ne_zero
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) :
    complexMatrixSingularValue A i ≠ 0 ↔
      complexMatrixGramEigenvalues A i ≠ 0 := by
  rw [complexMatrixSingularValue, Real.sqrt_ne_zero
    (complexMatrixGramEigenvalues_nonneg A i)]

/-- The matrix rank is the number of nonzero local singular values. -/
theorem complexMatrixRank_eq_card_nonzero_singularValue {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixRank A =
      Fintype.card {i : Fin n // complexMatrixSingularValue A i ≠ 0} := by
  rw [complexMatrixRank_eq_card_nonzero_gramEigenvalues A]
  apply Fintype.card_congr
  exact
  { toFun := fun i =>
      ⟨i.1,
        (complexMatrixSingularValue_ne_zero_iff_gramEigenvalue_ne_zero A i.1).2 i.2⟩
    invFun := fun i =>
      ⟨i.1,
        (complexMatrixSingularValue_ne_zero_iff_gramEigenvalue_ne_zero A i.1).1 i.2⟩
    left_inv := by intro i; rfl
    right_inv := by intro i; rfl }

theorem complexMatrixSingularValue_antitone {m n : ℕ}
    (A : CMatrix m n) :
    Antitone (complexMatrixSingularValue A) := by
  intro i j hij
  exact Real.sqrt_le_sqrt (complexMatrixGramEigenvalues_antitone A hij)

private theorem complex_re_star_mul_ofReal_mul (lam : ℝ) (c : ℂ) :
    RCLike.re (star c * ((lam : ℂ) * c)) = lam * ‖c‖ ^ 2 := by
  have hmul : star c * ((lam : ℂ) * c) =
      ((lam * ‖c‖ ^ 2 : ℝ) : ℂ) := by
    have hcc : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      simpa [RCLike.star_def] using (RCLike.conj_mul c)
    calc
      star c * ((lam : ℂ) * c) = (lam : ℂ) * (star c * c) := by ring
      _ = (lam : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [hcc]
      _ = ((lam * ‖c‖ ^ 2 : ℝ) : ℂ) := by simp
  calc
    RCLike.re (star c * ((lam : ℂ) * c)) =
        RCLike.re (((lam * ‖c‖ ^ 2 : ℝ) : ℂ)) := by
          exact congrArg Complex.re hmul
    _ = lam * ‖c‖ ^ 2 := by
          change (((lam * ‖c‖ ^ 2 : ℝ) : ℂ).re) = lam * ‖c‖ ^ 2
          rw [Complex.ofReal_re]

theorem complexMatrixGramLin_re_inner_eq_sum_gramEigenvalues_mul_repr_norm_sq
    {m n : ℕ} (A : CMatrix m n) (x : EuclideanSpace ℂ (Fin n)) :
    RCLike.re (inner ℂ x (complexMatrixGramLin A x)) =
      ∑ i : Fin n, complexMatrixGramEigenvalues A i *
        ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
  let b := complexMatrixGramEigenvectorBasis A
  have hdiag : ∀ i : Fin n, b.repr (complexMatrixGramLin A x) i =
      (complexMatrixGramEigenvalues A i : ℂ) * b.repr x i := by
    intro i
    simpa [b, complexMatrixGramEigenvalues, complexMatrixGramEigenvectorBasis] using
      (LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply
        (complexMatrixGramLin_isSymmetric A)
        (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)) x i)
  have hinner := OrthonormalBasis.sum_inner_mul_inner b x
    (complexMatrixGramLin A x)
  rw [← hinner]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hbG :
      inner ℂ (b i) (complexMatrixGramLin A x) =
        b.repr (complexMatrixGramLin A x) i := by
    rw [OrthonormalBasis.repr_apply_apply]
  have hxb : inner ℂ x (b i) = star (b.repr x i) := by
    rw [OrthonormalBasis.repr_apply_apply]
    exact (inner_conj_symm (𝕜 := ℂ) x (b i)).symm
  rw [hbG, hxb, hdiag i]
  exact complex_re_star_mul_ofReal_mul
    (complexMatrixGramEigenvalues A i) (b.repr x i)

theorem complexMatrixEuclideanLin_norm_sq_eq_sum_gramEigenvalues_mul_repr_norm_sq
    {m n : ℕ} (A : CMatrix m n) (x : EuclideanSpace ℂ (Fin n)) :
    ‖complexMatrixEuclideanLin A x‖ ^ 2 =
      ∑ i : Fin n, complexMatrixGramEigenvalues A i *
        ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
  calc
    ‖complexMatrixEuclideanLin A x‖ ^ 2 =
        RCLike.re (inner ℂ (complexMatrixEuclideanLin A x)
          (complexMatrixEuclideanLin A x)) := by
          rw [inner_self_eq_norm_sq]
    _ = RCLike.re (inner ℂ x
          ((LinearMap.adjoint (complexMatrixEuclideanLin A))
            (complexMatrixEuclideanLin A x))) := by
          rw [LinearMap.adjoint_inner_right]
    _ = RCLike.re (inner ℂ x (complexMatrixGramLin A x)) := rfl
    _ = ∑ i : Fin n, complexMatrixGramEigenvalues A i *
        ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 :=
          complexMatrixGramLin_re_inner_eq_sum_gramEigenvalues_mul_repr_norm_sq A x

theorem complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
    {m k : ℕ} (A : CMatrix m (k + 1))
    (x : EuclideanSpace ℂ (Fin (k + 1))) :
    complexMatrixSingularValue A (Fin.last k) * ‖x‖ ≤
      ‖complexMatrixEuclideanLin A x‖ := by
  let b := complexMatrixGramEigenvectorBasis A
  have hnorm_repr :
      (∑ i : Fin (k + 1), ‖b.repr x i‖ ^ 2) = ‖x‖ ^ 2 := by
    simpa [b, OrthonormalBasis.repr_apply_apply] using
      (OrthonormalBasis.sum_sq_norm_inner_right b x)
  have hlast_le : ∀ i : Fin (k + 1),
      complexMatrixGramEigenvalues A (Fin.last k) ≤
        complexMatrixGramEigenvalues A i := by
    intro i
    exact complexMatrixGramEigenvalues_antitone A (Fin.le_last i)
  have hsq : (complexMatrixSingularValue A (Fin.last k) * ‖x‖) ^ 2 ≤
      ‖complexMatrixEuclideanLin A x‖ ^ 2 := by
    rw [mul_pow, complexMatrixSingularValue_sq]
    calc
      complexMatrixGramEigenvalues A (Fin.last k) * ‖x‖ ^ 2 =
          complexMatrixGramEigenvalues A (Fin.last k) *
            (∑ i : Fin (k + 1), ‖b.repr x i‖ ^ 2) := by
            rw [hnorm_repr]
      _ = ∑ i : Fin (k + 1),
          complexMatrixGramEigenvalues A (Fin.last k) *
            ‖b.repr x i‖ ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin (k + 1),
          complexMatrixGramEigenvalues A i * ‖b.repr x i‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro i _hi
            exact mul_le_mul_of_nonneg_right (hlast_le i) (sq_nonneg _)
      _ = ‖complexMatrixEuclideanLin A x‖ ^ 2 := by
            rw [complexMatrixEuclideanLin_norm_sq_eq_sum_gramEigenvalues_mul_repr_norm_sq]
  exact
    (sq_le_sq₀
      (mul_nonneg (complexMatrixSingularValue_nonneg A (Fin.last k))
        (norm_nonneg x))
      (norm_nonneg (complexMatrixEuclideanLin A x))).mp hsq

/-- Applying the Euclidean linear-map bridge to a coordinate basis vector
    extracts the corresponding column of the source-facing matrix. -/
theorem complexMatrixEuclideanLin_basisFun {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j) =
      WithLp.toLp (2 : ENNReal) (fun i : Fin m => A i j) := by
  apply WithLp.ofLp_injective
  calc
    WithLp.ofLp
        (complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j)) =
        complexMatrixVecMul A
          (WithLp.ofLp (EuclideanSpace.basisFun (Fin n) ℂ j)) := by
      rfl
    _ = complexMatrixVecMul A (standardBasisCVec j) := by
      congr
      ext k
      simp [standardBasisCVec]
    _ = fun i : Fin m => A i j := complexMatrixVecMul_standardBasisCVec A j
    _ = WithLp.ofLp (WithLp.toLp (2 : ENNReal) (fun i : Fin m => A i j)) := by
      simp

/-- Squared Euclidean norm of a matrix column, expressed through the
    `Matrix.toEuclideanLin` bridge. -/
theorem complexMatrixEuclideanLin_norm_sq_basisFun {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    ‖complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2 =
      ∑ i : Fin m, ‖A i j‖ ^ 2 := by
  have hcol :
      WithLp.ofLp
        (complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j)) =
        fun i : Fin m => A i j := by
    calc
      WithLp.ofLp
          (complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j)) =
          complexMatrixVecMul A
            (WithLp.ofLp (EuclideanSpace.basisFun (Fin n) ℂ j)) := by
        rfl
      _ = complexMatrixVecMul A (standardBasisCVec j) := by
        congr
        ext k
        simp [standardBasisCVec]
      _ = fun i : Fin m => A i j := complexMatrixVecMul_standardBasisCVec A j
  rw [EuclideanSpace.norm_sq_eq]
  rw [hcol]

/-- The coordinate-basis diagonal entry of `A† A` is the squared Euclidean
    norm of the corresponding column of `A`. -/
theorem complexMatrixGramLin_basisFun_re_inner {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    RCLike.re
      (inner ℂ (EuclideanSpace.basisFun (Fin n) ℂ j)
        (complexMatrixGramLin A (EuclideanSpace.basisFun (Fin n) ℂ j))) =
      ∑ i : Fin m, ‖A i j‖ ^ 2 := by
  rw [show inner ℂ (EuclideanSpace.basisFun (Fin n) ℂ j)
        (complexMatrixGramLin A (EuclideanSpace.basisFun (Fin n) ℂ j)) =
        inner ℂ
          (complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j))
          (complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j)) by
    simp [complexMatrixGramLin, LinearMap.adjoint_inner_right]]
  rw [inner_self_eq_norm_sq]
  exact complexMatrixEuclideanLin_norm_sq_basisFun A j

/-- Complex rectangular Frobenius norm squared, as the sum of squared entry
    moduli. -/
noncomputable def complexMatrixFrobeniusSq {m n : ℕ} (A : CMatrix m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ ^ 2

/-- Complex rectangular Frobenius norm, source-facing for Higham's `||A||_F`.
    This explicit wrapper avoids relying on scoped matrix norm instances. -/
noncomputable def complexMatrixFrobenius {m n : ℕ} (A : CMatrix m n) : ℝ :=
  Real.sqrt (complexMatrixFrobeniusSq A)

theorem complexMatrixFrobeniusSq_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixFrobeniusSq A := by
  unfold complexMatrixFrobeniusSq
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖

theorem complexMatrixFrobenius_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixFrobenius A :=
  Real.sqrt_nonneg _

theorem complexMatrixFrobenius_sq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobenius A ^ 2 = complexMatrixFrobeniusSq A := by
  rw [complexMatrixFrobenius, Real.sq_sqrt (complexMatrixFrobeniusSq_nonneg A)]

/-- Entrywise absolute value preserves the complex Frobenius square. -/
theorem complexMatrixFrobeniusSq_absMatrix_eq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobeniusSq (complexAbsMatrix A) = complexMatrixFrobeniusSq A := by
  simp [complexMatrixFrobeniusSq]

/-- Entrywise absolute value preserves the complex Frobenius norm. -/
theorem complexMatrixFrobenius_absMatrix_eq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobenius (complexAbsMatrix A) = complexMatrixFrobenius A := by
  rw [complexMatrixFrobenius, complexMatrixFrobenius,
    complexMatrixFrobeniusSq_absMatrix_eq]

theorem complexMatrixFrobeniusSq_adjoint_eq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobeniusSq (complexMatrixAdjoint A) = complexMatrixFrobeniusSq A := by
  unfold complexMatrixFrobeniusSq complexMatrixAdjoint complexMatrixTranspose complexConjMatrix
  rw [Finset.sum_comm]
  simp

theorem complexMatrixFrobenius_adjoint_eq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobenius (complexMatrixAdjoint A) = complexMatrixFrobenius A := by
  rw [complexMatrixFrobenius, complexMatrixFrobenius,
    complexMatrixFrobeniusSq_adjoint_eq]

/-- Source-facing entrywise maximum norm `||A||_M := max_{i,j} |a_ij|`
    from Higham Table 6.2. -/
noncomputable def complexMatrixEntrywiseMaxNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  ‖fun ij : Fin m × Fin n => A ij.1 ij.2‖

/-- Source-facing entrywise sum norm `||A||_S := sum_{i,j} |a_ij|`
    from Higham Table 6.2. -/
noncomputable def complexMatrixEntrywiseSumNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  ∑ ij : Fin m × Fin n, ‖A ij.1 ij.2‖

lemma complexMatrixEntrywiseMaxNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixEntrywiseMaxNorm A := by
  unfold complexMatrixEntrywiseMaxNorm
  exact norm_nonneg _

lemma complexMatrixEntrywiseMaxNorm_coord_le {m n : ℕ} (A : CMatrix m n)
    (i : Fin m) (j : Fin n) :
    ‖A i j‖ ≤ complexMatrixEntrywiseMaxNorm A := by
  unfold complexMatrixEntrywiseMaxNorm
  simpa using norm_le_pi_norm (fun ij : Fin m × Fin n => A ij.1 ij.2) (i, j)

lemma complexMatrixEntrywiseMaxNorm_le_of_coord_le {m n : ℕ} (A : CMatrix m n)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖A i j‖ ≤ c) :
    complexMatrixEntrywiseMaxNorm A ≤ c := by
  unfold complexMatrixEntrywiseMaxNorm
  rw [pi_norm_le_iff_of_nonneg hc]
  intro ij
  exact h ij.1 ij.2

lemma complexMatrixEntrywiseSumNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixEntrywiseSumNorm A := by
  unfold complexMatrixEntrywiseSumNorm
  exact Finset.sum_nonneg fun ij _ => norm_nonneg (A ij.1 ij.2)

lemma complexMatrixEntrywiseSumNorm_coord_le {m n : ℕ} (A : CMatrix m n)
    (i : Fin m) (j : Fin n) :
    ‖A i j‖ ≤ complexMatrixEntrywiseSumNorm A := by
  unfold complexMatrixEntrywiseSumNorm
  exact Finset.single_le_sum
    (fun ij _ => norm_nonneg (A ij.1 ij.2))
    (Finset.mem_univ (i, j))

lemma complexMatrixEntrywiseMaxNorm_le_sumNorm {m n : ℕ} (A : CMatrix m n) :
    complexMatrixEntrywiseMaxNorm A ≤ complexMatrixEntrywiseSumNorm A := by
  exact complexMatrixEntrywiseMaxNorm_le_of_coord_le A
    (complexMatrixEntrywiseSumNorm_nonneg A)
    (fun i j => complexMatrixEntrywiseSumNorm_coord_le A i j)

/-- Product-index form of the Frobenius square, convenient for Table 6.2
    entrywise `M` and `S` comparisons. -/
lemma complexMatrixFrobeniusSq_eq_entrywise_sum {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobeniusSq A =
      ∑ ij : Fin m × Fin n, ‖A ij.1 ij.2‖ ^ 2 := by
  unfold complexMatrixFrobeniusSq
  simpa using
    (Fintype.sum_prod_type' (fun i : Fin m => fun j : Fin n => ‖A i j‖ ^ 2)).symm

/-- Frobenius square as a sum of squared Euclidean norms of columns. -/
lemma complexMatrixFrobeniusSq_eq_sum_col_norm_sq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobeniusSq A =
      Finset.univ.sum (fun j : Fin n =>
        (norm (complexMatrixEuclideanLin A
          (EuclideanSpace.basisFun (Fin n) Complex j))) ^ 2) := by
  unfold complexMatrixFrobeniusSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (complexMatrixEuclideanLin_norm_sq_basisFun A j).symm

/-- Table 6.2 `S` versus `M` entry:
    `||A||_S <= mn ||A||_M`. -/
theorem complexMatrixEntrywiseSumNorm_le_card_mul_entrywiseMaxNorm
    {m n : ℕ} (A : CMatrix m n) :
    complexMatrixEntrywiseSumNorm A ≤
      ((m * n : ℕ) : ℝ) * complexMatrixEntrywiseMaxNorm A := by
  calc
    complexMatrixEntrywiseSumNorm A
        ≤ ∑ _ij : Fin m × Fin n, complexMatrixEntrywiseMaxNorm A := by
          unfold complexMatrixEntrywiseSumNorm
          exact Finset.sum_le_sum fun ij _ =>
            complexMatrixEntrywiseMaxNorm_coord_le A ij.1 ij.2
    _ = ((m * n : ℕ) : ℝ) * complexMatrixEntrywiseMaxNorm A := by
          simp [Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]

/-- Table 6.2 `M` versus `F` entry:
    `||A||_M <= ||A||_F`. -/
theorem complexMatrixEntrywiseMaxNorm_le_frobenius {m n : ℕ} (A : CMatrix m n) :
    complexMatrixEntrywiseMaxNorm A ≤ complexMatrixFrobenius A := by
  apply complexMatrixEntrywiseMaxNorm_le_of_coord_le A (complexMatrixFrobenius_nonneg A)
  intro i j
  apply (sq_le_sq₀ (norm_nonneg _) (complexMatrixFrobenius_nonneg A)).mp
  rw [complexMatrixFrobenius_sq, complexMatrixFrobeniusSq_eq_entrywise_sum]
  exact Finset.single_le_sum
    (fun ij _ => sq_nonneg ‖A ij.1 ij.2‖)
    (Finset.mem_univ (i, j))

/-- Table 6.2 `F` versus `S` entry:
    `||A||_F <= ||A||_S`. -/
theorem complexMatrixFrobenius_le_entrywiseSumNorm {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobenius A ≤ complexMatrixEntrywiseSumNorm A := by
  apply (sq_le_sq₀ (complexMatrixFrobenius_nonneg A)
    (complexMatrixEntrywiseSumNorm_nonneg A)).mp
  rw [complexMatrixFrobenius_sq, complexMatrixFrobeniusSq_eq_entrywise_sum]
  calc
    (∑ ij : Fin m × Fin n, ‖A ij.1 ij.2‖ ^ 2)
        ≤ ∑ ij : Fin m × Fin n,
            complexMatrixEntrywiseSumNorm A * ‖A ij.1 ij.2‖ := by
          apply Finset.sum_le_sum
          intro ij _hi
          have hcoord := complexMatrixEntrywiseSumNorm_coord_le A ij.1 ij.2
          nlinarith [norm_nonneg (A ij.1 ij.2)]
    _ = complexMatrixEntrywiseSumNorm A *
        complexMatrixEntrywiseSumNorm A := by
          rw [← Finset.mul_sum]
          rfl
    _ = complexMatrixEntrywiseSumNorm A ^ 2 := by ring

/-- Table 6.2 `S` versus `F` entry:
    `||A||_S <= sqrt(mn) ||A||_F`. -/
theorem complexMatrixEntrywiseSumNorm_le_sqrt_card_mul_frobenius {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixEntrywiseSumNorm A ≤
      Real.sqrt ((m * n : ℕ) : ℝ) * complexMatrixFrobenius A := by
  have hholder :=
    Real.inner_le_weight_mul_Lp_of_nonneg (s := Finset.univ) (p := (2 : ℝ))
      (by norm_num)
      (w := fun _ij : Fin m × Fin n => (1 : ℝ))
      (f := fun ij : Fin m × Fin n => ‖A ij.1 ij.2‖)
      (by intro ij; exact zero_le_one)
      (by intro ij; exact norm_nonneg (A ij.1 ij.2))
  have hcard :
      (∑ _ij : Fin m × Fin n, (1 : ℝ)) = ((m * n : ℕ) : ℝ) := by
    simp [Fintype.card_prod, Nat.cast_mul]
  have hhalf : (1 : ℝ) - (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
  have hinv_two : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
  have hsqprod := complexMatrixFrobeniusSq_eq_entrywise_sum A
  calc
    complexMatrixEntrywiseSumNorm A
        = ∑ ij : Fin m × Fin n, (1 : ℝ) * ‖A ij.1 ij.2‖ := by
          simp [complexMatrixEntrywiseSumNorm]
    _ ≤ (∑ _ij : Fin m × Fin n, (1 : ℝ)) ^ (1 - (2 : ℝ)⁻¹) *
        (∑ ij : Fin m × Fin n, (1 : ℝ) * ‖A ij.1 ij.2‖ ^ (2 : ℝ)) ^
          (2 : ℝ)⁻¹ := hholder
    _ = Real.sqrt ((m * n : ℕ) : ℝ) * complexMatrixFrobenius A := by
          rw [hcard, hhalf, hinv_two]
          rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          simp [complexMatrixFrobenius, hsqprod]

/-- Squared form of the Table 6.2 `S` versus `F` Cauchy-Schwarz entry. -/
theorem complexMatrixEntrywiseSumNorm_sq_le_card_mul_frobeniusSq {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixEntrywiseSumNorm A ^ 2 ≤
      ((m * n : ℕ) : ℝ) * complexMatrixFrobeniusSq A := by
  have h := complexMatrixEntrywiseSumNorm_le_sqrt_card_mul_frobenius A
  have hsq :
      complexMatrixEntrywiseSumNorm A ^ 2 ≤
        (Real.sqrt ((m * n : ℕ) : ℝ) * complexMatrixFrobenius A) ^ 2 :=
    (sq_le_sq₀ (complexMatrixEntrywiseSumNorm_nonneg A)
      (mul_nonneg (Real.sqrt_nonneg _) (complexMatrixFrobenius_nonneg A))).mpr h
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), complexMatrixFrobenius_sq] at hsq
  exact hsq

/-- Table 6.2 `F` versus `M` entry:
    `||A||_F <= sqrt(mn) ||A||_M`. -/
theorem complexMatrixFrobenius_le_sqrt_card_mul_entrywiseMaxNorm {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobenius A ≤
      Real.sqrt ((m * n : ℕ) : ℝ) * complexMatrixEntrywiseMaxNorm A := by
  have hM_nonneg := complexMatrixEntrywiseMaxNorm_nonneg A
  apply (sq_le_sq₀ (complexMatrixFrobenius_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) hM_nonneg)).mp
  rw [complexMatrixFrobenius_sq, complexMatrixFrobeniusSq_eq_entrywise_sum]
  calc
    (∑ ij : Fin m × Fin n, ‖A ij.1 ij.2‖ ^ 2)
        ≤ ∑ _ij : Fin m × Fin n, complexMatrixEntrywiseMaxNorm A ^ 2 := by
          apply Finset.sum_le_sum
          intro ij _hi
          exact (sq_le_sq₀ (norm_nonneg _) hM_nonneg).mpr
            (complexMatrixEntrywiseMaxNorm_coord_le A ij.1 ij.2)
    _ = ((m * n : ℕ) : ℝ) * complexMatrixEntrywiseMaxNorm A ^ 2 := by
          simp [Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
    _ = (Real.sqrt ((m * n : ℕ) : ℝ) * complexMatrixEntrywiseMaxNorm A) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Source-facing rank-one matrix `x y^T`, without conjugating the second
    factor. This is the witness family used in Higham Problem 6.1. -/
noncomputable def complexMatrixRankOne {m n : ℕ} (x : CVec m) (y : CVec n) :
    CMatrix m n :=
  fun i j => x i * y j

/-- The standard-basis rank-one witness `e_i e_j^T` has matrix rank one. -/
theorem complexMatrixRank_rankOne_standard_standard {m n : Nat}
    (i0 : Fin m) (j0 : Fin n) :
    complexMatrixRank
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) = 1 := by
  unfold complexMatrixRank
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan :
      Submodule.span Complex
          (Set.range
            (Matrix.col
              (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0) :
                Matrix (Fin m) (Fin n) Complex))) =
        Complex ∙ standardBasisCVec i0 := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      by_cases hj : j = j0
      · rw [hj]
        have hcol :
            Matrix.col
                (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0) :
                  Matrix (Fin m) (Fin n) Complex) j0 =
              standardBasisCVec i0 := by
          ext i
          simp [complexMatrixRankOne, standardBasisCVec]
        rw [hcol]
        exact Submodule.mem_span_singleton_self (standardBasisCVec i0)
      · have hcol :
            Matrix.col
                (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0) :
                  Matrix (Fin m) (Fin n) Complex) j =
              0 := by
          ext i
          simp [complexMatrixRankOne, standardBasisCVec, hj]
        rw [hcol]
        exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      apply Submodule.subset_span
      refine ⟨j0, ?_⟩
      ext i
      simp [complexMatrixRankOne, standardBasisCVec]
  rw [hspan]
  exact finrank_span_singleton (standardBasisCVec_ne_zero i0)

lemma complexMatrixEntrywiseSumNorm_eq_sum_sum {m n : ℕ} (A : CMatrix m n) :
    complexMatrixEntrywiseSumNorm A = ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ := by
  unfold complexMatrixEntrywiseSumNorm
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]

theorem complexMatrixEntrywiseSumNorm_rankOne {m n : ℕ}
    (x : CVec m) (y : CVec n) :
    complexMatrixEntrywiseSumNorm (complexMatrixRankOne x y) =
      complexVecOneNorm x * complexVecOneNorm y := by
  rw [complexMatrixEntrywiseSumNorm_eq_sum_sum]
  unfold complexMatrixRankOne complexVecOneNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, ‖x i * y j‖)
        = ∑ i : Fin m, ∑ j : Fin n, ‖x i‖ * ‖y j‖ := by
          simp
    _ = ∑ i : Fin m, ‖x i‖ * ∑ j : Fin n, ‖y j‖ := by
          simp [Finset.mul_sum]
    _ = (∑ i : Fin m, ‖x i‖) * (∑ j : Fin n, ‖y j‖) := by
          rw [Finset.sum_mul]

theorem complexMatrixEntrywiseSumNorm_rankOne_standard_standard {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) :
    complexMatrixEntrywiseSumNorm
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) = 1 := by
  rw [complexMatrixEntrywiseSumNorm_rankOne]
  rw [complexVecOneNorm_standardBasisCVec, complexVecOneNorm_standardBasisCVec]
  norm_num

theorem complexMatrixEntrywiseSumNorm_rankOne_const_standard {m n : ℕ}
    (j0 : Fin n) :
    complexMatrixEntrywiseSumNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) =
      (m : ℝ) := by
  rw [complexMatrixEntrywiseSumNorm_rankOne]
  rw [complexVecOneNorm_const_one, complexVecOneNorm_standardBasisCVec]
  ring

theorem complexMatrixEntrywiseSumNorm_rankOne_standard_const {m n : ℕ}
    (i0 : Fin m) :
    complexMatrixEntrywiseSumNorm
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) =
      (n : ℝ) := by
  rw [complexMatrixEntrywiseSumNorm_rankOne]
  rw [complexVecOneNorm_standardBasisCVec, complexVecOneNorm_const_one]
  ring

theorem complexMatrixEntrywiseSumNorm_rankOne_const_const {m n : ℕ} :
    complexMatrixEntrywiseSumNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) =
      ((m * n : ℕ) : ℝ) := by
  rw [complexMatrixEntrywiseSumNorm_rankOne]
  rw [complexVecOneNorm_const_one, complexVecOneNorm_const_one]
  norm_num

theorem complexMatrixFrobeniusSq_rankOne {m n : ℕ}
    (x : CVec m) (y : CVec n) :
    complexMatrixFrobeniusSq (complexMatrixRankOne x y) =
      (∑ i : Fin m, ‖x i‖ ^ 2) * (∑ j : Fin n, ‖y j‖ ^ 2) := by
  unfold complexMatrixFrobeniusSq complexMatrixRankOne
  calc
    (∑ i : Fin m, ∑ j : Fin n, ‖x i * y j‖ ^ 2)
        = ∑ i : Fin m, ∑ j : Fin n, (‖x i‖ ^ 2) * (‖y j‖ ^ 2) := by
          simp [mul_pow]
    _ = ∑ i : Fin m, (‖x i‖ ^ 2) * ∑ j : Fin n, ‖y j‖ ^ 2 := by
          simp [Finset.mul_sum]
    _ = (∑ i : Fin m, ‖x i‖ ^ 2) * (∑ j : Fin n, ‖y j‖ ^ 2) := by
          rw [Finset.sum_mul]

theorem complexMatrixFrobenius_rankOne_standard_standard {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) :
    complexMatrixFrobenius
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) = 1 := by
  rw [complexMatrixFrobenius, complexMatrixFrobeniusSq_rankOne]
  rw [complexVecNormSqSum_standardBasisCVec, complexVecNormSqSum_standardBasisCVec]
  norm_num

theorem complexMatrixFrobenius_rankOne_const_standard {m n : ℕ}
    (j0 : Fin n) :
    complexMatrixFrobenius
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) =
      Real.sqrt (m : ℝ) := by
  rw [complexMatrixFrobenius, complexMatrixFrobeniusSq_rankOne]
  rw [complexVecNormSqSum_const_one, complexVecNormSqSum_standardBasisCVec]
  ring_nf

theorem complexMatrixFrobenius_rankOne_standard_const {m n : ℕ}
    (i0 : Fin m) :
    complexMatrixFrobenius
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) =
      Real.sqrt (n : ℝ) := by
  rw [complexMatrixFrobenius, complexMatrixFrobeniusSq_rankOne]
  rw [complexVecNormSqSum_standardBasisCVec, complexVecNormSqSum_const_one]
  ring_nf

theorem complexMatrixFrobenius_rankOne_const_const {m n : ℕ} :
    complexMatrixFrobenius
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) =
      Real.sqrt ((m * n : ℕ) : ℝ) := by
  rw [complexMatrixFrobenius, complexMatrixFrobeniusSq_rankOne]
  rw [complexVecNormSqSum_const_one, complexVecNormSqSum_const_one]
  norm_num

theorem complexMatrixEntrywiseMaxNorm_rankOne_const_const {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    complexMatrixEntrywiseMaxNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) = 1 := by
  let i0 : Fin m := { val := 0, isLt := hm }
  let j0 : Fin n := { val := 0, isLt := hn }
  apply le_antisymm
  · apply complexMatrixEntrywiseMaxNorm_le_of_coord_le _ zero_le_one
    intro i j
    simp [complexMatrixRankOne]
  · have h := complexMatrixEntrywiseMaxNorm_coord_le
      (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) i0 j0
    simpa [complexMatrixRankOne] using h

theorem complexMatrixEntrywiseMaxNorm_rankOne_standard_standard {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) :
    complexMatrixEntrywiseMaxNorm
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) = 1 := by
  apply le_antisymm
  · apply complexMatrixEntrywiseMaxNorm_le_of_coord_le _ zero_le_one
    intro i j
    by_cases hi : i = i0
    · by_cases hj : j = j0
      · simp [complexMatrixRankOne, standardBasisCVec, hi, hj]
      · simp [complexMatrixRankOne, standardBasisCVec, hi, hj]
    · simp [complexMatrixRankOne, standardBasisCVec, hi]
  · have h := complexMatrixEntrywiseMaxNorm_coord_le
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) i0 j0
    simpa [complexMatrixRankOne, standardBasisCVec] using h

theorem complexMatrixEntrywiseMaxNorm_rankOne_const_standard {m n : ℕ}
    (hm : 0 < m) (j0 : Fin n) :
    complexMatrixEntrywiseMaxNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) = 1 := by
  let i0 : Fin m := { val := 0, isLt := hm }
  apply le_antisymm
  · apply complexMatrixEntrywiseMaxNorm_le_of_coord_le _ zero_le_one
    intro i j
    by_cases hj : j = j0
    · simp [complexMatrixRankOne, standardBasisCVec, hj]
    · simp [complexMatrixRankOne, standardBasisCVec, hj]
  · have h := complexMatrixEntrywiseMaxNorm_coord_le
      (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) i0 j0
    simpa [complexMatrixRankOne, standardBasisCVec] using h

theorem complexMatrixEntrywiseMaxNorm_rankOne_standard_const {m n : ℕ}
    (i0 : Fin m) (hn : 0 < n) :
    complexMatrixEntrywiseMaxNorm
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) = 1 := by
  let j0 : Fin n := { val := 0, isLt := hn }
  apply le_antisymm
  · apply complexMatrixEntrywiseMaxNorm_le_of_coord_le _ zero_le_one
    intro i j
    by_cases hi : i = i0
    · simp [complexMatrixRankOne, standardBasisCVec, hi]
    · simp [complexMatrixRankOne, standardBasisCVec, hi]
  · have h := complexMatrixEntrywiseMaxNorm_coord_le
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) i0 j0
    simpa [complexMatrixRankOne, standardBasisCVec] using h

/-- The entrywise Frobenius square is the real trace of the Gram operator
    `A† A`. -/
theorem complexMatrixFrobeniusSq_eq_re_trace_gramLin {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobeniusSq A =
      RCLike.re
        ((complexMatrixGramLin A).trace ℂ (EuclideanSpace ℂ (Fin n))) := by
  rw [LinearMap.trace_eq_sum_inner (complexMatrixGramLin A)
    (EuclideanSpace.basisFun (Fin n) ℂ)]
  unfold complexMatrixFrobeniusSq
  change (∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ ^ 2) =
    (∑ j : Fin n,
      inner ℂ (EuclideanSpace.basisFun (Fin n) ℂ j)
        (complexMatrixGramLin A (EuclideanSpace.basisFun (Fin n) ℂ j))).re
  rw [Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  symm
  exact complexMatrixGramLin_basisFun_re_inner A j

/-- Real trace of the Gram operator as the sum of the sorted Gram eigenvalues. -/
theorem complexMatrixGramLin_re_trace_eq_sum_gramEigenvalues {m n : ℕ}
    (A : CMatrix m n) :
    RCLike.re
      ((complexMatrixGramLin A).trace ℂ (EuclideanSpace ℂ (Fin n))) =
      ∑ i : Fin n, complexMatrixGramEigenvalues A i := by
  simpa [complexMatrixGramEigenvalues] using
    LinearMap.IsSymmetric.re_trace_eq_sum_eigenvalues
      (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n))
      (complexMatrixGramLin_isSymmetric A)

/-- Frobenius square as the sum of the sorted Gram eigenvalues. -/
theorem complexMatrixFrobeniusSq_eq_sum_gramEigenvalues {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobeniusSq A =
      ∑ i : Fin n, complexMatrixGramEigenvalues A i := by
  rw [complexMatrixFrobeniusSq_eq_re_trace_gramLin,
    complexMatrixGramLin_re_trace_eq_sum_gramEigenvalues]

/-- Frobenius square as the sum of squared local singular values. This is the
    squared form of Higham's Chapter 6 SVD/Frobenius identity. -/
theorem complexMatrixFrobeniusSq_eq_sum_singularValue_sq {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobeniusSq A =
      ∑ i : Fin n, complexMatrixSingularValue A i ^ 2 := by
  rw [complexMatrixFrobeniusSq_eq_sum_gramEigenvalues]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← complexMatrixSingularValue_sq]

/-- Source-facing Frobenius norm formula in terms of the local singular
    values: `||A||_F = sqrt (sum_i sigma_i^2)`. -/
theorem complexMatrixFrobenius_eq_sqrt_sum_singularValue_sq {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobenius A =
      Real.sqrt (∑ i : Fin n, complexMatrixSingularValue A i ^ 2) := by
  rw [complexMatrixFrobenius, complexMatrixFrobeniusSq_eq_sum_singularValue_sq]

theorem complexMatrixEuclideanLin_norm_sq_gramEigenvectorBasis {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    ‖complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)‖ ^ 2 =
      complexMatrixGramEigenvalues A i := by
  apply Complex.ofReal_injective
  calc
    ((‖complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)‖ ^ 2 : ℝ) : ℂ)
        = inner ℂ (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i))
            (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)) := by
          simp [inner_self_eq_norm_sq_to_K]
    _ = inner ℂ (complexMatrixGramEigenvectorBasis A i)
            (complexMatrixGramLin A (complexMatrixGramEigenvectorBasis A i)) := by
          simp [complexMatrixGramLin, LinearMap.adjoint_inner_right]
    _ = ((complexMatrixGramEigenvalues A i : ℝ) : ℂ) := by
          rw [inner_product_apply_eigenvector
            (complexMatrixGramLin_apply_eigenvectorBasis A i)]
          simp [complexMatrixGramEigenvectorBasis]

theorem complexMatrixSingularValue_eq_norm_euclideanLin_gramEigenvectorBasis
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) :
    complexMatrixSingularValue A i =
      ‖complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)‖ := by
  rw [complexMatrixSingularValue,
    ← complexMatrixEuclideanLin_norm_sq_gramEigenvectorBasis A i]
  exact Real.sqrt_sq (norm_nonneg _)

/-- The Gram eigenvector attached to a displayed singular value attains that
    singular value in the Euclidean operator action. -/
theorem complexMatrixSingularValue_mul_norm_gramEigenvectorBasis_eq_norm_euclideanLin
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) :
    complexMatrixSingularValue A i * ‖complexMatrixGramEigenvectorBasis A i‖ =
      ‖complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)‖ := by
  rw [complexMatrixGramEigenvectorBasis_norm]
  simpa using complexMatrixSingularValue_eq_norm_euclideanLin_gramEigenvectorBasis A i

/-- Every displayed singular value has a nonzero Gram-eigenvector witness
    attaining it. -/
theorem complexMatrixSingularValue_exists_attaining_vector
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) :
    ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 ∧
      complexMatrixSingularValue A i * ‖x‖ =
        ‖complexMatrixEuclideanLin A x‖ := by
  refine ⟨complexMatrixGramEigenvectorBasis A i, ?_, ?_⟩
  · intro hx
    have hnorm := complexMatrixGramEigenvectorBasis_norm A i
    rw [hx, norm_zero] at hnorm
    norm_num at hnorm
  · exact
      complexMatrixSingularValue_mul_norm_gramEigenvectorBasis_eq_norm_euclideanLin
        A i

/-- Squared-norm version of the Gram-eigenvector singular-value attainment
    certificate. -/
theorem complexMatrixSingularValue_exists_attaining_vector_sq
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) :
    ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 ∧
      ‖complexMatrixEuclideanLin A x‖ ^ 2 =
        (complexMatrixSingularValue A i) ^ 2 * ‖x‖ ^ 2 := by
  refine ⟨complexMatrixGramEigenvectorBasis A i, ?_, ?_⟩
  · intro hx
    have hnorm := complexMatrixGramEigenvectorBasis_norm A i
    rw [hx, norm_zero] at hnorm
    norm_num at hnorm
  · have hattain :=
      complexMatrixSingularValue_mul_norm_gramEigenvectorBasis_eq_norm_euclideanLin
        A i
    calc
      ‖complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)‖ ^ 2 =
          (complexMatrixSingularValue A i *
            ‖complexMatrixGramEigenvectorBasis A i‖) ^ 2 := by
            rw [hattain]
      _ =
          (complexMatrixSingularValue A i) ^ 2 *
            ‖complexMatrixGramEigenvectorBasis A i‖ ^ 2 := by
            ring

/-- Inner products of the images `A v_i` of the sorted Gram eigenvector basis.
    This is the local SVD bridge showing that these images are orthogonal and
    have squared norms given by the Gram eigenvalues. -/
theorem complexMatrixEuclideanLin_gramEigenvectorBasis_inner {m n : ℕ}
    (A : CMatrix m n) (i j : Fin n) :
    inner ℂ (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i))
      (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A j)) =
      (complexMatrixGramEigenvalues A j : ℂ) *
        inner ℂ (complexMatrixGramEigenvectorBasis A i)
          (complexMatrixGramEigenvectorBasis A j) := by
  calc
    inner ℂ (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i))
        (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A j))
        = inner ℂ (complexMatrixGramEigenvectorBasis A i)
            (complexMatrixGramLin A (complexMatrixGramEigenvectorBasis A j)) := by
          simp [complexMatrixGramLin, LinearMap.adjoint_inner_right]
    _ = inner ℂ (complexMatrixGramEigenvectorBasis A i)
        ((complexMatrixGramEigenvalues A j : ℂ) •
          complexMatrixGramEigenvectorBasis A j) := by
          rw [complexMatrixGramLin_apply_eigenvectorBasis]
    _ = (complexMatrixGramEigenvalues A j : ℂ) *
        inner ℂ (complexMatrixGramEigenvectorBasis A i)
          (complexMatrixGramEigenvectorBasis A j) := by
          rw [inner_smul_right]

theorem complexMatrixEuclideanLin_gramEigenvectorBasis_inner_self
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) :
    inner ℂ (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i))
      (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)) =
      (complexMatrixGramEigenvalues A i : ℂ) := by
  rw [complexMatrixEuclideanLin_gramEigenvectorBasis_inner]
  simp [complexMatrixGramEigenvectorBasis]

theorem complexMatrixEuclideanLin_gramEigenvectorBasis_inner_eq_zero_of_ne
    {m n : ℕ} (A : CMatrix m n) {i j : Fin n} (hij : i ≠ j) :
    inner ℂ (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i))
      (complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A j)) = 0 := by
  rw [complexMatrixEuclideanLin_gramEigenvectorBasis_inner]
  simp [complexMatrixGramEigenvectorBasis, hij]

/-- Normalized left singular vector candidate attached to a nonzero local
    singular value. When the singular value is zero this total definition
    returns the zero vector; the unit and reconstruction theorems expose the
    nonzero hypotheses explicitly. -/
noncomputable def complexMatrixLeftSingularVector {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) : EuclideanSpace ℂ (Fin m) :=
  ((complexMatrixSingularValue A i : ℂ)⁻¹) •
    complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)

theorem complexMatrixLeftSingularVector_norm_of_ne_zero {m n : ℕ}
    (A : CMatrix m n) (i : Fin n)
    (hσ : complexMatrixSingularValue A i ≠ 0) :
    ‖complexMatrixLeftSingularVector A i‖ = 1 := by
  have hσ_nonneg : 0 ≤ complexMatrixSingularValue A i :=
    complexMatrixSingularValue_nonneg A i
  rw [complexMatrixLeftSingularVector, norm_smul,
    ← complexMatrixSingularValue_eq_norm_euclideanLin_gramEigenvectorBasis A i]
  rw [norm_inv]
  rw [Complex.norm_of_nonneg hσ_nonneg]
  rw [inv_mul_cancel₀ hσ]

theorem complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left
    {m n : ℕ} (A : CMatrix m n) (i : Fin n)
    (hσ : complexMatrixSingularValue A i ≠ 0) :
    complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i) =
      (complexMatrixSingularValue A i : ℂ) •
        complexMatrixLeftSingularVector A i := by
  rw [complexMatrixLeftSingularVector, smul_smul]
  have hσC : (complexMatrixSingularValue A i : ℂ) ≠ 0 := by
    exact_mod_cast hσ
  rw [mul_inv_cancel₀ hσC, one_smul]

theorem complexMatrixEuclideanLin_gramEigenvectorBasis_eq_zero_of_singularValue_eq_zero
    {m n : ℕ} (A : CMatrix m n) (i : Fin n)
    (hσ : complexMatrixSingularValue A i = 0) :
    complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i) = 0 := by
  apply norm_eq_zero.mp
  rw [← complexMatrixSingularValue_eq_norm_euclideanLin_gramEigenvectorBasis A i]
  exact hσ

theorem complexMatrixLeftSingularVector_eq_zero_of_singularValue_eq_zero
    {m n : ℕ} (A : CMatrix m n) (i : Fin n)
    (hσ : complexMatrixSingularValue A i = 0) :
    complexMatrixLeftSingularVector A i = 0 := by
  simp [complexMatrixLeftSingularVector, hσ]

theorem complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all
    {m n : ℕ} (A : CMatrix m n) (i : Fin n) :
    complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i) =
      (complexMatrixSingularValue A i : ℂ) •
        complexMatrixLeftSingularVector A i := by
  by_cases hσ : complexMatrixSingularValue A i = 0
  · rw [complexMatrixEuclideanLin_gramEigenvectorBasis_eq_zero_of_singularValue_eq_zero A i hσ,
      hσ]
    simp
  · exact complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left
      A i hσ

theorem complexMatrixLeftSingularVector_norm_eq_ite {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    ‖complexMatrixLeftSingularVector A i‖ =
      if complexMatrixSingularValue A i = 0 then 0 else 1 := by
  by_cases hσ : complexMatrixSingularValue A i = 0
  · rw [complexMatrixLeftSingularVector_eq_zero_of_singularValue_eq_zero A i hσ,
      norm_zero]
    simp [hσ]
  · rw [complexMatrixLeftSingularVector_norm_of_ne_zero A i hσ]
    simp [hσ]

theorem complexMatrixLeftSingularVector_inner_eq_zero_of_ne {m n : ℕ}
    (A : CMatrix m n) {i j : Fin n} (hij : i ≠ j) :
    inner ℂ (complexMatrixLeftSingularVector A i)
      (complexMatrixLeftSingularVector A j) = 0 := by
  rw [complexMatrixLeftSingularVector, complexMatrixLeftSingularVector,
    inner_smul_left, inner_smul_right,
    complexMatrixEuclideanLin_gramEigenvectorBasis_inner_eq_zero_of_ne A hij]
  simp

theorem complexMatrixLeftSingularVector_injective_on_nonzero {m n : ℕ}
    (A : CMatrix m n) {i j : Fin n}
    (_hi : complexMatrixSingularValue A i ≠ 0)
    (hj : complexMatrixSingularValue A j ≠ 0)
    (hvec :
      complexMatrixLeftSingularVector A i =
        complexMatrixLeftSingularVector A j) :
    i = j := by
  by_contra hij
  have horth := complexMatrixLeftSingularVector_inner_eq_zero_of_ne A hij
  have hself :
      inner ℂ (complexMatrixLeftSingularVector A j)
        (complexMatrixLeftSingularVector A j) = 1 := by
    have hnorm := complexMatrixLeftSingularVector_norm_of_ne_zero A j hj
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  rw [hvec, hself] at horth
  norm_num at horth

theorem complexMatrixLeftSingularVector_mem_range_euclideanLin {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    complexMatrixLeftSingularVector A i ∈
      LinearMap.range (complexMatrixEuclideanLin A) := by
  refine ⟨((complexMatrixSingularValue A i : ℂ)⁻¹) •
    complexMatrixGramEigenvectorBasis A i, ?_⟩
  simp [complexMatrixLeftSingularVector]

/-- The nonzero local left singular vectors are an orthonormal family. This is
    the range-basis ingredient needed before rectangular SVD packaging. -/
theorem complexMatrixLeftSingularVector_orthonormal_nonzero {m n : ℕ}
    (A : CMatrix m n) :
    Orthonormal ℂ
      (fun i : {i : Fin n // complexMatrixSingularValue A i ≠ 0} =>
        complexMatrixLeftSingularVector A i.1) := by
  constructor
  · intro i
    exact complexMatrixLeftSingularVector_norm_of_ne_zero A i.1 i.2
  · intro i j hij
    apply complexMatrixLeftSingularVector_inner_eq_zero_of_ne A
    intro h
    exact hij (Subtype.ext h)

/-- Nonzero local left singular vectors, as vectors in the range of `A`. -/
noncomputable def complexMatrixLeftSingularVectorInRange {m n : ℕ}
    (A : CMatrix m n)
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) :
    LinearMap.range (complexMatrixEuclideanLin A) :=
  ⟨complexMatrixLeftSingularVector A i.1,
    complexMatrixLeftSingularVector_mem_range_euclideanLin A i.1⟩

theorem complexMatrixLeftSingularVectorInRange_orthonormal {m n : ℕ}
    (A : CMatrix m n) :
    Orthonormal ℂ (complexMatrixLeftSingularVectorInRange A) := by
  exact
    (complexMatrixLeftSingularVector_orthonormal_nonzero A).codRestrict
      (LinearMap.range (complexMatrixEuclideanLin A))
      (fun i => complexMatrixLeftSingularVector_mem_range_euclideanLin A i.1)

theorem complexMatrixLeftSingularVector_nonzero_card {m n : ℕ}
    (A : CMatrix m n) :
    Fintype.card {i : Fin n // complexMatrixSingularValue A i ≠ 0} =
      complexMatrixRank A :=
  (complexMatrixRank_eq_card_nonzero_singularValue A).symm

theorem complexMatrixLeftSingularVector_nonzero_card_eq_finrank_range
    {m n : ℕ} (A : CMatrix m n) :
    Fintype.card {i : Fin n // complexMatrixSingularValue A i ≠ 0} =
      Module.finrank ℂ (LinearMap.range (complexMatrixEuclideanLin A)) := by
  rw [complexMatrixLeftSingularVector_nonzero_card,
    complexMatrixRank_eq_finrank_range_euclideanLin]

/-- In positive-rank cases, the nonzero local left singular vectors form an
    orthonormal basis of the range of `A`. The zero-rank case is intentionally
    left to the general finite-dimensional empty-basis API. -/
noncomputable def complexMatrixLeftSingularVectorInRangeBasisOfRankPos
    {m n : ℕ} (A : CMatrix m n) (hrank : 0 < complexMatrixRank A) :
    Module.Basis {i : Fin n // complexMatrixSingularValue A i ≠ 0} ℂ
      (LinearMap.range (complexMatrixEuclideanLin A)) := by
  have hcard_pos :
      0 < Fintype.card {i : Fin n // complexMatrixSingularValue A i ≠ 0} := by
    simpa [complexMatrixRank_eq_card_nonzero_singularValue A] using hrank
  haveI : Nonempty {i : Fin n // complexMatrixSingularValue A i ≠ 0} :=
    Fintype.card_pos_iff.mp hcard_pos
  exact basisOfOrthonormalOfCardEqFinrank
    (complexMatrixLeftSingularVectorInRange_orthonormal A)
    (complexMatrixLeftSingularVector_nonzero_card_eq_finrank_range A)

theorem complexMatrixLeftSingularVectorInRangeBasisOfRankPos_apply
    {m n : ℕ} (A : CMatrix m n) (hrank : 0 < complexMatrixRank A)
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) :
    complexMatrixLeftSingularVectorInRangeBasisOfRankPos A hrank i =
      complexMatrixLeftSingularVectorInRange A i := by
  simp [complexMatrixLeftSingularVectorInRangeBasisOfRankPos,
    coe_basisOfOrthonormalOfCardEqFinrank]

/-- The set of nonzero local left singular vectors in the target space. -/
noncomputable def complexMatrixLeftSingularVectorNonzeroSet {m n : ℕ}
    (A : CMatrix m n) : Set (EuclideanSpace ℂ (Fin m)) :=
  Set.range
    (fun i : {i : Fin n // complexMatrixSingularValue A i ≠ 0} =>
      complexMatrixLeftSingularVector A i.1)

theorem complexMatrixLeftSingularVectorNonzeroSet_subset_range {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixLeftSingularVectorNonzeroSet A ⊆
      LinearMap.range (complexMatrixEuclideanLin A) := by
  rintro x ⟨i, rfl⟩
  exact complexMatrixLeftSingularVector_mem_range_euclideanLin A i.1

theorem complexMatrixLeftSingularVectorNonzeroSet_orthonormal {m n : ℕ}
    (A : CMatrix m n) :
    Orthonormal ℂ
      ((↑) : complexMatrixLeftSingularVectorNonzeroSet A →
        EuclideanSpace ℂ (Fin m)) := by
  simpa [complexMatrixLeftSingularVectorNonzeroSet] using
    (complexMatrixLeftSingularVector_orthonormal_nonzero A).toSubtypeRange

theorem exists_complexMatrixLeftSingularVector_orthonormalBasis_extension
    {m n : ℕ} (A : CMatrix m n) :
    ∃ (u : Finset (EuclideanSpace ℂ (Fin m)))
      (b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))),
        complexMatrixLeftSingularVectorNonzeroSet A ⊆ u ∧
          ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)) :=
  (complexMatrixLeftSingularVectorNonzeroSet_orthonormal A).exists_orthonormalBasis_extension

/-- Singular-vector expansion of the Euclidean linear map. This is a
    coordinate-free diagonal action statement toward Higham's Chapter 6
    rectangular SVD: in the sorted right Gram eigenvector basis, `A x` is the
    sum of the source coordinates multiplied by the corresponding local
    singular values and left singular vector candidates. -/
theorem complexMatrixEuclideanLin_singular_expansion {m n : ℕ}
    (A : CMatrix m n) (x : EuclideanSpace ℂ (Fin n)) :
    complexMatrixEuclideanLin A x =
      ∑ i : Fin n,
        ((complexMatrixGramEigenvectorBasis A).repr x i) •
          ((complexMatrixSingularValue A i : ℂ) •
            complexMatrixLeftSingularVector A i) := by
  conv_lhs =>
    rw [← (complexMatrixGramEigenvectorBasis A).sum_repr x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]

/-- In any target orthonormal-basis extension containing the nonzero local left
    singular vectors, the coordinate of `A v_i` along the matching left
    singular vector is the local singular value. -/
theorem complexMatrixSVD_targetBasisCoord_eq_singularValue {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)))
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) :
    b.repr
        (complexMatrixEuclideanLin A
          (complexMatrixGramEigenvectorBasis A i.1))
        ⟨complexMatrixLeftSingularVector A i.1,
          hsub ⟨i, rfl⟩⟩ =
      (complexMatrixSingularValue A i.1 : ℂ) := by
  rw [OrthonormalBasis.repr_apply_apply]
  rw [complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
  rw [inner_smul_right]
  have hbcoord :
      b ⟨complexMatrixLeftSingularVector A i.1, hsub ⟨i, rfl⟩⟩ =
        complexMatrixLeftSingularVector A i.1 := by
    simpa using congr_fun hb
      ⟨complexMatrixLeftSingularVector A i.1, hsub ⟨i, rfl⟩⟩
  rw [hbcoord]
  have hinner :
      inner ℂ (complexMatrixLeftSingularVector A i.1)
        (complexMatrixLeftSingularVector A i.1) = 1 := by
    have hnorm := complexMatrixLeftSingularVector_norm_of_ne_zero A i.1 i.2
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  rw [hinner, mul_one]

/-- In any target orthonormal-basis extension containing the nonzero local left
    singular vectors, every coordinate of `A v_i` away from the matching left
    singular vector is zero. Together with
    `complexMatrixSVD_targetBasisCoord_eq_singularValue`, this gives the
    diagonal-coordinate form of the local rectangular SVD packaging layer. -/
theorem complexMatrixSVD_targetBasisCoord_eq_zero_of_ne {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)))
    (i : Fin n) (k : u)
    (hk : (k : EuclideanSpace ℂ (Fin m)) ≠
      complexMatrixLeftSingularVector A i) :
    b.repr
        (complexMatrixEuclideanLin A
          (complexMatrixGramEigenvectorBasis A i))
        k = 0 := by
  by_cases hσ : complexMatrixSingularValue A i = 0
  · rw [complexMatrixEuclideanLin_gramEigenvectorBasis_eq_zero_of_singularValue_eq_zero A i hσ]
    simp
  · rw [OrthonormalBasis.repr_apply_apply]
    rw [complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
    rw [inner_smul_right]
    have hmem :
        complexMatrixLeftSingularVector A i ∈ u := by
      exact hsub ⟨⟨i, hσ⟩, rfl⟩
    let ui : u := ⟨complexMatrixLeftSingularVector A i, hmem⟩
    have hne : k ≠ ui := by
      intro h
      apply hk
      exact congr_arg Subtype.val h
    have hb_k : b k = (k : EuclideanSpace ℂ (Fin m)) := by
      simpa using congr_fun hb k
    have hb_ui : b ui = complexMatrixLeftSingularVector A i := by
      simpa [ui]
        using congr_fun hb ui
    have hinner : inner ℂ (b k) (b ui) = 0 := b.inner_eq_zero hne
    rw [hb_k, hb_ui] at hinner
    rw [hb_k, hinner, mul_zero]

/-- Coordinate matrix of the Euclidean linear map in the sorted right Gram
    eigenvector basis and a supplied target orthonormal-basis extension. Its
    columns are the singular columns `sigma_i • u_i`; the following theorems
    prove that this matrix represents `A` and has the expected diagonal column
    entries. -/
noncomputable def complexMatrixSVDCoordinateMatrix {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    (b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))) :
    u → Fin n → ℂ :=
  fun k i =>
    b.repr
      ((complexMatrixSingularValue A i : ℂ) •
        complexMatrixLeftSingularVector A i) k

/-- Matrix-coordinate representation of `A x` in the SVD source basis and any
    target orthonormal-basis extension. This is the source-facing rectangular
    SVD packaging layer before choosing concrete unitary matrices. -/
theorem complexMatrixSVDCoordinateMatrix_repr_apply {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    (b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin n)) (k : u) :
    b.repr (complexMatrixEuclideanLin A x) k =
      ∑ i : Fin n,
        complexMatrixSVDCoordinateMatrix A b k i *
          (complexMatrixGramEigenvectorBasis A).repr x i := by
  conv_lhs =>
    rw [complexMatrixEuclideanLin_singular_expansion A x]
  rw [map_sum]
  simp [complexMatrixSVDCoordinateMatrix, map_smul, mul_comm]

/-- Matrix-vector form of the coordinate SVD representation: in the sorted
    right Gram eigenvector basis and target basis `b`, the coordinate vector of
    `A x` is the coordinate SVD matrix times the coordinate vector of `x`. -/
theorem complexMatrixSVDCoordinateMatrix_mulVec_repr {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    (b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin n)) :
    Matrix.mulVec (complexMatrixSVDCoordinateMatrix A b)
        ((complexMatrixGramEigenvectorBasis A).repr x) =
      b.repr (complexMatrixEuclideanLin A x) := by
  ext k
  simpa [Matrix.mulVec] using
    (complexMatrixSVDCoordinateMatrix_repr_apply A b x k).symm

/-- The coordinate matrix has diagonal entry `sigma_i` in the row corresponding
    to the matching nonzero left singular vector. -/
theorem complexMatrixSVDCoordinateMatrix_apply_leftSingular {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)))
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) :
    complexMatrixSVDCoordinateMatrix A b
        ⟨complexMatrixLeftSingularVector A i.1, hsub ⟨i, rfl⟩⟩ i.1 =
      (complexMatrixSingularValue A i.1 : ℂ) := by
  rw [complexMatrixSVDCoordinateMatrix,
    ← complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
  exact complexMatrixSVD_targetBasisCoord_eq_singularValue A hsub hb i

/-- The coordinate matrix has zero entries away from the row corresponding to
    the matching local left singular vector. -/
theorem complexMatrixSVDCoordinateMatrix_apply_zero_of_ne {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)))
    (i : Fin n) (k : u)
    (hk : (k : EuclideanSpace ℂ (Fin m)) ≠
      complexMatrixLeftSingularVector A i) :
    complexMatrixSVDCoordinateMatrix A b k i = 0 := by
  rw [complexMatrixSVDCoordinateMatrix,
    ← complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
  exact complexMatrixSVD_targetBasisCoord_eq_zero_of_ne A hsub hb i k hk

/-- A zero singular value gives a zero column in the coordinate SVD matrix. -/
theorem complexMatrixSVDCoordinateMatrix_apply_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    (b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m)))
    (i : Fin n) (k : u)
    (hσ : complexMatrixSingularValue A i = 0) :
    complexMatrixSVDCoordinateMatrix A b k i = 0 := by
  simp [complexMatrixSVDCoordinateMatrix, hσ]

/-- Explicit diagonal-or-zero entries of the coordinate SVD matrix. -/
theorem complexMatrixSVDCoordinateMatrix_apply_eq_ite {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)))
    (k : u) (i : Fin n) :
    complexMatrixSVDCoordinateMatrix A b k i =
      if complexMatrixSingularValue A i = 0 then 0
      else if (k : EuclideanSpace ℂ (Fin m)) =
          complexMatrixLeftSingularVector A i
        then (complexMatrixSingularValue A i : ℂ)
        else 0 := by
  by_cases hσ : complexMatrixSingularValue A i = 0
  · rw [if_pos hσ]
    exact complexMatrixSVDCoordinateMatrix_apply_eq_zero_of_singularValue_eq_zero
      A b i k hσ
  · rw [if_neg hσ]
    by_cases hk : (k : EuclideanSpace ℂ (Fin m)) =
        complexMatrixLeftSingularVector A i
    · rw [if_pos hk]
      have hk_sub :
          k = ⟨complexMatrixLeftSingularVector A i,
              hsub ⟨⟨i, hσ⟩, rfl⟩⟩ := Subtype.ext hk
      rw [hk_sub]
      exact complexMatrixSVDCoordinateMatrix_apply_leftSingular
        A hsub hb ⟨i, hσ⟩
    · rw [if_neg hk]
      exact complexMatrixSVDCoordinateMatrix_apply_zero_of_ne
        A hsub hb i k hk

/-- Coordinate representation of `A x` with the coordinate SVD matrix expanded
    into its explicit diagonal-or-zero entries. -/
theorem complexMatrixSVDCoordinateMatrix_repr_apply_eq_sum_ite {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin n)) (k : u) :
    b.repr (complexMatrixEuclideanLin A x) k =
      ∑ i : Fin n,
        (if complexMatrixSingularValue A i = 0 then 0
          else if (k : EuclideanSpace ℂ (Fin m)) =
              complexMatrixLeftSingularVector A i
            then (complexMatrixSingularValue A i : ℂ)
            else 0) *
          (complexMatrixGramEigenvectorBasis A).repr x i := by
  rw [complexMatrixSVDCoordinateMatrix_repr_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [complexMatrixSVDCoordinateMatrix_apply_eq_ite A hsub hb k i]

/-- Explicit diagonal-or-zero coordinate matrix for the local rectangular SVD,
    before choosing concrete standard-coordinate unitary matrices. -/
noncomputable def complexMatrixSVDDiagonalCoordinateMatrix {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))} :
    Matrix u (Fin n) ℂ :=
  fun k i =>
    if complexMatrixSingularValue A i = 0 then 0
    else if (k : EuclideanSpace ℂ (Fin m)) =
        complexMatrixLeftSingularVector A i
      then (complexMatrixSingularValue A i : ℂ)
      else 0

/-- The coordinate SVD matrix is the explicit diagonal-or-zero coordinate
    matrix when the target orthonormal basis extends the nonzero left singular
    vectors. -/
theorem complexMatrixSVDCoordinateMatrix_eq_diagonalCoordinateMatrix {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m))) :
    complexMatrixSVDCoordinateMatrix A b =
      complexMatrixSVDDiagonalCoordinateMatrix A := by
  ext k i
  exact complexMatrixSVDCoordinateMatrix_apply_eq_ite A hsub hb k i

/-- Matrix-vector coordinate form of the explicit diagonal local SVD. -/
theorem complexMatrixSVDDiagonalCoordinateMatrix_mulVec_repr {m n : ℕ}
    (A : CMatrix m n)
    {u : Finset (EuclideanSpace ℂ (Fin m))}
    {b : OrthonormalBasis u ℂ (EuclideanSpace ℂ (Fin m))}
    (hsub : complexMatrixLeftSingularVectorNonzeroSet A ⊆ u)
    (hb : ⇑b = ((↑) : u → EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin n)) :
    Matrix.mulVec (complexMatrixSVDDiagonalCoordinateMatrix (u := u) A)
        ((complexMatrixGramEigenvectorBasis A).repr x) =
      b.repr (complexMatrixEuclideanLin A x) := by
  rw [← complexMatrixSVDCoordinateMatrix_eq_diagonalCoordinateMatrix A hsub hb]
  exact complexMatrixSVDCoordinateMatrix_mulVec_repr A b x

/-- Finite-index target-coordinate matrix for the local rectangular SVD.
    Its rows are indexed by an arbitrary target orthonormal basis indexed by
    `Fin m`, and its columns are indexed by the sorted Gram eigenvector basis. -/
noncomputable def complexMatrixSVDTargetCoordinateMatrix {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun k i =>
    b.repr
      ((complexMatrixSingularValue A i : ℂ) •
        complexMatrixLeftSingularVector A i) k

/-- Finite-index coordinate representation of `A x` in a target
    orthonormal basis and the sorted right Gram eigenvector basis. -/
theorem complexMatrixSVDTargetCoordinateMatrix_repr_apply {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin n)) (k : Fin m) :
    b.repr (complexMatrixEuclideanLin A x) k =
      ∑ i : Fin n,
        complexMatrixSVDTargetCoordinateMatrix A b k i *
          (complexMatrixGramEigenvectorBasis A).repr x i := by
  conv_lhs =>
    rw [complexMatrixEuclideanLin_singular_expansion A x]
  rw [map_sum]
  simp [complexMatrixSVDTargetCoordinateMatrix, map_smul, mul_comm]

/-- Matrix-vector form of the finite-index target-coordinate SVD
    representation. -/
theorem complexMatrixSVDTargetCoordinateMatrix_mulVec_repr {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin n)) :
    Matrix.mulVec (complexMatrixSVDTargetCoordinateMatrix A b)
        ((complexMatrixGramEigenvectorBasis A).repr x) =
      b.repr (complexMatrixEuclideanLin A x) := by
  ext k
  simpa [Matrix.mulVec] using
    (complexMatrixSVDTargetCoordinateMatrix_repr_apply A b x k).symm

/-- Explicit finite-index diagonal-or-zero matrix for a target basis that
    contains every nonzero local left singular vector. -/
noncomputable def complexMatrixSVDFinDiagonalCoordinateMatrix {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun k i =>
    if complexMatrixSingularValue A i = 0 then 0
    else if b k = complexMatrixLeftSingularVector A i
      then (complexMatrixSingularValue A i : ℂ)
      else 0

/-- The finite-index SVD diagonal matrix has exactly the displayed
    diagonal-or-zero entries. This is the source-notation entry formula for
    the `Σ` matrix used in the local rectangular SVD. -/
theorem complexMatrixSVDFinDiagonalCoordinateMatrix_apply {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (k : Fin m) (i : Fin n) :
    complexMatrixSVDFinDiagonalCoordinateMatrix A b k i =
      if complexMatrixSingularValue A i = 0 then 0
      else if b k = complexMatrixLeftSingularVector A i
        then (complexMatrixSingularValue A i : ℂ)
        else 0 := rfl

/-- If the finite-index target basis contains all nonzero local left singular
    vectors, the target-coordinate SVD matrix has explicit diagonal-or-zero
    entries. -/
theorem complexMatrixSVDTargetCoordinateMatrix_apply_eq_ite {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i)
    (k : Fin m) (i : Fin n) :
    complexMatrixSVDTargetCoordinateMatrix A b k i =
      if complexMatrixSingularValue A i = 0 then 0
      else if b k = complexMatrixLeftSingularVector A i
        then (complexMatrixSingularValue A i : ℂ)
        else 0 := by
  by_cases hσ : complexMatrixSingularValue A i = 0
  · rw [if_pos hσ]
    simp [complexMatrixSVDTargetCoordinateMatrix, hσ]
  · rw [if_neg hσ]
    by_cases hk : b k = complexMatrixLeftSingularVector A i
    · rw [if_pos hk]
      rw [complexMatrixSVDTargetCoordinateMatrix,
        ← complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
      rw [OrthonormalBasis.repr_apply_apply]
      rw [complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
      rw [inner_smul_right, hk]
      have hinner :
          inner ℂ (complexMatrixLeftSingularVector A i)
            (complexMatrixLeftSingularVector A i) = 1 := by
        have hnorm := complexMatrixLeftSingularVector_norm_of_ne_zero A i hσ
        rw [inner_self_eq_norm_sq_to_K, hnorm]
        simp
      rw [hinner, mul_one]
    · rw [if_neg hk]
      obtain ⟨j, hj⟩ := hcontains i hσ
      have hkj : k ≠ j := by
        intro h
        exact hk (by rw [h, hj])
      rw [complexMatrixSVDTargetCoordinateMatrix,
        ← complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
      rw [OrthonormalBasis.repr_apply_apply]
      rw [complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all]
      rw [inner_smul_right]
      have hinner : inner ℂ (b k) (b j) = 0 := b.inner_eq_zero hkj
      rw [hj] at hinner
      rw [hinner, mul_zero]

/-- Finite-index coordinate SVD matrix equals the explicit diagonal-or-zero
    matrix when the target basis contains all nonzero local left singular
    vectors. -/
theorem complexMatrixSVDTargetCoordinateMatrix_eq_finDiagonalCoordinateMatrix
    {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) :
    complexMatrixSVDTargetCoordinateMatrix A b =
      complexMatrixSVDFinDiagonalCoordinateMatrix A b := by
  ext k i
  exact complexMatrixSVDTargetCoordinateMatrix_apply_eq_ite A b hcontains k i

/-- Matrix-vector coordinate form for the explicit finite-index diagonal SVD
    matrix. -/
theorem complexMatrixSVDFinDiagonalCoordinateMatrix_mulVec_repr {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i)
    (x : EuclideanSpace ℂ (Fin n)) :
    Matrix.mulVec (complexMatrixSVDFinDiagonalCoordinateMatrix A b)
        ((complexMatrixGramEigenvectorBasis A).repr x) =
      b.repr (complexMatrixEuclideanLin A x) := by
  rw [← complexMatrixSVDTargetCoordinateMatrix_eq_finDiagonalCoordinateMatrix A b hcontains]
  exact complexMatrixSVDTargetCoordinateMatrix_mulVec_repr A b x

/-- A finite-index target orthonormal basis containing all nonzero local left
    singular vectors exists. -/
theorem exists_complexMatrixLeftSingularVector_fin_orthonormalBasis_extension
    {m n : ℕ} (A : CMatrix m n) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i := by
  obtain ⟨u, b, hsub, hb⟩ :=
    exists_complexMatrixLeftSingularVector_orthonormalBasis_extension A
  have hcard : Fintype.card u = Fintype.card (Fin m) := by
    rw [← Module.finrank_eq_card_basis b.toBasis]
    simp
  let e : u ≃ Fin m := Fintype.equivOfCardEq hcard
  refine ⟨b.reindex e, ?_⟩
  intro i hσ
  let ku : u :=
    ⟨complexMatrixLeftSingularVector A i, hsub ⟨⟨i, hσ⟩, rfl⟩⟩
  refine ⟨e ku, ?_⟩
  rw [OrthonormalBasis.reindex_apply]
  have hbu : b ku = complexMatrixLeftSingularVector A i := by
    simpa [ku] using congrFun hb ku
  simpa [ku] using hbu

/-- The target-basis row occupied by a nonzero local left singular vector. -/
noncomputable def complexMatrixLeftSingularVectorBasisIndex {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i)
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) : Fin m :=
  Classical.choose (hcontains i.1 i.2)

theorem complexMatrixLeftSingularVectorBasisIndex_apply {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i)
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) :
    b (complexMatrixLeftSingularVectorBasisIndex A b hcontains i) =
      complexMatrixLeftSingularVector A i.1 :=
  Classical.choose_spec (hcontains i.1 i.2)

theorem complexMatrixLeftSingularVectorBasisIndex_injective {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) :
    Function.Injective
      (complexMatrixLeftSingularVectorBasisIndex A b hcontains) := by
  intro i j hij
  apply Subtype.ext
  exact complexMatrixLeftSingularVector_injective_on_nonzero A i.2 j.2 <| by
    calc
      complexMatrixLeftSingularVector A i.1 =
          b (complexMatrixLeftSingularVectorBasisIndex A b hcontains i) := by
            exact (complexMatrixLeftSingularVectorBasisIndex_apply A b hcontains i).symm
      _ = b (complexMatrixLeftSingularVectorBasisIndex A b hcontains j) := by
            rw [hij]
      _ = complexMatrixLeftSingularVector A j.1 := by
            exact complexMatrixLeftSingularVectorBasisIndex_apply A b hcontains j

/-- The chosen target-basis rows for nonzero local left singular vectors,
    packaged as an embedding. -/
noncomputable def complexMatrixLeftSingularVectorBasisEmbedding {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) :
    {i : Fin n // complexMatrixSingularValue A i ≠ 0} ↪ Fin m where
  toFun := complexMatrixLeftSingularVectorBasisIndex A b hcontains
  inj' := complexMatrixLeftSingularVectorBasisIndex_injective A b hcontains

@[simp]
theorem complexMatrixLeftSingularVectorBasisEmbedding_apply {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i)
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) :
    complexMatrixLeftSingularVectorBasisEmbedding A b hcontains i =
      complexMatrixLeftSingularVectorBasisIndex A b hcontains i := rfl

section

attribute [local instance]
  NumStability.complexMatrixVecMulCoordinateMatrix.«_proof_3»

/-- In the square case, extend the injective placement of nonzero singular
    columns in the target basis to a full permutation of the finite index set. -/
noncomputable def complexMatrixLeftSingularVectorBasisPerm {n : ℕ}
    (A : CMatrix n n)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin n, b k = complexMatrixLeftSingularVector A i) :
    Equiv.Perm (Fin n) :=
  (complexMatrixLeftSingularVectorBasisEmbedding A b hcontains).toEquivRange.extendSubtype

end

theorem complexMatrixLeftSingularVectorBasisPerm_apply_nonzero {n : ℕ}
    (A : CMatrix n n)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin n, b k = complexMatrixLeftSingularVector A i)
    (i : {i : Fin n // complexMatrixSingularValue A i ≠ 0}) :
    complexMatrixLeftSingularVectorBasisPerm A b hcontains i.1 =
      complexMatrixLeftSingularVectorBasisIndex A b hcontains i := by
  classical
  simpa [complexMatrixLeftSingularVectorBasisPerm,
    Function.Embedding.toEquivRange,
    complexMatrixLeftSingularVectorBasisEmbedding] using
    (Equiv.extendSubtype_apply_of_mem
      ((complexMatrixLeftSingularVectorBasisEmbedding A b hcontains).toEquivRange)
      i.1 i.2)

/-- Left unitary change-of-basis matrix from target SVD coordinates to
    standard coordinates. -/
noncomputable def complexMatrixSVDLeftUnitary {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) :
    Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin m) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp]
theorem complexMatrixSVDLeftUnitary_apply {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (i j : Fin m) :
    (complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ) i j =
      b j i := rfl

/-- The left unitary sends target-basis coordinates back to the target vector. -/
theorem complexMatrixSVDLeftUnitary_mulVec_repr {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (y : EuclideanSpace ℂ (Fin m)) :
    Matrix.mulVec (complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ)
        (b.repr y) = y := by
  ext i
  have h := congrArg (fun z : EuclideanSpace ℂ (Fin m) => z i) (b.sum_repr y)
  simpa [Matrix.mulVec, complexMatrixSVDLeftUnitary, Pi.smul_apply,
    smul_eq_mul, mul_comm] using h

/-- Right unitary change-of-basis matrix whose columns are the sorted right
    Gram eigenvectors. -/
noncomputable def complexMatrixSVDRightUnitary {m n : ℕ}
    (A : CMatrix m n) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix
      (complexMatrixGramEigenvectorBasis A).toBasis,
    (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary
      (complexMatrixGramEigenvectorBasis A)⟩

@[simp]
theorem complexMatrixSVDRightUnitary_apply {m n : ℕ}
    (A : CMatrix m n) (i j : Fin n) :
    (complexMatrixSVDRightUnitary A : Matrix (Fin n) (Fin n) ℂ) i j =
      complexMatrixGramEigenvectorBasis A j i := rfl

/-- The right unitary sends right singular coordinates back to the source
    vector. -/
theorem complexMatrixSVDRightUnitary_mulVec_repr {m n : ℕ}
    (A : CMatrix m n) (x : EuclideanSpace ℂ (Fin n)) :
    Matrix.mulVec (complexMatrixSVDRightUnitary A : Matrix (Fin n) (Fin n) ℂ)
        ((complexMatrixGramEigenvectorBasis A).repr x) = x := by
  ext i
  have h := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z i)
    ((complexMatrixGramEigenvectorBasis A).sum_repr x)
  simpa [Matrix.mulVec, complexMatrixSVDRightUnitary, Pi.smul_apply,
    smul_eq_mul, mul_comm] using h

/-- The conjugate transpose of the right unitary extracts coordinates in the
    sorted right Gram eigenvector basis. -/
theorem complexMatrixSVDRightUnitary_conjTranspose_mulVec {m n : ℕ}
    (A : CMatrix m n) (x : EuclideanSpace ℂ (Fin n)) :
    Matrix.mulVec
        (star (complexMatrixSVDRightUnitary A : Matrix (Fin n) (Fin n) ℂ)) x =
      (complexMatrixGramEigenvectorBasis A).repr x := by
  rw [← complexMatrixSVDRightUnitary_mulVec_repr A x]
  rw [Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]

/-- Rectangular SVD in unitary-coordinate `mulVec` form:
    `U * D * V^*` acts as the original matrix, where `D` is the finite-index
    diagonal-or-zero coordinate SVD matrix. -/
theorem complexMatrixSVDUnitary_diagonal_mulVec {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i)
    (x : EuclideanSpace ℂ (Fin n)) :
    Matrix.mulVec
        ((complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ) *
          complexMatrixSVDFinDiagonalCoordinateMatrix A b *
            star (complexMatrixSVDRightUnitary A : Matrix (Fin n) (Fin n) ℂ))
        x =
      complexMatrixEuclideanLin A x := by
  rw [← Matrix.mulVec_mulVec x
    ((complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ) *
      complexMatrixSVDFinDiagonalCoordinateMatrix A b)
    (star (complexMatrixSVDRightUnitary A : Matrix (Fin n) (Fin n) ℂ))]
  rw [← Matrix.mulVec_mulVec
    (Matrix.mulVec
      (star (complexMatrixSVDRightUnitary A : Matrix (Fin n) (Fin n) ℂ)) x)
    (complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ)
    (complexMatrixSVDFinDiagonalCoordinateMatrix A b)]
  rw [complexMatrixSVDRightUnitary_conjTranspose_mulVec]
  rw [complexMatrixSVDFinDiagonalCoordinateMatrix_mulVec_repr A b hcontains]
  exact complexMatrixSVDLeftUnitary_mulVec_repr b (complexMatrixEuclideanLin A x)

/-- Existence form of the rectangular SVD unitary-coordinate action theorem. -/
theorem exists_complexMatrixSVDUnitary_diagonal_mulVec {m n : ℕ}
    (A : CMatrix m n) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      (∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) ∧
        ∀ x : EuclideanSpace ℂ (Fin n),
          Matrix.mulVec
              ((complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ) *
                complexMatrixSVDFinDiagonalCoordinateMatrix A b *
                  star (complexMatrixSVDRightUnitary A :
                    Matrix (Fin n) (Fin n) ℂ))
              x =
            complexMatrixEuclideanLin A x := by
  obtain ⟨b, hcontains⟩ :=
    exists_complexMatrixLeftSingularVector_fin_orthonormalBasis_extension A
  exact ⟨b, hcontains, fun x =>
    complexMatrixSVDUnitary_diagonal_mulVec A b hcontains x⟩

/-- Rectangular SVD in matrix equality form for the chosen local unitary
    coordinates. -/
theorem complexMatrixSVDUnitary_diagonal_eq {m n : ℕ}
    (A : CMatrix m n)
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hcontains :
      ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) :
    ((complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ) *
      complexMatrixSVDFinDiagonalCoordinateMatrix A b *
        star (complexMatrixSVDRightUnitary A : Matrix (Fin n) (Fin n) ℂ)) =
      (A : Matrix (Fin m) (Fin n) ℂ) := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have h := complexMatrixSVDUnitary_diagonal_mulVec A b hcontains
    (EuclideanSpace.single j (1 : ℂ))
  rw [complexMatrixEuclideanLin, Matrix.ofLp_toLpLin] at h
  rw [EuclideanSpace.ofLp_single] at h
  exact h

/-- Existence form of the rectangular SVD unitary-coordinate matrix equality. -/
theorem exists_complexMatrixSVDUnitary_diagonal_eq {m n : ℕ}
    (A : CMatrix m n) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      (∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) ∧
        ((complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ) *
          complexMatrixSVDFinDiagonalCoordinateMatrix A b *
            star (complexMatrixSVDRightUnitary A :
              Matrix (Fin n) (Fin n) ℂ)) =
          (A : Matrix (Fin m) (Fin n) ℂ) := by
  obtain ⟨b, hcontains⟩ :=
    exists_complexMatrixLeftSingularVector_fin_orthonormalBasis_extension A
  exact ⟨b, hcontains,
    complexMatrixSVDUnitary_diagonal_eq A b hcontains⟩

/-- Source-facing rectangular SVD existence package: there is a finite-index
    target orthonormal basis such that `U * Σ * V^* = A`, and the rectangular
    `Σ` matrix has the expected singular-value diagonal entries and zero
    off-diagonal/zero-singular-value entries. -/
theorem exists_complexMatrixSVDUnitary_diagonal_eq_with_entry_formula {m n : ℕ}
    (A : CMatrix m n) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      (∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
        ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) ∧
        ((complexMatrixSVDLeftUnitary b : Matrix (Fin m) (Fin m) ℂ) *
          complexMatrixSVDFinDiagonalCoordinateMatrix A b *
            star (complexMatrixSVDRightUnitary A :
              Matrix (Fin n) (Fin n) ℂ)) =
          (A : Matrix (Fin m) (Fin n) ℂ) ∧
        ∀ k : Fin m, ∀ i : Fin n,
          complexMatrixSVDFinDiagonalCoordinateMatrix A b k i =
            if complexMatrixSingularValue A i = 0 then 0
            else if b k = complexMatrixLeftSingularVector A i
              then (complexMatrixSingularValue A i : ℂ)
              else 0 := by
  obtain ⟨b, hcontains, heq⟩ := exists_complexMatrixSVDUnitary_diagonal_eq A
  exact ⟨b, hcontains, heq, fun k i =>
    complexMatrixSVDFinDiagonalCoordinateMatrix_apply A b k i⟩

/-- Source-facing rectangular SVD predicate with explicit unitary factors.
    `U * Sigma * V^* = A`, `V` is the sorted right-Gram unitary, and
    `Sigma` is the finite-index diagonal-or-zero singular-value matrix for
    some target orthonormal basis containing all nonzero left singular
    vectors. -/
structure IsComplexMatrixSVD {m n : ℕ} (A : CMatrix m n)
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (Sigma : Matrix (Fin m) (Fin n) ℂ)
    (V : Matrix.unitaryGroup (Fin n) ℂ) : Prop where
  mul_eq :
    ((U : Matrix (Fin m) (Fin m) ℂ) * Sigma *
        star (V : Matrix (Fin n) (Fin n) ℂ)) =
      (A : Matrix (Fin m) (Fin n) ℂ)
  right_eq :
    V = complexMatrixSVDRightUnitary A
  exists_left_basis :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      U = complexMatrixSVDLeftUnitary b ∧
        Sigma = complexMatrixSVDFinDiagonalCoordinateMatrix A b ∧
          (∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
            ∃ k : Fin m, b k = complexMatrixLeftSingularVector A i) ∧
          ∀ k : Fin m, ∀ i : Fin n,
            Sigma k i =
              if complexMatrixSingularValue A i = 0 then 0
              else if b k = complexMatrixLeftSingularVector A i
                then (complexMatrixSingularValue A i : ℂ)
                else 0

/-- Existence of source-facing rectangular SVD factors. -/
theorem exists_isComplexMatrixSVD {m n : ℕ} (A : CMatrix m n) :
    ∃ (U : Matrix.unitaryGroup (Fin m) ℂ)
      (Sigma : Matrix (Fin m) (Fin n) ℂ)
      (V : Matrix.unitaryGroup (Fin n) ℂ),
        IsComplexMatrixSVD A U Sigma V := by
  obtain ⟨b, hcontains, heq, hentry⟩ :=
    exists_complexMatrixSVDUnitary_diagonal_eq_with_entry_formula A
  refine ⟨complexMatrixSVDLeftUnitary b,
    complexMatrixSVDFinDiagonalCoordinateMatrix A b,
    complexMatrixSVDRightUnitary A, ?_⟩
  refine ⟨heq, rfl, ?_⟩
  exact ⟨b, rfl, rfl, hcontains, hentry⟩

theorem complexMatrixGramLin_norm_eq_top_eigenvalue {m n : ℕ}
    (hn : 0 < n) (A : CMatrix m n) :
    ‖(complexMatrixGramLin A).toContinuousLinearMap‖ =
      complexMatrixGramEigenvalues A ⟨0, hn⟩ := by
  apply le_antisymm
  · haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := by infer_instance
    let G : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      (complexMatrixGramLin A).toContinuousLinearMap
    let s : ℝ :=
      ⨆ x : { x : EuclideanSpace ℂ (Fin n) // x ≠ 0 },
        RCLike.re
          (inner ℂ
            (complexMatrixGramLin A (x : EuclideanSpace ℂ (Fin n)))
            (x : EuclideanSpace ℂ (Fin n))) /
          ‖(x : EuclideanSpace ℂ (Fin n))‖ ^ 2
    have hs_exists :
        ∃ i : Fin n, complexMatrixGramEigenvalues A i = s := by
      simpa [complexMatrixGramEigenvalues, s] using
        (complexMatrixGramLin_isSymmetric A).exists_eigenvalues_eq
          (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n))
          ((complexMatrixGramLin_isSymmetric A).hasEigenvalue_iSup_of_finiteDimensional)
    obtain ⟨i, hi⟩ := hs_exists
    have hs_le_top : s ≤ complexMatrixGramEigenvalues A ⟨0, hn⟩ := by
      rw [← hi]
      exact complexMatrixGramEigenvalues_antitone A (Fin.zero_le i)
    have hs_bdd :
        BddAbove
          (Set.range fun x : { x : EuclideanSpace ℂ (Fin n) // x ≠ 0 } =>
            RCLike.re
              (inner ℂ
                (complexMatrixGramLin A (x : EuclideanSpace ℂ (Fin n)))
                (x : EuclideanSpace ℂ (Fin n))) /
              ‖(x : EuclideanSpace ℂ (Fin n))‖ ^ 2) := by
      refine ⟨‖G‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      have h := G.rayleighQuotient_le_norm
        (x : EuclideanSpace ℂ (Fin n))
      exact (le_abs_self _).trans h
    have hrq_nonneg (x : EuclideanSpace ℂ (Fin n)) :
        0 ≤ G.rayleighQuotient x := by
      by_cases hx : x = 0
      · simp [ContinuousLinearMap.rayleighQuotient, hx]
      · exact div_nonneg
          (LinearMap.IsPositive.re_inner_nonneg_left
            (complexMatrixGramLin_isPositive A) x)
          (sq_nonneg _)
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient G
      (by simpa [G] using complexMatrixGramLin_isSymmetric A)]
    refine ciSup_le ?_
    intro x
    by_cases hx : x = 0
    · have htop_nonneg : 0 ≤ complexMatrixGramEigenvalues A ⟨0, hn⟩ :=
        complexMatrixGramEigenvalues_nonneg A ⟨0, hn⟩
      simpa [ContinuousLinearMap.rayleighQuotient, hx] using htop_nonneg
    · calc
        |G.rayleighQuotient x| = G.rayleighQuotient x := by
          exact abs_of_nonneg (hrq_nonneg x)
        _ ≤ s := by
          simpa [s, G, ContinuousLinearMap.rayleighQuotient] using
            (le_ciSup hs_bdd ⟨x, hx⟩)
        _ ≤ complexMatrixGramEigenvalues A ⟨0, hn⟩ := hs_le_top
  · haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let i0 : Fin n := ⟨0, hn⟩
    let v : EuclideanSpace ℂ (Fin n) := complexMatrixGramEigenvectorBasis A i0
    have hlam_nonneg : 0 ≤ complexMatrixGramEigenvalues A i0 :=
      complexMatrixGramEigenvalues_nonneg A i0
    calc
      complexMatrixGramEigenvalues A i0 =
          ‖(complexMatrixGramEigenvalues A i0 : ℂ) • v‖ := by
            rw [norm_smul]
            simp [v, Real.norm_eq_abs, abs_of_nonneg hlam_nonneg]
      _ = ‖(complexMatrixGramLin A).toContinuousLinearMap v‖ := by
            rw [← complexMatrixGramLin_apply_eigenvectorBasis A i0]
            rfl
      _ ≤ ‖(complexMatrixGramLin A).toContinuousLinearMap‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ = ‖(complexMatrixGramLin A).toContinuousLinearMap‖ := by
            simp [v]

/-- Source-facing complex matrix operator `2`-norm, explicitly transported
    through Mathlib's Euclidean-space linear-map norm.  This avoids relying on
    scoped matrix norm instances when working with the local `CMatrix`
    abbreviation. -/
noncomputable def complexMatrixOp2 {m n : ℕ} (A : CMatrix m n) : ℝ :=
  ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin m) (n := Fin n) ≪≫ₗ
      LinearMap.toContinuousLinearMap)
      (A : Matrix (Fin m) (Fin n) ℂ)‖

theorem complexMatrixOp2_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixOp2 A :=
  norm_nonneg _

theorem complexMatrixOp2_eq_norm_euclideanLin {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOp2 A =
      ‖(complexMatrixEuclideanLin A).toContinuousLinearMap‖ := by
  simp [complexMatrixOp2, complexMatrixEuclideanLin]

/-- The source-facing complex matrix operator `2`-norm is continuous as a
function of the matrix entries. -/
theorem continuous_complexMatrixOp2 {m n : ℕ} :
    Continuous (fun A : CMatrix m n => complexMatrixOp2 A) := by
  let L : CMatrix m n →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m)) :=
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin m) (n := Fin n) ≪≫ₗ
      LinearMap.toContinuousLinearMap).toLinearMap
  have hL : Continuous fun A : CMatrix m n => L A :=
    LinearMap.continuous_of_finiteDimensional L
  have hnorm : Continuous fun A : CMatrix m n => ‖L A‖ := hL.norm
  simpa [L, complexMatrixOp2_eq_norm_euclideanLin, complexMatrixEuclideanLin] using hnorm

theorem complexMatrixOp2_smul {m n : ℕ} (a : ℂ) (A : CMatrix m n) :
    complexMatrixOp2 ((a • A : Matrix (Fin m) (Fin n) ℂ) : CMatrix m n) =
      ‖a‖ * complexMatrixOp2 A := by
  rw [complexMatrixOp2_eq_norm_euclideanLin,
    complexMatrixOp2_eq_norm_euclideanLin]
  have hlin :
      (complexMatrixEuclideanLin
          (((a • A : Matrix (Fin m) (Fin n) ℂ)) : CMatrix m n)).toContinuousLinearMap =
        a • (complexMatrixEuclideanLin A).toContinuousLinearMap := by
    ext x i
    simp [complexMatrixEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.mul_sum, mul_assoc]
  rw [hlin]
  exact norm_smul a (complexMatrixEuclideanLin A).toContinuousLinearMap

theorem complexMatrix_eq_zero_of_op2_eq_zero {m n : ℕ} {A : CMatrix m n}
    (hA : complexMatrixOp2 A = 0) :
    A = 0 := by
  have hlin_norm :
      ‖(complexMatrixEuclideanLin A).toContinuousLinearMap‖ = 0 := by
    simpa [complexMatrixOp2_eq_norm_euclideanLin A] using hA
  have hlin_zero :
      (complexMatrixEuclideanLin A).toContinuousLinearMap = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff
      ((complexMatrixEuclideanLin A).toContinuousLinearMap)).mp hlin_norm
  ext i j
  have happ :=
    congrArg (fun f : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) =>
      f (EuclideanSpace.basisFun (Fin n) ℂ j)) hlin_zero
  have hbasis_zero :
      complexMatrixEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℂ j) = 0 := by
    simpa using happ
  have hcol_toLp :
      WithLp.toLp (2 : ENNReal) (fun i : Fin m => A i j) = 0 := by
    rw [← complexMatrixEuclideanLin_basisFun A j]
    exact hbasis_zero
  have hzero_col : (fun i : Fin m => A i j) = 0 := by
    have hcol := congrArg WithLp.ofLp hcol_toLp
    simpa using hcol
  exact congrFun hzero_col i

open scoped Matrix.Norms.L2Operator in
theorem complexMatrixOp2_adjoint_eq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOp2 (complexMatrixAdjoint A) = complexMatrixOp2 A := by
  rw [complexMatrixOp2, complexMatrixOp2]
  rw [← Matrix.l2_opNorm_def (complexCMatrixAsMatrix (complexMatrixAdjoint A))]
  rw [← Matrix.l2_opNorm_def (complexCMatrixAsMatrix A)]
  simpa [complexCMatrixAsMatrix, complexMatrixAdjoint, complexMatrixTranspose, complexConjMatrix]
    using (Matrix.l2_opNorm_conjTranspose (A := complexCMatrixAsMatrix A))

/-- The concrete Euclidean linear map of `A†A` is the Gram operator associated
    with `A`. -/
theorem complexMatrixEuclideanLin_adjoint_mul_self {m n : ℕ} (A : CMatrix m n) :
    complexMatrixEuclideanLin (complexMatrixMul (complexMatrixAdjoint A) A) =
      complexMatrixGramLin A := by
  let b := complexEuclideanBasisFin n
  rw [← Matrix.toLin_toMatrix b b
    (complexMatrixEuclideanLin (complexMatrixMul (complexMatrixAdjoint A) A))]
  rw [← Matrix.toLin_toMatrix b b (complexMatrixGramLin A)]
  congr 1
  rw [complexMatrixEuclideanLin_toMatrix, complexMatrixGramLin_toMatrix]
  ext i j
  simp [complexCMatrixAsMatrix, complexMatrixAdjoint, complexMatrixTranspose,
    complexConjMatrix, complexMatrixMul, Matrix.mul_apply]

/-- Operator-2 norm of a concrete Gram matrix: `‖A†A‖₂ = ‖A‖₂²`. -/
theorem complexMatrixOp2_adjoint_mul_self_eq_sq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOp2 (complexMatrixMul (complexMatrixAdjoint A) A) =
      complexMatrixOp2 A ^ 2 := by
  have hlin := complexMatrixEuclideanLin_adjoint_mul_self A
  rw [complexMatrixOp2_eq_norm_euclideanLin]
  rw [hlin]
  rw [complexMatrixGramLin_toContinuousLinearMap]
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  rw [← complexMatrixOp2_eq_norm_euclideanLin A]
  ring

/-- Operator-2 norm of the right Gram product: `‖AA†‖₂ = ‖A‖₂²`. -/
theorem complexMatrixOp2_mul_adjoint_self_eq_sq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOp2 (complexMatrixMul A (complexMatrixAdjoint A)) =
      complexMatrixOp2 A ^ 2 := by
  calc
    complexMatrixOp2 (complexMatrixMul A (complexMatrixAdjoint A)) =
        complexMatrixOp2
          (complexMatrixAdjoint (complexMatrixMul A (complexMatrixAdjoint A))) := by
          rw [complexMatrixOp2_adjoint_eq]
    _ = complexMatrixOp2
          (complexMatrixMul (complexMatrixAdjoint (complexMatrixAdjoint A))
            (complexMatrixAdjoint A)) := by
          rw [complexMatrixAdjoint_mul]
    _ = complexMatrixOp2 (complexMatrixAdjoint A) ^ 2 := by
          rw [complexMatrixOp2_adjoint_mul_self_eq_sq]
    _ = complexMatrixOp2 A ^ 2 := by
          rw [complexMatrixOp2_adjoint_eq]

/-- A square complex matrix with `A†A = n I` has Euclidean operator norm at
    most `sqrt n`. -/
theorem complexMatrixOp2_le_sqrt_of_conjTranspose_mul_self {n : ℕ}
    (A : CMatrix n n)
    (hA : (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
      ((n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) :
    complexMatrixOp2 A ≤ Real.sqrt (n : ℝ) := by
  let L := complexMatrixEuclideanLin A
  have hgram :
      complexMatrixGramLin A =
        (n : ℂ) •
          (LinearMap.id :
            EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :=
    complexMatrixGramLin_eq_smul_id_of_conjTranspose_mul_self A hA
  rw [complexMatrixOp2_eq_norm_euclideanLin]
  refine ContinuousLinearMap.opNorm_le_bound L.toContinuousLinearMap
    (Real.sqrt_nonneg _) ?_
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  have hsq :
      ‖L x‖ ^ 2 = (n : ℝ) * ‖x‖ ^ 2 := by
    calc
      ‖L x‖ ^ 2 = RCLike.re (inner ℂ (L x) (L x)) := by
        rw [inner_self_eq_norm_sq]
      _ = RCLike.re (inner ℂ x ((LinearMap.adjoint L) (L x))) := by
        rw [LinearMap.adjoint_inner_right]
      _ = RCLike.re (inner ℂ x ((complexMatrixGramLin A) x)) := by
        rfl
      _ = RCLike.re
            (inner ℂ x
              (((n : ℂ) •
                (LinearMap.id :
                  EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) x)) := by
        rw [hgram]
      _ = RCLike.re (inner ℂ x ((n : ℂ) • x)) := by
        simp
      _ = (n : ℝ) * ‖x‖ ^ 2 := by
        rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
        change (((n : ℂ) * ((‖x‖ : ℂ) ^ 2)).re) = (n : ℝ) * ‖x‖ ^ 2
        rw [Complex.mul_re]
        simp [pow_two]
  have htarget :
      (Real.sqrt (n : ℝ) * ‖x‖) ^ 2 = (n : ℝ) * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  change ‖L x‖ ^ 2 ≤ (Real.sqrt (n : ℝ) * ‖x‖) ^ 2
  rw [hsq, htarget]

theorem complexMatrixOp2_sq_eq_top_gramEigenvalue {m n : ℕ}
    (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixOp2 A ^ 2 =
      complexMatrixGramEigenvalues A ⟨0, hn⟩ := by
  rw [complexMatrixOp2_eq_norm_euclideanLin, pow_two]
  rw [← ContinuousLinearMap.norm_adjoint_comp_self
    ((complexMatrixEuclideanLin A).toContinuousLinearMap),
    ← complexMatrixGramLin_toContinuousLinearMap A]
  exact complexMatrixGramLin_norm_eq_top_eigenvalue hn A

theorem complexMatrixOp2_eq_top_singularValue {m n : ℕ}
    (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixOp2 A =
      complexMatrixSingularValue A ⟨0, hn⟩ := by
  apply (sq_eq_sq₀ (complexMatrixOp2_nonneg A)
    (complexMatrixSingularValue_nonneg A ⟨0, hn⟩)).mp
  rw [complexMatrixSingularValue_sq]
  exact complexMatrixOp2_sq_eq_top_gramEigenvalue hn A

theorem complexMatrixSingularValue_le_complexMatrixOp2 {m n : ℕ}
    (A : CMatrix m n) (i : Fin n) :
    complexMatrixSingularValue A i ≤ complexMatrixOp2 A := by
  calc
    complexMatrixSingularValue A i =
        ‖complexMatrixEuclideanLin A (complexMatrixGramEigenvectorBasis A i)‖ := by
          rw [complexMatrixSingularValue_eq_norm_euclideanLin_gramEigenvectorBasis]
    _ = ‖(complexMatrixEuclideanLin A).toContinuousLinearMap
          (complexMatrixGramEigenvectorBasis A i)‖ := rfl
    _ ≤ ‖(complexMatrixEuclideanLin A).toContinuousLinearMap‖ *
          ‖complexMatrixGramEigenvectorBasis A i‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖(complexMatrixEuclideanLin A).toContinuousLinearMap‖ := by
          simp [complexMatrixGramEigenvectorBasis]
    _ = complexMatrixOp2 A := by
          rw [complexMatrixOp2_eq_norm_euclideanLin]

/-- The Euclidean operator `2`-norm is bounded by the Frobenius norm. -/
theorem complexMatrixOp2_le_complexMatrixFrobenius {m n : ℕ}
    (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixOp2 A ≤ complexMatrixFrobenius A := by
  apply (sq_le_sq₀ (complexMatrixOp2_nonneg A)
    (complexMatrixFrobenius_nonneg A)).mp
  rw [complexMatrixOp2_sq_eq_top_gramEigenvalue hn,
    complexMatrixFrobenius_sq,
    complexMatrixFrobeniusSq_eq_sum_gramEigenvalues]
  exact Finset.single_le_sum
    (fun i _hi => complexMatrixGramEigenvalues_nonneg A i)
    (Finset.mem_univ (⟨0, hn⟩ : Fin n))

/-- Squared Frobenius norm is bounded by the source dimension times the
    squared Euclidean operator `2`-norm. This is the dimension-cardinality
    version of the later rank-sensitive estimate. -/
theorem complexMatrixFrobeniusSq_le_card_mul_complexMatrixOp2_sq {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobeniusSq A ≤ (n : ℝ) * complexMatrixOp2 A ^ 2 := by
  rw [complexMatrixFrobeniusSq_eq_sum_singularValue_sq]
  calc
    (∑ i : Fin n, complexMatrixSingularValue A i ^ 2)
        ≤ ∑ _i : Fin n, complexMatrixOp2 A ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          exact (sq_le_sq₀ (complexMatrixSingularValue_nonneg A i)
            (complexMatrixOp2_nonneg A)).mpr
            (complexMatrixSingularValue_le_complexMatrixOp2 A i)
    _ = (n : ℝ) * complexMatrixOp2 A ^ 2 := by
          simp [nsmul_eq_mul]

/-- Frobenius norm is bounded by `sqrt n` times the Euclidean operator
    `2`-norm, where `n` is the source dimension. -/
theorem complexMatrixFrobenius_le_sqrt_card_mul_complexMatrixOp2 {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobenius A ≤
      Real.sqrt (n : ℝ) * complexMatrixOp2 A := by
  have hsq :
      complexMatrixFrobenius A ^ 2 ≤
        (Real.sqrt (n : ℝ) * complexMatrixOp2 A) ^ 2 := by
    rw [complexMatrixFrobenius_sq]
    calc
      complexMatrixFrobeniusSq A
          ≤ (n : ℝ) * complexMatrixOp2 A ^ 2 :=
            complexMatrixFrobeniusSq_le_card_mul_complexMatrixOp2_sq A
      _ = (Real.sqrt (n : ℝ) * complexMatrixOp2 A) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (sq_le_sq₀ (complexMatrixFrobenius_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (complexMatrixOp2_nonneg A))).mp hsq

lemma complexMatrixEuclideanLin_mul {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) (x : EuclideanSpace Complex (Fin p)) :
    complexMatrixEuclideanLin (complexMatrixMul A B) x =
      complexMatrixEuclideanLin A (complexMatrixEuclideanLin B x) := by
  apply WithLp.ofLp_injective
  calc
    WithLp.ofLp (complexMatrixEuclideanLin (complexMatrixMul A B) x)
        = complexMatrixVecMul (complexMatrixMul A B) (WithLp.ofLp x) := rfl
    _ = complexMatrixVecMul A (complexMatrixVecMul B (WithLp.ofLp x)) :=
        complexMatrixVecMul_mul A B (WithLp.ofLp x)
    _ = WithLp.ofLp (complexMatrixEuclideanLin A (complexMatrixEuclideanLin B x)) := rfl

/-- Squared left product form of Higham Problem 6.5:
    `||AB||_F^2 <= ||A||_2^2 ||B||_F^2`. -/
theorem complexMatrixFrobeniusSq_mul_le_op2_sq_mul {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixFrobeniusSq (complexMatrixMul A B) <=
      (complexMatrixOp2 A) ^ 2 * (complexMatrixFrobeniusSq B) := by
  rw [complexMatrixFrobeniusSq_eq_sum_col_norm_sq (A := complexMatrixMul A B),
    complexMatrixFrobeniusSq_eq_sum_col_norm_sq (A := B)]
  calc
    Finset.univ.sum (fun j : Fin p =>
        (norm (complexMatrixEuclideanLin (complexMatrixMul A B)
          (EuclideanSpace.basisFun (Fin p) Complex j))) ^ 2)
        <= Finset.univ.sum (fun j : Fin p =>
            ((complexMatrixOp2 A) *
              norm (complexMatrixEuclideanLin B
                (EuclideanSpace.basisFun (Fin p) Complex j))) ^ 2) := by
          apply Finset.sum_le_sum
          intro j _hj
          have hbound :
              norm (complexMatrixEuclideanLin (complexMatrixMul A B)
                (EuclideanSpace.basisFun (Fin p) Complex j)) <=
                (complexMatrixOp2 A) *
                  norm (complexMatrixEuclideanLin B
                    (EuclideanSpace.basisFun (Fin p) Complex j)) := by
            rw [complexMatrixEuclideanLin_mul]
            simpa [complexMatrixOp2_eq_norm_euclideanLin A] using
              ContinuousLinearMap.le_opNorm
                ((complexMatrixEuclideanLin A).toContinuousLinearMap)
                (complexMatrixEuclideanLin B (EuclideanSpace.basisFun (Fin p) Complex j))
          have hleft_nonneg :
              0 <= norm (complexMatrixEuclideanLin (complexMatrixMul A B)
                (EuclideanSpace.basisFun (Fin p) Complex j)) := norm_nonneg _
          have hright_nonneg :
              0 <= (complexMatrixOp2 A) *
                norm (complexMatrixEuclideanLin B
                  (EuclideanSpace.basisFun (Fin p) Complex j)) :=
            mul_nonneg (complexMatrixOp2_nonneg A) (norm_nonneg _)
          nlinarith
    _ = Finset.univ.sum (fun j : Fin p =>
            (complexMatrixOp2 A) ^ 2 *
              (norm (complexMatrixEuclideanLin B
                (EuclideanSpace.basisFun (Fin p) Complex j))) ^ 2) := by
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ = (complexMatrixOp2 A) ^ 2 *
          Finset.univ.sum (fun j : Fin p =>
            (norm (complexMatrixEuclideanLin B
              (EuclideanSpace.basisFun (Fin p) Complex j))) ^ 2) := by
          rw [Finset.mul_sum]

/-- Left product form of Higham Problem 6.5:
    `||AB||_F <= ||A||_2 ||B||_F`. -/
theorem complexMatrixFrobenius_mul_le_op2_mul {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixFrobenius (complexMatrixMul A B) <=
      complexMatrixOp2 A * complexMatrixFrobenius B := by
  have hsq :
      (complexMatrixFrobenius (complexMatrixMul A B)) ^ 2 <=
        (complexMatrixOp2 A * complexMatrixFrobenius B) ^ 2 := by
    rw [complexMatrixFrobenius_sq]
    calc
      complexMatrixFrobeniusSq (complexMatrixMul A B)
          <= (complexMatrixOp2 A) ^ 2 * complexMatrixFrobeniusSq B :=
            complexMatrixFrobeniusSq_mul_le_op2_sq_mul A B
      _ = (complexMatrixOp2 A * complexMatrixFrobenius B) ^ 2 := by
            rw [show (complexMatrixOp2 A * complexMatrixFrobenius B) ^ 2 =
                (complexMatrixOp2 A) ^ 2 * (complexMatrixFrobenius B) ^ 2 by ring,
              complexMatrixFrobenius_sq]
  exact le_of_sq_le_sq hsq
    (mul_nonneg (complexMatrixOp2_nonneg A) (complexMatrixFrobenius_nonneg B))

/-- Right product form of Higham Problem 6.5:
    `||BC||_F <= ||B||_F ||C||_2`. -/
theorem complexMatrixFrobenius_mul_le_mul_op2 {m n p : ℕ}
    (B : CMatrix m n) (C : CMatrix n p) :
    complexMatrixFrobenius (complexMatrixMul B C) <=
      complexMatrixFrobenius B * complexMatrixOp2 C := by
  have hleft :=
    complexMatrixFrobenius_mul_le_op2_mul
      (complexMatrixAdjoint C) (complexMatrixAdjoint B)
  calc
    complexMatrixFrobenius (complexMatrixMul B C)
        = complexMatrixFrobenius (complexMatrixAdjoint (complexMatrixMul B C)) := by
            rw [complexMatrixFrobenius_adjoint_eq]
    _ = complexMatrixFrobenius
          (complexMatrixMul (complexMatrixAdjoint C) (complexMatrixAdjoint B)) := by
            rw [complexMatrixAdjoint_mul]
    _ <= complexMatrixOp2 (complexMatrixAdjoint C) *
          complexMatrixFrobenius (complexMatrixAdjoint B) := hleft
    _ = complexMatrixOp2 C * complexMatrixFrobenius B := by
          rw [complexMatrixOp2_adjoint_eq, complexMatrixFrobenius_adjoint_eq]
    _ = complexMatrixFrobenius B * complexMatrixOp2 C := by ring

/-- The finite-dimensional foundation requested by GPT-5.5 Pro: every square
    Euclidean contraction is the midpoint of two unitary matrices. -/
def ComplexSquareContractionMidpointProperty (n : ℕ) : Prop :=
  ∀ L : CMatrix n n, complexMatrixOp2 L <= 1 →
    ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
      L = (fun i j =>
        (1 / 2 : ℂ) *
          ((U : Matrix (Fin n) (Fin n) ℂ) i j +
            (V : Matrix (Fin n) (Fin n) ℂ) i j))

/-- Full local rank makes every local singular value nonzero. -/
theorem complexMatrixSingularValue_ne_zero_of_rank_eq_card {m n : Nat}
    (A : CMatrix m n) (hrank : complexMatrixRank A = n) :
    ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 := by
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun i => complexMatrixSingularValue A i ≠ 0)
  have hcard_s : s.card = Fintype.card (Fin n) := by
    calc
      s.card =
          Fintype.card
            {i : Fin n // complexMatrixSingularValue A i ≠ 0} := by
            simp [s, Fintype.card_subtype]
      _ = complexMatrixRank A :=
            (complexMatrixRank_eq_card_nonzero_singularValue A).symm
      _ = n := hrank
      _ = Fintype.card (Fin n) := by simp
  have hall := (Finset.card_filter_eq_iff
    (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => complexMatrixSingularValue A i ≠ 0)).mp
    (by simpa [s] using hcard_s)
  intro i
  exact hall i (Finset.mem_univ i)
end NumStability
