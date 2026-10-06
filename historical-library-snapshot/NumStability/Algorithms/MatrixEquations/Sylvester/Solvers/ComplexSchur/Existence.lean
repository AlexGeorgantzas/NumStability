import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Vec
import NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation

/-!
# Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.Existence

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
Analysis/SylvesterSchurExistence.lean

Complex-path Schur existence for the Chapter 16 Sylvester equation
(Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Section 16.2, equations (16.4)-(16.6)).

MOTIVATION / HONEST SCOPE.

The real-valued Chapter 16 development
(`NumStability/Algorithms/Sylvester/Higham16.lean`,
`NumStability/Algorithms/Sylvester/Higham16Spectrum.lean`) proves the Bartels-Stewart
triangular solve only *conditionally* on SUPPLIED Schur factors: the theorem
`existsUnique_isSylvesterSolutionRect_schurTriangular` requires the caller to
hand over real orthogonal `U, V`, a real matrix `R` with `A = U R Uᵀ`, and a
real UPPER-TRIANGULAR `S` with `B = V S Vᵀ`.  That "supplied factors" hypothesis
is genuine and unavoidable there, because a real matrix in general has NO real
upper-triangular Schur form: the real Schur form of Higham (16.4) is only
*quasi*-triangular (2x2 real blocks for complex-conjugate eigenpairs).  The real
file therefore cannot discharge its own supplied-triangular hypothesis, and does
not claim to.

Over `ℂ`, by contrast, the classical Schur triangulation
`NumStability.schur_triangulation` (`NumStability/Analysis/SchurTriangulation.lean`)
gives, for EVERY complex square matrix, a genuine unitary `U` and a genuine
upper-triangular `T` with `Uᴴ A U = T`.  This file uses that primitive to turn
the complex analogue of the supplied-triangular hypothesis into an
*unconditional existence* statement, and then proves unique solvability of the
complex Sylvester equation `A X - X B = C`.

WHAT IS UNCONDITIONAL HERE (no supplied factors):

* `complexSylvester_schur_factors_exist` — for any `A : ℂ^{m×m}`,
  `B : ℂ^{n×n}` there exist a unitary `U` and upper-triangular `R` with
  `Uᴴ A U = R`, and a unitary `V` and upper-triangular `S` with `Vᴴ B V = S`.
  This is exactly the datum the real file must *assume*; over `ℂ` it is proved.

WHAT REMAINS AN EXPLICIT, NON-TAUTOLOGICAL HYPOTHESIS:

* the per-column shift nonsingularity `det (R - s_kk • I) ≠ 0`.  This is a
  condition on the DIAGONAL ENTRIES of the triangular factors, i.e. on the
  eigenvalues `λ_i(A) ≠ μ_k(B)` (the Sylvester separation / no-common-eigenvalue
  condition of (16.3)).  It is emphatically NOT the conclusion in disguise: it
  constrains only the (supplied-by-Schur) eigenvalues, not the solution `X`.  The
  headline theorem `complexSylvester_exists_unique_of_schur_shift` exposes it as
  a hypothesis phrased in terms of the Schur factors produced by the existence
  step, and states honestly that this is the residual assumption.

WHAT IS NOT CLAIMED:

* No real Schur form, no real quasi-triangular (2x2 block) solve of Higham
  (16.4)/(16.7)-(16.8): those are over `ℝ` and are genuinely different objects.
  This file does not touch, restate, or overclaim the real results.
* No floating-point rounding analysis; all arithmetic is exact over `ℂ`.
* No spectral converse claim beyond what the shift hypothesis encodes.

Everything is stated for the standard Mathlib matrix type `Matrix (Fin _) (Fin _)
ℂ` with ordinary matrix multiplication `*` and `Matrix.mulVec`, so that the
complex Schur primitive (`Uᴴ * A * U = T`) plugs in directly.
-/







open scoped BigOperators Matrix

namespace NumStability

-- ============================================================
-- The complex Sylvester operator and solution predicate
-- ============================================================

/-- Higham, 2nd ed., Chapter 16, equation (16.1), complex square form:
    the Sylvester operator `X ↦ A X - X B` on complex square matrices, using
    ordinary Mathlib matrix multiplication so that the complex Schur factors
    `Uᴴ A U` plug in directly. -/
noncomputable def complexSylvesterOp {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  A * X - X * B

/-- Higham, 2nd ed., Chapter 16, equation (16.1), complex square form:
    the predicate `A X - X B = C`. -/
def IsComplexSylvesterSolution {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C X : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  complexSylvesterOp A B X = C

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2), complex vec/Kronecker
    coefficient `I_n kron A - B^T kron I_m`.  The product index follows
    Mathlib's column-stacking convention: `(j,i)` denotes entry `(i,j)`. -/
noncomputable def complexSylvesterVecCoeff {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) A -
    Matrix.kronecker (Matrix.transpose B) (1 : Matrix (Fin m) (Fin m) ℂ)

/-- Left multiplication by `A` in vectorized complex form, the
    `I_n kron A` half of Higham, 2nd ed., Chapter 16.1, equation (16.2). -/
theorem complex_vec_left_mul_rect {m k n : ℕ}
    (A : Matrix (Fin m) (Fin k) ℂ)
    (X : Matrix (Fin k) (Fin n) ℂ) :
    Matrix.vec (A * X) =
      Matrix.mulVec
        (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) A)
        (Matrix.vec X) := by
  simpa [Matrix.kronecker] using Matrix.vec_mul_eq_mulVec A X

/-- Right multiplication by `B` in vectorized complex form, the
    `B^T kron I_m` half of Higham, 2nd ed., Chapter 16.1, equation (16.2). -/
theorem complex_vec_right_mul_rect {m n p : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin p) ℂ) :
    Matrix.vec (X * B) =
      Matrix.mulVec
        (Matrix.kronecker (Matrix.transpose B)
          (1 : Matrix (Fin m) (Fin m) ℂ))
        (Matrix.vec X) := by
  simpa [Matrix.kronecker] using
    (Matrix.kronecker_mulVec_vec (1 : Matrix (Fin m) (Fin m) ℂ)
      X (Matrix.transpose B)).symm

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2), complex form:
    applying `I_n kron A - B^T kron I_m` to `vec(X)` gives `vec(AX - XB)`. -/
theorem complexSylvesterVecCoeff_mulVec_vec {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.mulVec (complexSylvesterVecCoeff A B) (Matrix.vec X) =
      Matrix.vec (complexSylvesterOp A B X) := by
  ext p
  have hleft := congrFun (complex_vec_left_mul_rect A X) p
  have hright := congrFun (complex_vec_right_mul_rect X B) p
  unfold complexSylvesterVecCoeff
  simp only [Pi.sub_apply, Matrix.sub_mulVec, hleft.symm, hright.symm]
  simp [complexSylvesterOp, Matrix.vec, Matrix.mul_apply]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2), complex form:
    the vectorized linear system is equivalent to the Sylvester equation. -/
theorem complex_sylvester_vec_system_iff_solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C X : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.mulVec (complexSylvesterVecCoeff A B) (Matrix.vec X) = Matrix.vec C ↔
      IsComplexSylvesterSolution A B C X := by
  constructor
  · intro h
    unfold IsComplexSylvesterSolution
    ext i j
    have hp := congrFun h (j, i)
    rw [complexSylvesterVecCoeff_mulVec_vec] at hp
    simpa [Matrix.vec] using hp
  · intro h
    rw [complexSylvesterVecCoeff_mulVec_vec, h]

/-- If the homogeneous complex Sylvester equation has a unique solution, then
    the vec/Kronecker Sylvester coefficient matrix is nonsingular. -/
theorem complexSylvesterVecCoeff_det_ne_zero_of_unique_homogeneous {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (huniq : ∃! X : Matrix (Fin m) (Fin n) ℂ,
      IsComplexSylvesterSolution A B (0 : Matrix (Fin m) (Fin n) ℂ) X) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hvzero⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff
      (M := complexSylvesterVecCoeff A B)).mpr hdet
  let X : Matrix (Fin m) (Fin n) ℂ := fun i j => v (j, i)
  have hvecX : Matrix.vec X = v := by
    ext p
    cases p
    rfl
  have hXsol :
      IsComplexSylvesterSolution A B (0 : Matrix (Fin m) (Fin n) ℂ) X := by
    unfold IsComplexSylvesterSolution
    have hcoeff := complexSylvesterVecCoeff_mulVec_vec A B X
    rw [hvecX] at hcoeff
    have hvecOp : Matrix.vec (complexSylvesterOp A B X) = 0 :=
      hcoeff.symm.trans hvzero
    ext i j
    have hp := congrFun hvecOp (j, i)
    simpa [Matrix.vec] using hp
  have hzeroSol :
      IsComplexSylvesterSolution A B (0 : Matrix (Fin m) (Fin n) ℂ)
        (0 : Matrix (Fin m) (Fin n) ℂ) := by
    simp [IsComplexSylvesterSolution, complexSylvesterOp]
  obtain ⟨Y, _, huniqY⟩ := huniq
  have hXeq0 : X = 0 := by
    calc
      X = Y := huniqY X hXsol
      _ = 0 := (huniqY (0 : Matrix (Fin m) (Fin n) ℂ) hzeroSol).symm
  apply hvne
  rw [← hvecX, hXeq0]
  simp

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4): upper triangularity for a
    complex square matrix (all strictly-below-diagonal entries vanish).  This is
    the structure produced unconditionally by `schur_triangulation` over `ℂ`. -/
def IsUpperTriangularC {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n, j < i → T i j = 0

































































































































































































































































































/-- A diagonal entry of a supplied complex upper-triangular matrix makes the
    shifted matrix singular.  This is the finite-dimensional spectral fact
    behind using Schur diagonal entries in Higham (16.3). -/
theorem complexUpperTriangular_det_sub_diag_eq_zero {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : IsUpperTriangularC T) (i : Fin n) :
    Matrix.det (T - Matrix.scalar (Fin n) (T i i)) = 0 := by
  have htri : (T - Matrix.scalar (Fin n) (T i i)).BlockTriangular id := by
    intro a b hba
    have hzero : T a b = 0 := hT a b hba
    have hscalar : Matrix.scalar (Fin n) (T i i) a b = 0 := by
      rw [Matrix.scalar_apply]
      exact Matrix.diagonal_apply_ne _ (ne_of_gt hba)
    rw [Matrix.sub_apply, hzero, hscalar, sub_zero]
  rw [Matrix.det_of_upperTriangular htri]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by rw [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq, sub_self])

/-- Every diagonal entry of a supplied complex upper-triangular matrix is
    realized by a nonzero right eigenvector. -/
theorem complexUpperTriangular_exists_eigenpair_diag {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : IsUpperTriangularC T) (i : Fin n) :
    ∃ y : Fin n → ℂ,
      y ≠ 0 ∧ Matrix.mulVec T y = fun k => T i i * y k := by
  obtain ⟨y, hyne, hyzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr
      (complexUpperTriangular_det_sub_diag_eq_zero T hT i)
  refine ⟨y, hyne, ?_⟩
  funext k
  have hk := congrFun hyzero k
  have hcoord : Matrix.mulVec T y k - T i i * y k = 0 := by
    simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hk
  exact sub_eq_zero.mp hcoord

/-- Supplied complex upper-triangular spectral bridge: if two triangular factors
    have no common supplied right eigenpair, then their diagonal entries are
    pairwise separated. -/
theorem complexUpperTriangular_diagonal_separation_of_no_common_eigenpair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j := by
  intro i j hij
  have hAeig := complexUpperTriangular_exists_eigenpair_diag A hA i
  have hBeig :
      ∃ z : Fin n → ℂ,
        z ≠ 0 ∧ Matrix.mulVec B z = fun k => A i i * z k := by
    obtain ⟨z, hzne, hz⟩ := complexUpperTriangular_exists_eigenpair_diag B hB j
    refine ⟨z, hzne, ?_⟩
    simpa [hij] using hz
  exact hno (A i i) ⟨hAeig, hBeig⟩



































-- ============================================================
-- Complex Schur factors exist unconditionally
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), complex Schur factors:
    for any complex square matrices `A` and `B` there exist unitary `U`, `V` and
    upper-triangular `R`, `S` with `Uᴴ A U = R` and `Vᴴ B V = S`.

    This is UNCONDITIONAL: it is exactly the datum that the real-valued file
    `Higham16Spectrum.lean` must supply as a hypothesis, discharged here by the
    complex Schur triangulation `schur_triangulation`.  (Over `ℝ` the analogous
    statement is false — the real Schur form is only quasi-triangular — so no
    real theorem is being restated or overclaimed.) -/
theorem complexSylvester_schur_factors_exist {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (R : Matrix (Fin m) (Fin m) ℂ)
      (V : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ Uᴴ * A * U = R ∧ IsUpperTriangularC R ∧
      V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Vᴴ * B * V = S ∧ IsUpperTriangularC S := by
  obtain ⟨U, R, hUu, hUeq, hRtri⟩ := schur_triangulation A
  obtain ⟨V, S, hVu, hVeq, hStri⟩ := schur_triangulation B
  exact ⟨U, R, V, S, hUu, hUeq, hRtri, hVu, hVeq, hStri⟩

-- ============================================================
-- The transformed equation R Y - Y S = C' in Schur coordinates
-- ============================================================

/-- Conjugation of the Sylvester operator by supplied unitary factors, complex
    form of Higham (16.5).  With `Uᴴ A U = R`, `Vᴴ B V = S`, and `X = U Y Vᴴ`,
    the operator transforms as `A X - X B = U (R Y - Y S) Vᴴ`. -/
theorem complexSylvesterOp_conj {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S) :
    complexSylvesterOp A B (U * Y * Vᴴ) =
      U * (complexSylvesterOp R S Y) * Vᴴ := by
  have hUU : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hVV : Vᴴ * V = 1 := by
    have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
  -- express R and S back through A, B
  subst hR
  subst hS
  simp only [complexSylvesterOp, Matrix.mul_sub, Matrix.sub_mul]
  -- U (Uᴴ A U Y - Y Vᴴ B V) Vᴴ = A (U Y Vᴴ) - (U Y Vᴴ) B
  have e1 : U * (Uᴴ * A * U * Y) * Vᴴ = A * (U * Y * Vᴴ) := by
    have : U * (Uᴴ * A * U * Y) * Vᴴ = (U * Uᴴ) * A * (U * Y * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [this, hUU, Matrix.one_mul]
  have e2 : U * (Y * (Vᴴ * B * V)) * Vᴴ = (U * Y * Vᴴ) * B := by
    have : U * (Y * (Vᴴ * B * V)) * Vᴴ = (U * Y * Vᴴ) * B * (V * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [this]
    have hVV' : V * Vᴴ = 1 := by
      have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
    rw [hVV', Matrix.mul_one]
  rw [e1, e2]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.5), complex form:
    with supplied unitary factors, `X = U Y Vᴴ` solves `A X - X B = C` iff `Y`
    solves the transformed equation `R Y - Y S = Uᴴ C V`. -/
theorem isComplexSylvesterSolution_conj_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S) :
    IsComplexSylvesterSolution A B C (U * Y * Vᴴ) ↔
      IsComplexSylvesterSolution R S (Uᴴ * C * V) Y := by
  have hUU : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hUhU : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hVV : V * Vᴴ = 1 := by
    have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hVhV : Vᴴ * V = 1 := by
    have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hconj := complexSylvesterOp_conj A B U V R S Y hU hV hR hS
  constructor
  · intro h
    -- h : A (U Y Vᴴ) - (U Y Vᴴ) B = C, i.e. U (RY - YS) Vᴴ = C
    unfold IsComplexSylvesterSolution at h ⊢
    rw [hconj] at h
    -- Uᴴ (U (RY-YS) Vᴴ) V = RY - YS ; Uᴴ C V is RHS
    have := congrArg (fun M => Uᴴ * M * V) h
    simp only at this
    rw [← this]
    have lhs :
        Uᴴ * (U * complexSylvesterOp R S Y * Vᴴ) * V =
          complexSylvesterOp R S Y := by
      have step : Uᴴ * (U * complexSylvesterOp R S Y * Vᴴ) * V =
          (Uᴴ * U) * complexSylvesterOp R S Y * (Vᴴ * V) := by
        simp only [Matrix.mul_assoc]
      rw [step, hUhU, hVhV, Matrix.one_mul, Matrix.mul_one]
    rw [lhs]
  · intro h
    unfold IsComplexSylvesterSolution at h ⊢
    rw [hconj, h]
    -- U (Uᴴ C V) Vᴴ = C
    have step : U * (Uᴴ * C * V) * Vᴴ = (U * Uᴴ) * C * (V * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [step, hUU, hVV, Matrix.one_mul, Matrix.mul_one]

-- ============================================================
-- The complex Bartels-Stewart column solve
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex form: the shifted
    column coefficient `R - s • I` appearing in the column recurrence
    `(R - s_kk I) y_k = ...`. -/
def complexShiftedCoeff {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (s : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  R - s • (1 : Matrix (Fin m) (Fin m) ℂ)

/-- A finite upper-triangular complex matrix with nonzero diagonal has nonzero
    determinant.  This is the complex analogue of the repository's real
    triangular determinant bridge, using the same below-diagonal convention. -/
theorem complex_det_ne_zero_of_upperTriangular_diag_ne_zero {m : ℕ}
    (T : Matrix (Fin m) (Fin m) ℂ)
    (hupper : IsUpperTriangularC T)
    (hdiag : ∀ i : Fin m, T i i ≠ 0) :
    T.det ≠ 0 := by
  classical
  have htri : Matrix.BlockTriangular (M := T) id := by
    intro i j hij
    exact hupper i j (by simpa using hij)
  rw [Matrix.det_of_upperTriangular htri]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)

/-- Shifting an upper-triangular complex matrix by a scalar multiple of the
    identity preserves upper triangularity. -/
theorem complexShiftedCoeff_upperTriangular {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (s : ℂ)
    (hR : IsUpperTriangularC R) :
    IsUpperTriangularC (complexShiftedCoeff R s) := by
  intro i j hji
  have hij : i ≠ j := ne_of_gt hji
  simp [complexShiftedCoeff, Matrix.sub_apply, hR i j hji, hij]

/-- For an upper-triangular complex Schur factor, pairwise separation between a
    scalar `s` and the diagonal entries gives nonsingularity of the shifted
    column coefficient `R - s I`. -/
theorem complexShiftedCoeff_det_ne_zero_of_upperTriangular_diag_ne
    {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (s : ℂ)
    (hR : IsUpperTriangularC R)
    (hgap : ∀ i : Fin m, R i i ≠ s) :
    (complexShiftedCoeff R s).det ≠ 0 := by
  apply complex_det_ne_zero_of_upperTriangular_diag_ne_zero
  · exact complexShiftedCoeff_upperTriangular R s hR
  · intro i
    have hdiag : R i i - s ≠ 0 := sub_ne_zero.mpr (hgap i)
    simpa [complexShiftedCoeff] using hdiag

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex Schur diagonal
    separation supplies the per-column shifted determinant hypotheses for the
    triangular Bartels-Stewart solve. -/
theorem complexSylvester_shift_det_ne_zero_of_schur_diagonal_separation
    {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (hR : IsUpperTriangularC R)
    (hsep : ∀ i : Fin m, ∀ k : Fin n, R i i ≠ S k k) :
    ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0 := by
  intro k
  exact complexShiftedCoeff_det_ne_zero_of_upperTriangular_diag_ne
    R (S k k) hR (fun i => hsep i k)













/-- Entrywise column identity: for upper-triangular `S`, applying the shifted
    coefficient to column `k` of `Y` reproduces the `k`-th column of the
    Sylvester operator `R Y - Y S` plus a sum over strictly earlier columns.
    This is the pure algebra behind Higham (16.6). -/
theorem complexSylvester_column_identity {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S) (k : Fin n) :
    (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
      (fun i => complexSylvesterOp R S Y i k +
        ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) := by
  funext i
  -- expand shifted coefficient
  have hlhs :
      (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) i =
        (∑ l : Fin m, R i l * Y l k) - S k k * Y i k := by
    unfold complexShiftedCoeff
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [Matrix.mulVec, dotProduct]
  rw [hlhs]
  -- split the row sum ∑_j Y_ij S_jk using upper triangularity of S
  have hsplit :
      (∑ j : Fin n, Y i j * S j k) =
        S k k * Y i k +
          ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j := by
    -- keep only j ≤ k, since S j k = 0 for k < j
    have hsub : (∑ j ∈ Finset.univ.filter (fun j => j ≤ k), Y i j * S j k) =
        ∑ j : Fin n, Y i j * S j k := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hjnot
      have hnot : ¬ (j ≤ k) := by
        intro hle
        exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
      have hkj : k < j := not_le.mp hnot
      rw [hS j k hkj, mul_zero]
    rw [← hsub]
    have hset : Finset.univ.filter (fun j => j ≤ k) =
        insert k (Finset.univ.filter (fun j => j < k)) := by
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
    have hknotmem : k ∉ Finset.univ.filter (fun j => j < k) := by
      intro hmem
      exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl k)
    rw [hset, Finset.sum_insert hknotmem, mul_comm (Y i k) (S k k)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- assemble
  have hop : complexSylvesterOp R S Y i k =
      (∑ l : Fin m, R i l * Y l k) - (∑ j : Fin n, Y i j * S j k) := by
    unfold complexSylvesterOp
    simp [Matrix.mul_apply, Matrix.sub_apply]
  rw [hop, hsplit]
  ring

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex form: if `Y` solves
    `R Y - Y S = C` with `S` upper-triangular, then column `k` satisfies the
    Bartels-Stewart forward-substitution equation
    `(R - s_kk I) y_k = c_k + ∑_{j<k} s_jk y_j`. -/
theorem complexSylvester_column_equation {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S)
    (hY : IsComplexSylvesterSolution R S C Y) (k : Fin n) :
    (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
      (fun i => C i k +
        ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) := by
  rw [complexSylvester_column_identity R S Y hS k]
  funext i
  have : complexSylvesterOp R S Y i k = C i k := by
    unfold IsComplexSylvesterSolution at hY
    exact congrFun (congrFun hY i) k
  rw [this]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.5)-(16.6), complex form:
    for upper-triangular `S`, solving `R Y - Y S = C` is equivalent to
    satisfying every Bartels-Stewart column equation. -/
theorem isComplexSylvesterSolution_iff_columns {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S) :
    IsComplexSylvesterSolution R S C Y ↔
      ∀ k : Fin n,
        (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
          (fun i => C i k +
            ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) := by
  constructor
  · intro hY k
    exact complexSylvester_column_equation R S C Y hS hY k
  · intro h
    unfold IsComplexSylvesterSolution complexSylvesterOp
    ext i k
    have hk := congrFun (h k) i
    rw [complexSylvester_column_identity R S Y hS k] at hk
    -- hk : op i k + sum = C i k + sum  ⇒ op i k = C i k
    have := add_right_cancel hk
    -- goal: (R*Y - Y*S) i k = C i k
    have hop : complexSylvesterOp R S Y i k = C i k := this
    unfold complexSylvesterOp at hop
    simpa using hop

-- ============================================================
-- Uniqueness and existence of the column solve
-- ============================================================

































































































































































-- ============================================================
-- Headline: complex Sylvester unique solvability with Schur factors supplied
-- by existence (not by hypothesis)
-- ============================================================

















































































/-- Eigenpairs of a supplied complex Schur factor transfer back through the
    unitary similarity to eigenpairs of the original matrix. -/
theorem complexSchurFactor_eigenpair_to_original {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (y : Fin n → ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R)
    (hyne : y ≠ 0)
    (hy : Matrix.mulVec R y = fun i => μ * y i) :
    (Matrix.mulVec U y) ≠ 0 ∧
      Matrix.mulVec A (Matrix.mulVec U y) =
        fun i => μ * Matrix.mulVec U y i := by
  have hUU : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hUhU : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hAU : A * U = U * R := by
    calc
      A * U = (U * Uᴴ) * A * U := by rw [hUU, Matrix.one_mul]
      _ = U * (Uᴴ * A * U) := by simp [Matrix.mul_assoc]
      _ = U * R := by rw [hR]
  constructor
  · intro hUy
    apply hyne
    have hzero : Matrix.mulVec (Uᴴ * U) y = 0 := by
      rw [← Matrix.mulVec_mulVec y Uᴴ U, hUy, Matrix.mulVec_zero]
    simpa [hUhU] using hzero
  · calc
      Matrix.mulVec A (Matrix.mulVec U y)
          = Matrix.mulVec (A * U) y := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (U * R) y := by rw [hAU]
      _ = Matrix.mulVec U (Matrix.mulVec R y) := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec U (μ • y) := by
            rw [hy]
            rfl
      _ = μ • Matrix.mulVec U y := by rw [Matrix.mulVec_smul]
      _ = fun i => μ * Matrix.mulVec U y i := rfl

/-- Supplied complex Schur factors inherit diagonal separation from a
    no-common-right-eigenpair hypothesis on the original matrices. -/
theorem complexSchur_diagonal_separation_of_no_common_eigenpair {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S)
    (hRtri : IsUpperTriangularC R)
    (hStri : IsUpperTriangularC S)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    ∀ i : Fin m, ∀ j : Fin n, R i i ≠ S j j := by
  apply complexUpperTriangular_diagonal_separation_of_no_common_eigenpair
    R S hRtri hStri
  intro μ hcommon
  rcases hcommon with ⟨⟨y, hyne, hy⟩, ⟨z, hzne, hz⟩⟩
  obtain ⟨hUy_ne, hUy⟩ :=
    complexSchurFactor_eigenpair_to_original A U R μ y hU hR hyne hy
  obtain ⟨hVz_ne, hVz⟩ :=
    complexSchurFactor_eigenpair_to_original B V S μ z hV hS hzne hz
  exact hno μ ⟨⟨Matrix.mulVec U y, hUy_ne, hUy⟩,
    ⟨Matrix.mulVec V z, hVz_ne, hVz⟩⟩















































































































































end NumStability
