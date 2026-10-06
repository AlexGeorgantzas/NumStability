-- Source/Higham/Chapter06/Problem10.lean
--
-- Higham Chapter 6, Problem 6.10 source-facing theorem package.

import NumStability.Analysis.SingularValues.Basic

/-!
# Higham Chapter 6, Problem 6.10

Formalizes the two-block shear operator and sharp Euclidean operator-norm
formula from Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., Problem 6.10.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Two-block complex Euclidean vectors for the block matrix
    `[[I, F], [0, I]]` in Higham Problem 6.10.  The Boolean index keeps the
    proof on a direct two-block type; a `Fin (2*n)` reindexing can be added at
    a theorem boundary if a later API needs literal matrix dimensions. -/
abbrev ComplexTwoBlockVec (n : ℕ) := EuclideanSpace ℂ (Bool × Fin n)

section

-- Reuse the frozen numeral witness that the former monolith kept in its local cache.
attribute [local instance]
  NumStability.ComplexSquareContractionMidpointProperty.«_proof_1»

noncomputable def complexTwoBlockFirst {n : ℕ} (z : ComplexTwoBlockVec n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp (2 : ENNReal) (fun i => WithLp.ofLp z (false, i))

noncomputable def complexTwoBlockSecond {n : ℕ} (z : ComplexTwoBlockVec n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp (2 : ENNReal) (fun i => WithLp.ofLp z (true, i))

noncomputable def complexTwoBlockBuild {n : ℕ}
    (x y : EuclideanSpace ℂ (Fin n)) : ComplexTwoBlockVec n :=
  WithLp.toLp (2 : ENNReal) fun bi =>
    match bi.1 with
    | false => WithLp.ofLp x bi.2
    | true => WithLp.ofLp y bi.2

end

@[simp]
lemma complexTwoBlockFirst_build {n : ℕ}
    (x y : EuclideanSpace ℂ (Fin n)) :
    complexTwoBlockFirst (complexTwoBlockBuild x y) = x := by
  ext i
  simp [complexTwoBlockFirst, complexTwoBlockBuild]

@[simp]
lemma complexTwoBlockSecond_build {n : ℕ}
    (x y : EuclideanSpace ℂ (Fin n)) :
    complexTwoBlockSecond (complexTwoBlockBuild x y) = y := by
  ext i
  simp [complexTwoBlockSecond, complexTwoBlockBuild]

/-- Linear map form of Higham Problem 6.10's block matrix:
    `(x, y) ↦ (x + F y, y)`. -/
noncomputable def complexMatrixBlockShearLinearMap {n : ℕ} (F : CMatrix n n) :
    ComplexTwoBlockVec n →ₗ[ℂ] ComplexTwoBlockVec n where
  toFun z :=
    complexTwoBlockBuild
      (complexTwoBlockFirst z + complexMatrixEuclideanLin F (complexTwoBlockSecond z))
      (complexTwoBlockSecond z)
  map_add' z w := by
    ext bi
    cases bi with
    | mk b i =>
      cases b
      · simp [complexTwoBlockBuild, complexTwoBlockFirst, complexTwoBlockSecond,
          complexMatrixEuclideanLin, add_assoc, add_left_comm]
        exact congr_fun
          (Matrix.mulVec_add (F : Matrix (Fin n) (Fin n) ℂ)
            (fun i => WithLp.ofLp z (true, i))
            (fun i => WithLp.ofLp w (true, i))) i
      · simp [complexTwoBlockBuild, complexTwoBlockFirst, complexTwoBlockSecond,
          complexMatrixEuclideanLin, Matrix.mulVec]
  map_smul' a z := by
    ext bi
    cases bi with
    | mk b i =>
      cases b
      · simp [complexTwoBlockBuild, complexTwoBlockFirst, complexTwoBlockSecond,
          complexMatrixEuclideanLin, mul_add]
        exact congr_fun
          (Matrix.mulVec_smul (M := (F : Matrix (Fin n) (Fin n) ℂ)) a
            (fun i => WithLp.ofLp z (true, i))) i
      · simp [complexTwoBlockBuild, complexTwoBlockFirst, complexTwoBlockSecond,
          complexMatrixEuclideanLin, Matrix.mulVec]

noncomputable def complexMatrixBlockShearCLM {n : ℕ} (F : CMatrix n n) :
    ComplexTwoBlockVec n →L[ℂ] ComplexTwoBlockVec n :=
  (complexMatrixBlockShearLinearMap F).toContinuousLinearMap

/-- Euclidean operator norm of Higham Problem 6.10's block shear operator. -/
noncomputable def complexMatrixBlockShearOp2 {n : ℕ} (F : CMatrix n n) : ℝ :=
  ‖complexMatrixBlockShearCLM F‖

@[simp]
lemma complexMatrixBlockShear_first {n : ℕ}
    (F : CMatrix n n) (z : ComplexTwoBlockVec n) :
    complexTwoBlockFirst (complexMatrixBlockShearLinearMap F z) =
      complexTwoBlockFirst z + complexMatrixEuclideanLin F (complexTwoBlockSecond z) := by
  simp [complexMatrixBlockShearLinearMap]

@[simp]
lemma complexMatrixBlockShear_second {n : ℕ}
    (F : CMatrix n n) (z : ComplexTwoBlockVec n) :
    complexTwoBlockSecond (complexMatrixBlockShearLinearMap F z) =
      complexTwoBlockSecond z := by
  simp [complexMatrixBlockShearLinearMap]

/-- The Euclidean norm on the two-block index splits into the two component
    Euclidean norm squares. -/
lemma complexTwoBlockVec_norm_sq_eq {n : ℕ} (z : ComplexTwoBlockVec n) :
    ‖z‖ ^ 2 = ‖complexTwoBlockFirst z‖ ^ 2 + ‖complexTwoBlockSecond z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [complexTwoBlockFirst, complexTwoBlockSecond, add_comm]

lemma complexMatrixBlockShear_norm_sq_eq {n : ℕ}
    (F : CMatrix n n) (z : ComplexTwoBlockVec n) :
    ‖complexMatrixBlockShearCLM F z‖ ^ 2 =
      ‖complexTwoBlockFirst z + complexMatrixEuclideanLin F (complexTwoBlockSecond z)‖ ^ 2 +
        ‖complexTwoBlockSecond z‖ ^ 2 := by
  rw [complexTwoBlockVec_norm_sq_eq]
  simp [complexMatrixBlockShearCLM]

section

-- Reuse the frozen numeral witness that the former monolith kept in its local cache.
attribute [local instance]
  NumStability.ComplexSquareContractionMidpointProperty.«_proof_1»

/-- The scalar factor in Higham Problem 6.10:
    `q(t) = (t + sqrt (4+t^2))/2`. -/
noncomputable def highamProblem610Q (t : ℝ) : ℝ :=
  (t + Real.sqrt (4 + t ^ 2)) / 2

end

lemma highamProblem610Q_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ highamProblem610Q t := by
  unfold highamProblem610Q
  have hsqrt_nonneg : 0 ≤ Real.sqrt (4 + t ^ 2) := Real.sqrt_nonneg _
  nlinarith

lemma highamProblem610Q_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < highamProblem610Q t := by
  unfold highamProblem610Q
  have hsqrt_pos : 0 < Real.sqrt (4 + t ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg t]
  nlinarith

lemma highamProblem610Q_sq {t : ℝ} (_ht : 0 ≤ t) :
    highamProblem610Q t ^ 2 = 1 + t * highamProblem610Q t := by
  unfold highamProblem610Q
  have hrad_nonneg : 0 ≤ 4 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hsqrt_sq : Real.sqrt (4 + t ^ 2) ^ 2 = 4 + t ^ 2 :=
    Real.sq_sqrt hrad_nonneg
  nlinarith [hsqrt_sq]

lemma highamProblem610_scalar_bound {t a b : ℝ} (ht : 0 ≤ t) :
    (a + t * b) ^ 2 + b ^ 2 ≤
      highamProblem610Q t ^ 2 * (a ^ 2 + b ^ 2) := by
  let q := highamProblem610Q t
  have hqpos : 0 < q := highamProblem610Q_pos ht
  have hq : q ^ 2 = 1 + t * q := highamProblem610Q_sq ht
  have hgap :
      q * (q ^ 2 * (a ^ 2 + b ^ 2) - ((a + t * b) ^ 2 + b ^ 2)) =
        t * (q * a - b) ^ 2 := by
    have hzero : q ^ 2 - 1 - t * q = 0 := by nlinarith [hq]
    calc
      q * (q ^ 2 * (a ^ 2 + b ^ 2) - ((a + t * b) ^ 2 + b ^ 2))
          = t * (q * a - b) ^ 2 +
              (q ^ 2 - 1 - t * q) * (q * a ^ 2 + (q + t) * b ^ 2) := by
            ring
      _ = t * (q * a - b) ^ 2 := by
            rw [hzero]
            ring
  have hmul_nonneg :
      0 ≤ q * (q ^ 2 * (a ^ 2 + b ^ 2) - ((a + t * b) ^ 2 + b ^ 2)) := by
    rw [hgap]
    exact mul_nonneg ht (sq_nonneg _)
  have hdiff_nonneg :
      0 ≤ q ^ 2 * (a ^ 2 + b ^ 2) - ((a + t * b) ^ 2 + b ^ 2) :=
    nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hmul_nonneg) hqpos
  nlinarith

lemma complexMatrixBlockShear_apply_norm_le {n : ℕ}
    (F : CMatrix n n) (z : ComplexTwoBlockVec n) :
    ‖complexMatrixBlockShearCLM F z‖ ≤
      highamProblem610Q (complexMatrixOp2 F) * ‖z‖ := by
  let t : ℝ := complexMatrixOp2 F
  let q : ℝ := highamProblem610Q t
  let x : EuclideanSpace ℂ (Fin n) := complexTwoBlockFirst z
  let y : EuclideanSpace ℂ (Fin n) := complexTwoBlockSecond z
  have ht : 0 ≤ t := complexMatrixOp2_nonneg F
  have hq_nonneg : 0 ≤ q := highamProblem610Q_nonneg ht
  have hFy : ‖complexMatrixEuclideanLin F y‖ ≤ t * ‖y‖ := by
    simpa [t, complexMatrixOp2_eq_norm_euclideanLin F] using
      ContinuousLinearMap.le_opNorm
        ((complexMatrixEuclideanLin F).toContinuousLinearMap) y
  have hxFy :
      ‖x + complexMatrixEuclideanLin F y‖ ≤ ‖x‖ + t * ‖y‖ :=
    (norm_add_le x (complexMatrixEuclideanLin F y)).trans
      (add_le_add (le_refl ‖x‖) hFy)
  have hright_nonneg : 0 ≤ ‖x‖ + t * ‖y‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))
  have hxFy_sq :
      ‖x + complexMatrixEuclideanLin F y‖ ^ 2 ≤ (‖x‖ + t * ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mpr hxFy
  have hscalar :
      (‖x‖ + t * ‖y‖) ^ 2 + ‖y‖ ^ 2 ≤
        q ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    highamProblem610_scalar_bound ht
  have hsq :
      ‖complexMatrixBlockShearCLM F z‖ ^ 2 ≤ (q * ‖z‖) ^ 2 := by
    rw [complexMatrixBlockShear_norm_sq_eq]
    calc
      ‖complexTwoBlockFirst z + complexMatrixEuclideanLin F (complexTwoBlockSecond z)‖ ^ 2 +
          ‖complexTwoBlockSecond z‖ ^ 2
          ≤ (‖x‖ + t * ‖y‖) ^ 2 + ‖y‖ ^ 2 := by
            exact add_le_add hxFy_sq (le_refl _)
      _ ≤ q ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := hscalar
      _ = (q * ‖z‖) ^ 2 := by
            rw [mul_pow, complexTwoBlockVec_norm_sq_eq z]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hq_nonneg (norm_nonneg _))).mp hsq

theorem complexMatrixBlockShearOp2_le {n : ℕ} (F : CMatrix n n) :
    complexMatrixBlockShearOp2 F ≤ highamProblem610Q (complexMatrixOp2 F) := by
  apply ContinuousLinearMap.opNorm_le_bound (complexMatrixBlockShearCLM F)
    (highamProblem610Q_nonneg (complexMatrixOp2_nonneg F))
  intro z
  exact complexMatrixBlockShear_apply_norm_le F z

lemma highamProblem610Q_zero : highamProblem610Q 0 = 1 := by
  unfold highamProblem610Q
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num
  rw [hsqrt4]
  norm_num

lemma complexMatrixBlockShear_attaining_vector_norm
    {n : ℕ} (F : CMatrix n n) {t : ℝ} (ht : 0 ≤ t)
    {u v : EuclideanSpace ℂ (Fin n)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hFv : complexMatrixEuclideanLin F v = (t : ℂ) • u) :
    let q := highamProblem610Q t
    let z : ComplexTwoBlockVec n := complexTwoBlockBuild u ((q : ℂ) • v)
    ‖complexMatrixBlockShearCLM F z‖ = q * ‖z‖ := by
  intro q z
  have hq_nonneg : 0 ≤ q := highamProblem610Q_nonneg ht
  have hq_sq : q ^ 2 = 1 + t * q := highamProblem610Q_sq ht
  have hfirst :
      complexTwoBlockFirst (complexMatrixBlockShearCLM F z) = ((q ^ 2 : ℝ) : ℂ) • u := by
    dsimp [z]
    change complexTwoBlockFirst
        (complexMatrixBlockShearLinearMap F (complexTwoBlockBuild u ((q : ℂ) • v))) =
      ((q ^ 2 : ℝ) : ℂ) • u
    rw [complexMatrixBlockShear_first]
    rw [complexTwoBlockFirst_build, complexTwoBlockSecond_build, map_smul, hFv, smul_smul]
    have hscalar : (1 : ℂ) + (q : ℂ) * (t : ℂ) = ((q ^ 2 : ℝ) : ℂ) := by
      norm_num [hq_sq]
      ring
    calc
      u + ((q : ℂ) * (t : ℂ)) • u =
          ((1 : ℂ) + (q : ℂ) * (t : ℂ)) • u := by
            rw [add_smul, one_smul]
      _ = ((q ^ 2 : ℝ) : ℂ) • u := by rw [hscalar]
  have hsecond :
      complexTwoBlockSecond (complexMatrixBlockShearCLM F z) = (q : ℂ) • v := by
    dsimp [z]
    change complexTwoBlockSecond
        (complexMatrixBlockShearLinearMap F (complexTwoBlockBuild u ((q : ℂ) • v))) =
      (q : ℂ) • v
    rw [complexMatrixBlockShear_second, complexTwoBlockSecond_build]
  have hqv_norm : ‖(q : ℂ) • v‖ = q := by
    rw [norm_smul, Complex.norm_of_nonneg hq_nonneg, hv, mul_one]
  have hq2u_norm : ‖(((q ^ 2 : ℝ) : ℂ) • u)‖ = q ^ 2 := by
    have hq2_nonneg : 0 ≤ q ^ 2 := sq_nonneg q
    rw [norm_smul, Complex.norm_of_nonneg hq2_nonneg, hu, mul_one]
  have hqv_norm_sq : ‖((q : ℂ) • v)‖ ^ 2 = q ^ 2 := by
    rw [hqv_norm]
  have hq2u_norm_sq : ‖(((q ^ 2 : ℝ) : ℂ) • u)‖ ^ 2 = q ^ 4 := by
    rw [hq2u_norm]
    ring
  have hz_sq : ‖z‖ ^ 2 = 1 + q ^ 2 := by
    rw [complexTwoBlockVec_norm_sq_eq]
    dsimp [z]
    rw [complexTwoBlockFirst_build, complexTwoBlockSecond_build, hu]
    change 1 ^ 2 + ‖((q : ℂ) • v)‖ ^ 2 = 1 + q ^ 2
    rw [hqv_norm_sq]
    ring
  have hsq :
      ‖complexMatrixBlockShearCLM F z‖ ^ 2 = (q * ‖z‖) ^ 2 := by
    rw [complexTwoBlockVec_norm_sq_eq, hfirst, hsecond]
    rw [mul_pow, hz_sq]
    rw [hq2u_norm_sq, hqv_norm_sq]
    ring
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg hq_nonneg (norm_nonneg _))).mp
  exact hsq

lemma highamProblem610Q_le_of_singular_pair
    {n : ℕ} (F : CMatrix n n) {t : ℝ} (ht : 0 ≤ t)
    {u v : EuclideanSpace ℂ (Fin n)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hFv : complexMatrixEuclideanLin F v = (t : ℂ) • u) :
    highamProblem610Q t ≤ complexMatrixBlockShearOp2 F := by
  let q := highamProblem610Q t
  let z : ComplexTwoBlockVec n := complexTwoBlockBuild u ((q : ℂ) • v)
  have hq_nonneg : 0 ≤ q := highamProblem610Q_nonneg ht
  have hqv_norm : ‖(q : ℂ) • v‖ = q := by
    rw [norm_smul, Complex.norm_of_nonneg hq_nonneg, hv, mul_one]
  have hz_sq : ‖z‖ ^ 2 = 1 + q ^ 2 := by
    rw [complexTwoBlockVec_norm_sq_eq]
    dsimp [z]
    rw [complexTwoBlockFirst_build, complexTwoBlockSecond_build, hu]
    change 1 ^ 2 + ‖((q : ℂ) • v)‖ ^ 2 = 1 + q ^ 2
    rw [hqv_norm]
    ring
  have hz_pos : 0 < ‖z‖ := by
    have hz_ne : ‖z‖ ≠ 0 := by
      intro hz
      have hsqzero : ‖z‖ ^ 2 = 0 := by simp [hz]
      have hpos : 0 < 1 + q ^ 2 := by nlinarith [sq_nonneg q]
      nlinarith
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz_ne)
  have hattain :
      ‖complexMatrixBlockShearCLM F z‖ = q * ‖z‖ :=
    complexMatrixBlockShear_attaining_vector_norm F ht hu hv hFv
  have hle := ContinuousLinearMap.le_opNorm (complexMatrixBlockShearCLM F) z
  have hle' : q * ‖z‖ ≤ ‖complexMatrixBlockShearCLM F‖ * ‖z‖ := by
    rw [← hattain]
    exact hle
  have hmul : q * ‖z‖ ≤ complexMatrixBlockShearOp2 F * ‖z‖ := by
    simpa [complexMatrixBlockShearOp2] using hle'
  exact le_of_mul_le_mul_right hmul hz_pos

/-- Higham Problem 6.10, compact local form:
    `||[[I,F],[0,I]]||_2 = (||F||_2 + sqrt(4 + ||F||_2^2))/2`. -/
theorem complexMatrixBlockShearOp2_eq_highamProblem610Q
    {n : ℕ} (hn : 0 < n) (F : CMatrix n n) :
    complexMatrixBlockShearOp2 F = highamProblem610Q (complexMatrixOp2 F) := by
  apply le_antisymm
  · exact complexMatrixBlockShearOp2_le F
  · let i0 : Fin n := ⟨0, hn⟩
    let t : ℝ := complexMatrixOp2 F
    have ht_nonneg : 0 ≤ t := complexMatrixOp2_nonneg F
    by_cases ht0 : t = 0
    · let v : EuclideanSpace ℂ (Fin n) := complexMatrixGramEigenvectorBasis F i0
      have hv : ‖v‖ = 1 := complexMatrixGramEigenvectorBasis_norm F i0
      have hσ0 : complexMatrixSingularValue F i0 = 0 := by
        rw [← complexMatrixOp2_eq_top_singularValue hn F]
        exact ht0
      have hFv0 : complexMatrixEuclideanLin F v = 0 :=
        complexMatrixEuclideanLin_gramEigenvectorBasis_eq_zero_of_singularValue_eq_zero
          F i0 hσ0
      have hFv : complexMatrixEuclideanLin F v = (t : ℂ) • v := by
        rw [hFv0, ht0]
        simp
      simpa [t] using
        highamProblem610Q_le_of_singular_pair F ht_nonneg hv hv hFv
    · let v : EuclideanSpace ℂ (Fin n) := complexMatrixGramEigenvectorBasis F i0
      let u : EuclideanSpace ℂ (Fin n) := complexMatrixLeftSingularVector F i0
      have hv : ‖v‖ = 1 := complexMatrixGramEigenvectorBasis_norm F i0
      have ht_sing : complexMatrixSingularValue F i0 = t := by
        rw [← complexMatrixOp2_eq_top_singularValue hn F]
      have hσne : complexMatrixSingularValue F i0 ≠ 0 := by
        rw [ht_sing]
        exact ht0
      have hu : ‖u‖ = 1 := complexMatrixLeftSingularVector_norm_of_ne_zero F i0 hσne
      have hFv : complexMatrixEuclideanLin F v = (t : ℂ) • u := by
        rw [complexMatrixEuclideanLin_gramEigenvectorBasis_eq_singularValue_smul_left_all,
          ht_sing]
      simpa [t] using
        highamProblem610Q_le_of_singular_pair F ht_nonneg hu hv hFv

lemma highamProblem610Q_eq_sourceFormula {t : ℝ} (ht : 0 ≤ t) :
    highamProblem610Q t =
      Real.sqrt ((2 + t ^ 2 + t * Real.sqrt (4 + t ^ 2)) / 2) := by
  let q := highamProblem610Q t
  have hq_nonneg : 0 ≤ q := highamProblem610Q_nonneg ht
  have hrad_nonneg : 0 ≤ 4 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hsqrt_sq : Real.sqrt (4 + t ^ 2) ^ 2 = 4 + t ^ 2 :=
    Real.sq_sqrt hrad_nonneg
  have hformula : (2 + t ^ 2 + t * Real.sqrt (4 + t ^ 2)) / 2 = q ^ 2 := by
    unfold q highamProblem610Q
    nlinarith [hsqrt_sq]
  rw [hformula, Real.sqrt_sq_eq_abs, abs_of_nonneg hq_nonneg]

/-- Higham Problem 6.10, printed square-root formula for the local block
    shear operator. -/
theorem complexMatrixBlockShearOp2_eq_highamProblem610_sourceFormula
    {n : ℕ} (hn : 0 < n) (F : CMatrix n n) :
    complexMatrixBlockShearOp2 F =
      Real.sqrt ((2 + complexMatrixOp2 F ^ 2 +
          complexMatrixOp2 F * Real.sqrt (4 + complexMatrixOp2 F ^ 2)) / 2) := by
  rw [complexMatrixBlockShearOp2_eq_highamProblem610Q hn F,
    highamProblem610Q_eq_sourceFormula (complexMatrixOp2_nonneg F)]

/-- Golden-ratio specialization in Higham Problem 6.10:
    if `||F||_2 = 1`, the scalar factor is `(1 + sqrt 5)/2`. -/
lemma highamProblem610Q_one_eq_goldenRatio :
    highamProblem610Q 1 = (1 + Real.sqrt 5) / 2 := by
  unfold highamProblem610Q
  norm_num

theorem complexMatrixBlockShearOp2_eq_goldenRatio_of_op2_eq_one
    {n : ℕ} (hn : 0 < n) {F : CMatrix n n}
    (hF : complexMatrixOp2 F = 1) :
    complexMatrixBlockShearOp2 F = (1 + Real.sqrt 5) / 2 := by
  rw [complexMatrixBlockShearOp2_eq_highamProblem610Q hn F, hF,
    highamProblem610Q_one_eq_goldenRatio]
end NumStability
