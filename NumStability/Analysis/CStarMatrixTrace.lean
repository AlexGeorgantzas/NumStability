-- Analysis/CStarMatrixTrace.lean
--
-- Trace bridge for complex C⋆-matrices used by future trace-MGF arguments.

import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.OperatorLog
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

namespace NumStability

open scoped ComplexOrder

/-!
## Trace for complex C⋆-matrices

The Tropp/Lieb matrix-Laplace route is naturally stated for traces of
exponentials of complex self-adjoint matrices.  The repository's RandNLA
statements use function-valued finite real matrices and `finiteTrace`.

This file provides a small bridge: a trace on mathlib's `CStarMatrix` type, and
agreement with `finiteTrace` after embedding a finite real matrix into complex
C⋆-matrices.  It is trace vocabulary only; it does not prove trace-MGF
domination.
-/

/-- Ring-hom version of the finite-real-to-complex `CStarMatrix` embedding.

This is useful when transporting power-series constructions, especially the
repository-native real matrix exponential, through the complex C⋆-matrix
interface used by the Lieb/Tropp trace-MGF argument. -/
noncomputable def finiteComplexCStarMatrixRingHom {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ →+* CStarMatrix ι ι ℂ :=
  (CStarMatrix.ofMatrixRingEquiv : Matrix ι ι ℂ ≃+* CStarMatrix ι ι ℂ).toRingHom.comp
    (Complex.ofRealHom.mapMatrix)

@[simp]
theorem finiteComplexCStarMatrixRingHom_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (i j : ι) :
    finiteComplexCStarMatrixRingHom (ι := ι) M i j = (M i j : ℂ) := by
  rfl

/-- The ring-hom embedding from finite real matrices to complex C⋆-matrices is
continuous for the entrywise matrix topologies. -/
theorem finiteComplexCStarMatrixRingHom_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (finiteComplexCStarMatrixRingHom (ι := ι)) := by
  change Continuous fun M : Matrix ι ι ℝ =>
    CStarMatrix.ofMatrix (fun i j => (M i j : ℂ))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))

/-- The complex C⋆ embedding commutes with the repository-native finite real
matrix exponential. -/
theorem finiteComplexCStarMatrix_finiteMatrixExp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) :
    finiteComplexCStarMatrix (finiteMatrixExp M) =
      NormedSpace.exp (finiteComplexCStarMatrix M) := by
  let Mm : Matrix ι ι ℝ := M
  have hleft : Function.LeftInverse
      (fun C : CStarMatrix ι ι ℂ => (fun i j => (C i j).re : Matrix ι ι ℝ))
      (finiteComplexCStarMatrixRingHom (ι := ι)) := by
    intro M
    ext i j
    rfl
  have hleft_cont : Continuous
      (fun C : CStarMatrix ι ι ℂ => (fun i j => (C i j).re : Matrix ι ι ℝ)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))
  rw [finiteMatrixExp]
  change finiteComplexCStarMatrix
      ((@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
        (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
        (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
        Mm : Matrix ι ι ℝ)) =
      NormedSpace.exp (finiteComplexCStarMatrix M)
  rw [@NormedSpace.exp_eq_tsum_rat (Matrix ι ι ℝ) Matrix.instRing
      (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
      (Matrix.topologicalRing : IsTopologicalRing (Matrix ι ι ℝ))
      (inferInstance : Algebra ℚ (Matrix ι ι ℝ))]
  rw [@NormedSpace.exp_eq_tsum_rat (CStarMatrix ι ι ℂ)
      (CStarMatrix.instRing (n := ι) (A := ℂ))
      (inferInstance : TopologicalSpace (CStarMatrix ι ι ℂ))
      (cstarMatrix_normedSpaceExp_isTopologicalRing (ι := ι))
      (inferInstance : Algebra ℚ (CStarMatrix ι ι ℂ))]
  dsimp only
  have hbase :
      finiteComplexCStarMatrixRingHom (ι := ι) Mm =
        finiteComplexCStarMatrix M := by
    ext i j
    rfl
  have hmap := Function.LeftInverse.map_tsum
      (L := SummationFilter.unconditional ℕ)
      (f := fun n : ℕ => ((n.factorial : ℚ)⁻¹) • Mm ^ n)
      (g := finiteComplexCStarMatrixRingHom (ι := ι))
      (g' := fun C : CStarMatrix ι ι ℂ =>
        (fun i j => (C i j).re : Matrix ι ι ℝ))
      finiteComplexCStarMatrixRingHom_continuous hleft_cont hleft
  calc
    finiteComplexCStarMatrix
        (∑' n : ℕ, ((n.factorial : ℚ)⁻¹) • Mm ^ n) =
        finiteComplexCStarMatrixRingHom (ι := ι)
          (∑' n : ℕ, ((n.factorial : ℚ)⁻¹) • Mm ^ n) := by
          ext i j
          rfl
    _ = ∑' n : ℕ,
          finiteComplexCStarMatrixRingHom (ι := ι)
            (((n.factorial : ℚ)⁻¹) • Mm ^ n) := hmap
    _ = ∑' n : ℕ, ((n.factorial : ℚ)⁻¹) •
          (finiteComplexCStarMatrix M) ^ n := by
          congr
          funext n
          rw [map_inv_natCast_smul (finiteComplexCStarMatrixRingHom (ι := ι))
            ℚ ℚ n.factorial (Mm ^ n)]
          rw [map_pow]
          rw [hbase]

/-- A finite sum of self-adjoint C⋆-matrices is self-adjoint. -/
theorem cstarMatrix_finset_sum_isSelfAdjoint
    {α ι : Type*} [Fintype ι] [DecidableEq α]
    (s : Finset α) (F : α → CStarMatrix ι ι ℂ)
    (hF : ∀ a ∈ s, IsSelfAdjoint (F a)) :
    IsSelfAdjoint (s.sum F) := by
  classical
  revert hF
  refine Finset.induction_on s ?base ?step
  · intro _hF
    simp
  · intro a s has ih hF
    rw [Finset.sum_insert has]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih (fun b hb => hF b (Finset.mem_insert_of_mem hb)))

/-- Matrix trace on the complex `CStarMatrix` type. -/
noncomputable def cstarMatrixTrace {ι : Type*} [Fintype ι]
    (M : CStarMatrix ι ι ℂ) : ℂ :=
  ∑ i, M i i

@[simp]
theorem cstarMatrixTrace_apply {ι : Type*} [Fintype ι]
    (M : CStarMatrix ι ι ℂ) :
    cstarMatrixTrace M = ∑ i, M i i := by
  rfl

@[simp]
theorem cstarMatrixTrace_zero {ι : Type*} [Fintype ι] :
    cstarMatrixTrace (0 : CStarMatrix ι ι ℂ) = 0 := by
  simp [cstarMatrixTrace]

theorem cstarMatrixTrace_add {ι : Type*} [Fintype ι]
    (M N : CStarMatrix ι ι ℂ) :
    cstarMatrixTrace (M + N) = cstarMatrixTrace M + cstarMatrixTrace N := by
  simp [cstarMatrixTrace, Finset.sum_add_distrib]

theorem cstarMatrixTrace_smul {ι : Type*} [Fintype ι]
    (a : ℂ) (M : CStarMatrix ι ι ℂ) :
    cstarMatrixTrace (a • M) = a * cstarMatrixTrace M := by
  simp [cstarMatrixTrace, Finset.mul_sum]

theorem cstarMatrixTrace_neg {ι : Type*} [Fintype ι]
    (M : CStarMatrix ι ι ℂ) :
    cstarMatrixTrace (-M) = -cstarMatrixTrace M := by
  simp [cstarMatrixTrace]

theorem cstarMatrixTrace_sub {ι : Type*} [Fintype ι]
    (M N : CStarMatrix ι ι ℂ) :
    cstarMatrixTrace (M - N) = cstarMatrixTrace M - cstarMatrixTrace N := by
  simp [cstarMatrixTrace, Finset.sum_sub_distrib]

theorem cstarMatrixTrace_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cstarMatrixTrace (1 : CStarMatrix ι ι ℂ) = (Fintype.card ι : ℂ) := by
  simp [cstarMatrixTrace]

theorem cstarMatrixTrace_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℂ) :
    cstarMatrixTrace (a • (1 : CStarMatrix ι ι ℂ)) =
      a * (Fintype.card ι : ℂ) := by
  rw [cstarMatrixTrace_smul, cstarMatrixTrace_one]

/-- A finite sum of a constant scalar identity is the scalar identity with
coefficient multiplied by the number of summands. -/
theorem cstarMatrix_finset_sum_const_complex_smul_one
    {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (s : Finset α) (c : ℂ) :
    (∑ _a ∈ s, c • (1 : CStarMatrix ι ι ℂ)) =
      ((s.card : ℂ) * c) • (1 : CStarMatrix ι ι ℂ) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, ih]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Nat.cast_add, Nat.cast_one]
      ring
    · simp [hij]

/-- `Fin`-indexed specialization of
`cstarMatrix_finset_sum_const_complex_smul_one`. -/
theorem cstarMatrix_fin_sum_const_complex_smul_one
    {steps : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ) :
    (∑ _t : Fin steps, c • (1 : CStarMatrix ι ι ℂ)) =
      ((steps : ℂ) * c) • (1 : CStarMatrix ι ι ℂ) := by
  simpa [Fintype.card_fin] using
    cstarMatrix_finset_sum_const_complex_smul_one
      (s := (Finset.univ : Finset (Fin steps))) (ι := ι) c

/-- Cyclicity of the complex C⋆ matrix trace.  This is trace vocabulary needed
for future Golden-Thompson/Lieb-style trace-MGF arguments. -/
theorem cstarMatrixTrace_mul_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : CStarMatrix ι ι ℂ) :
    cstarMatrixTrace (M * N) = cstarMatrixTrace (N * M) := by
  simpa [cstarMatrixTrace, Matrix.trace, CStarMatrix.mul_apply] using
    (Matrix.trace_mul_comm (CStarMatrix.ofMatrix.symm M)
      (CStarMatrix.ofMatrix.symm N))

/-- The complex C⋆ trace has nonnegative real part on a square `Sᴴ S`. -/
theorem cstarMatrixTrace_star_mul_self_re_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : CStarMatrix ι ι ℂ) :
    0 ≤ (cstarMatrixTrace (star S * S)).re := by
  have hpsd :
      (Matrix.PosSemidef
        ((CStarMatrix.ofMatrix.symm (star S * S)) : Matrix ι ι ℂ)) := by
    simpa [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply] using
      (Matrix.posSemidef_conjTranspose_mul_self
        (CStarMatrix.ofMatrix.symm S : Matrix ι ι ℂ))
  have htrace :
      0 ≤ Matrix.trace
        ((CStarMatrix.ofMatrix.symm (star S * S)) : Matrix ι ι ℂ) :=
    hpsd.trace_nonneg
  have htrace' : 0 ≤ cstarMatrixTrace (star S * S) := by
    simpa [cstarMatrixTrace, Matrix.trace] using htrace
  exact (Complex.nonneg_iff.mp htrace').1

/-- The complex C⋆ trace has nonnegative real part on positive C⋆ matrices.

This uses the spectral order representation of positive elements as the
additive closure of squares `Sᴴ S`; it is not a trace-MGF domination theorem. -/
theorem cstarMatrixTrace_re_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CStarMatrix ι ι ℂ} (hM : 0 ≤ M) :
    0 ≤ (cstarMatrixTrace M).re := by
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem x hx =>
      rcases hx with ⟨S, rfl⟩
      exact cstarMatrixTrace_star_mul_self_re_nonneg S
  | zero =>
      simp [cstarMatrixTrace]
  | add x y hx hy ihx ihy =>
      rw [cstarMatrixTrace_add]
      simpa using add_nonneg ihx ihy

/-- Real-part monotonicity of the complex C⋆ trace for the C⋆ spectral order. -/
theorem cstarMatrixTrace_re_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : CStarMatrix ι ι ℂ} (hMN : M ≤ N) :
    (cstarMatrixTrace M).re ≤ (cstarMatrixTrace N).re := by
  have hdiff :
      0 ≤ (cstarMatrixTrace (N - M)).re :=
    cstarMatrixTrace_re_nonneg_of_nonneg (M := N - M) (sub_nonneg.mpr hMN)
  rw [cstarMatrixTrace_sub] at hdiff
  exact sub_nonneg.mp hdiff

/-- The complex C⋆ trace of a self-adjoint matrix is real-valued. -/
theorem cstarMatrixTrace_im_eq_zero_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CStarMatrix ι ι ℂ} (hM : IsSelfAdjoint M) :
    (cstarMatrixTrace M).im = 0 := by
  rw [cstarMatrixTrace, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  have hdiag_star : star (M i i) = M i i := by
    simpa [CStarMatrix.star_apply] using congr_fun (congr_fun hM i) i
  exact Complex.conj_eq_iff_im.mp hdiag_star

/-- The complex C⋆ trace of an embedded finite real matrix is the complex cast
of the repository-native finite real trace. -/
theorem cstarMatrixTrace_finiteComplexCStarMatrix
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) :
    cstarMatrixTrace (finiteComplexCStarMatrix M) = (finiteTrace M : ℂ) := by
  simp [cstarMatrixTrace, finiteComplexCStarMatrix, finiteTrace]

/-- Real part form of `cstarMatrixTrace_finiteComplexCStarMatrix`. -/
theorem cstarMatrixTrace_finiteComplexCStarMatrix_re
    {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) :
    (cstarMatrixTrace (finiteComplexCStarMatrix M)).re = finiteTrace M := by
  rw [cstarMatrixTrace_finiteComplexCStarMatrix]
  simp

/-- Complex trace form of the finite-real matrix-exponential bridge. -/
theorem cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) :
    cstarMatrixTrace (NormedSpace.exp (finiteComplexCStarMatrix M)) =
      (finiteTrace (finiteMatrixExp M) : ℂ) := by
  rw [← finiteComplexCStarMatrix_finiteMatrixExp M]
  exact cstarMatrixTrace_finiteComplexCStarMatrix (finiteMatrixExp M)

/-- Real-part trace form of the finite-real matrix-exponential bridge.  This
is the direct adapter from the C⋆ trace-MGF layer to the repository's finite
real trace-exponential concentration interface. -/
theorem cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) :
    (cstarMatrixTrace (NormedSpace.exp (finiteComplexCStarMatrix M))).re =
      finiteTrace (finiteMatrixExp M) := by
  rw [cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix]
  simp

/-- Real-part nonnegativity of the complex C⋆ trace for embedded finite PSD
real matrices. -/
theorem cstarMatrixTrace_finiteComplexCStarMatrix_re_nonneg_of_finitePSD
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : finitePSD M) :
    0 ≤ (cstarMatrixTrace (finiteComplexCStarMatrix M)).re := by
  rw [cstarMatrixTrace_finiteComplexCStarMatrix_re]
  exact finiteTrace_nonneg_of_finitePSD M hM

/-- Real-part monotonicity of the complex C⋆ trace after embedding a finite
real Loewner inequality. -/
theorem cstarMatrixTrace_finiteComplexCStarMatrix_re_mono_of_finiteLoewnerLe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : ι → ι → ℝ} (hMN : finiteLoewnerLe M N) :
    (cstarMatrixTrace (finiteComplexCStarMatrix M)).re ≤
      (cstarMatrixTrace (finiteComplexCStarMatrix N)).re := by
  rw [cstarMatrixTrace_finiteComplexCStarMatrix_re]
  rw [cstarMatrixTrace_finiteComplexCStarMatrix_re]
  exact finiteTrace_mono_of_finiteLoewnerLe hMN

/-- The complex CFC exponential of a scalar identity has the expected trace. -/
theorem cstarMatrixTrace_cfc_exp_algebraMap
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℂ) :
    cstarMatrixTrace
        (cfc (p := IsStarNormal) Complex.exp
          (algebraMap ℂ (CStarMatrix ι ι ℂ) a)) =
      Complex.exp a * (Fintype.card ι : ℂ) := by
  have h :
      cfc (p := IsStarNormal) Complex.exp
          (algebraMap ℂ (CStarMatrix ι ι ℂ) a) =
        algebraMap ℂ (CStarMatrix ι ι ℂ) (Complex.exp a) := by
    exact
      cfc_algebraMap (R := ℂ) (A := CStarMatrix ι ι ℂ)
        (p := IsStarNormal) a Complex.exp
  calc
    cstarMatrixTrace
        (cfc (p := IsStarNormal) Complex.exp
          (algebraMap ℂ (CStarMatrix ι ι ℂ) a)) =
        cstarMatrixTrace
          (algebraMap ℂ (CStarMatrix ι ι ℂ) (Complex.exp a)) :=
      congrArg cstarMatrixTrace h
    _ = Complex.exp a * (Fintype.card ι : ℂ) := by
      simp [Algebra.algebraMap_eq_smul_one, mul_comm]

/-- Real scalar-identity form of
`cstarMatrixTrace_cfc_exp_algebraMap`. -/
theorem cstarMatrixTrace_cfc_exp_real_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℝ) :
    cstarMatrixTrace
        (cfc (p := IsStarNormal) Complex.exp
          ((a : ℂ) • (1 : CStarMatrix ι ι ℂ))) =
      (Real.exp a : ℂ) * (Fintype.card ι : ℂ) := by
  have harg :
      ((a : ℂ) • (1 : CStarMatrix ι ι ℂ)) =
        algebraMap ℂ (CStarMatrix ι ι ℂ) (a : ℂ) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [harg]
  simpa [Complex.ofReal_exp] using
    cstarMatrixTrace_cfc_exp_algebraMap (ι := ι) (a := (a : ℂ))

/-- A scalar-identity upper bound on a self-adjoint finite complex C⋆-matrix
also bounds its normed-algebra exponential by the exponential scalar identity.

This is the C⋆ analogue of
`finiteTrace_finiteMatrixExp_le_card_mul_exp_of_finiteLoewnerLe_smul_id`; it is
the deterministic scalarization step needed after a matrix-CGF/log-MGF Loewner
bound has been proved. -/
theorem cstarMatrix_normedSpace_exp_le_real_smul_one_of_le_real_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) {c : ℝ}
    (hLe : H ≤ (c : ℂ) • (1 : CStarMatrix ι ι ℂ)) :
    NormedSpace.exp H ≤
      (Real.exp c : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
  have hmono :
      cfc (p := IsSelfAdjoint) Real.exp H ≤
        cfc (p := IsSelfAdjoint) (fun _x : ℝ => Real.exp c) H := by
    exact cfc_mono (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (a := H)
      (f := Real.exp) (g := fun _x : ℝ => Real.exp c)
      (fun x hx =>
        Real.exp_le_exp.mpr
          (cstarMatrix_spectrum_le_of_le_real_smul_one hLe hx))
      (hf := by fun_prop) (hg := by fun_prop)
  have hleft :
      cfc (p := IsSelfAdjoint) Real.exp H = NormedSpace.exp H :=
    CFC.real_exp_eq_normedSpace_exp
      (A := CStarMatrix ι ι ℂ) (a := H) hH
  have hright :
      cfc (p := IsSelfAdjoint) (fun _x : ℝ => Real.exp c) H =
        (Real.exp c : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
    rw [cfc_const (R := ℝ) (A := CStarMatrix ι ι ℂ)
      (p := IsSelfAdjoint) (r := Real.exp c) (a := H) (ha := hH)]
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  simpa [hleft, hright] using hmono

/-- Trace scalarization for a self-adjoint C⋆ matrix whose spectrum is bounded
above by a scalar identity. -/
theorem cstarMatrixTrace_normedSpace_exp_re_le_card_mul_exp_of_le_real_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H) {c : ℝ}
    (hLe : H ≤ (c : ℂ) • (1 : CStarMatrix ι ι ℂ)) :
    (cstarMatrixTrace (NormedSpace.exp H)).re ≤
      (Fintype.card ι : ℝ) * Real.exp c := by
  have hExpLe :
      NormedSpace.exp H ≤
        (Real.exp c : ℂ) • (1 : CStarMatrix ι ι ℂ) :=
    cstarMatrix_normedSpace_exp_le_real_smul_one_of_le_real_smul_one hH hLe
  have htrace := cstarMatrixTrace_re_mono hExpLe
  rw [cstarMatrixTrace_smul_one] at htrace
  have htrace' :
      (cstarMatrixTrace (NormedSpace.exp H)).re ≤
        Real.exp c * (Fintype.card ι : ℝ) := by
    simpa [Complex.ofReal_exp] using htrace
  simpa [mul_comm] using htrace'

end NumStability
