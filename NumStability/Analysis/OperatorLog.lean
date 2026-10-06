-- Analysis/OperatorLog.lean
--
-- Operator-log foundations used by future trace-MGF / matrix-concentration
-- formalizations.

import NumStability.Analysis.CStarMatrixBridge
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Topology.Instances.Matrix

namespace NumStability

open scoped ComplexOrder Pointwise

/-!
## Operator-log monotonicity

Tropp's Lieb-style matrix Laplace transform method uses operator-log
monotonicity as one of the functional-calculus foundations behind
trace-MGF domination.  This file records the available mathlib theorem in the
matrix type where the C⋆-algebraic order instances are already present.

This is not yet the trace-MGF domination theorem for RandNLA Algorithm 1: the
finite-real-to-complex-C⋆ bridge and regularized log-monotonicity adapter below
only prepare the C⋆ functional-calculus interface.  The noncommutative
Lieb/Tropp trace-exponential step remains separate.
-/

/-- The `NormedSpace.exp` API asks for the topological-ring structure induced
by the ring instance.  The complex `CStarMatrix` topology is definitionally the
matrix topology, so we expose this bridge explicitly for the local
trace-exponential wrappers below. -/
noncomputable instance cstarMatrix_normedSpaceExp_isTopologicalRing
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @IsTopologicalRing (CStarMatrix ι ι ℂ) inferInstance
      (@NonAssocRing.toNonUnitalNonAssocRing (CStarMatrix ι ι ℂ)
        (@Ring.toNonAssocRing (CStarMatrix ι ι ℂ)
          (CStarMatrix.instRing (n := ι) (A := ℂ)))) := by
  change IsTopologicalRing (Matrix ι ι ℂ)
  infer_instance

/-- The same topological-ring bridge for the ring structure inherited from the
`NormedRing` instance.  Some functional-calculus theorems elaborate
`NormedSpace.exp` through this path rather than through `CStarMatrix.instRing`. -/
noncomputable instance cstarMatrix_normedRingExp_isTopologicalRing
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @IsTopologicalRing (CStarMatrix ι ι ℂ) inferInstance
      (@NonAssocRing.toNonUnitalNonAssocRing (CStarMatrix ι ι ℂ)
        (@Ring.toNonAssocRing (CStarMatrix ι ι ℂ)
          (@NormedRing.toRing (CStarMatrix ι ι ℂ)
            (CStarMatrix.instNormedRing (n := ι) (A := ℂ))))) := by
  change IsTopologicalRing (Matrix ι ι ℂ)
  infer_instance

/-- Real continuous functional calculus for finite complex C⋆-matrices,
obtained by restricting the complex normal calculus to self-adjoint elements. -/
noncomputable instance cstarMatrix_realContinuousFunctionalCalculus
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint := by
  exact (IsSelfAdjoint.instContinuousFunctionalCalculus
    (A := CStarMatrix ι ι ℂ))

/-- Real continuous functional calculus for complex scalars, restricted to the
self-adjoint/real line.  This is the scalar endpoint used when commuting the
operator logarithm with finite diagonal embeddings. -/
noncomputable instance complex_realContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ ℂ IsSelfAdjoint := by
  exact (IsSelfAdjoint.instContinuousFunctionalCalculus (A := ℂ))

/-- Real continuous functional calculus for finite vectors of complex scalars,
restricted coordinatewise to self-adjoint entries. -/
noncomputable instance piComplex_realContinuousFunctionalCalculus
    {ι : Type*} [Fintype ι] :
    ContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint := by
  exact (IsSelfAdjoint.instContinuousFunctionalCalculus (A := ι → ℂ))

/-- `CFC.exp_log` elaborates through the real `NormedAlgebra` instance induced
from the complex normed algebra.  This bridge exposes the corresponding
nonnegative-spectrum instance for finite complex C⋆-matrices. -/
noncomputable instance cstarMatrix_normedRingExp_nonnegSpectrumClass
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) _ _
      (@NonUnitalNormedRing.toNonUnitalRing (CStarMatrix ι ι ℂ)
        (@NormedRing.toNonUnitalNormedRing (CStarMatrix ι ι ℂ)
          (CStarMatrix.instNormedRing (n := ι) (A := ℂ))))
      inferInstance
      (@NormedSpace.toModule ℝ (CStarMatrix ι ι ℂ) _ _
        (@NormedAlgebra.toNormedSpace ℝ (CStarMatrix ι ι ℂ) _ _
          (@NormedAlgebra.complexToReal (CStarMatrix ι ι ℂ) _
            (CStarMatrix.instNormedAlgebra (n := ι) (A := ℂ))))) := by
  exact CStarAlgebra.instNonnegSpectrumClass

/-- Spectrum nonnegativity for finite complex C-star matrices, stated with
the algebra-module instance used by `spectrum ℝ A`.

The repository also exposes a `NonnegSpectrumClass` instance for the
normed-space route used by exponential/logarithm APIs.  This theorem is the
matching wrapper for ordinary real spectra; it avoids brittle typeclass search
through the several real module structures on `CStarMatrix`. -/
theorem cstarMatrix_spectrum_nonneg_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} (hA : 0 ≤ A)
    {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 ≤ x := by
  have hnn :
      @NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) inferInstance inferInstance
        (@Ring.toNonUnitalRing (CStarMatrix ι ι ℂ) inferInstance)
        inferInstance Algebra.toModule := by
    exact CStarAlgebra.instNonnegSpectrumClass
  exact @spectrum_nonneg_of_nonneg ℝ (CStarMatrix ι ι ℂ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    hnn A hA x hx

/-- A scalar-identity upper bound controls the real spectrum of a finite
complex C⋆-matrix. -/
theorem cstarMatrix_spectrum_le_of_le_real_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CStarMatrix ι ι ℂ} {c : ℝ}
    (hLe : A ≤ (c : ℂ) • (1 : CStarMatrix ι ι ℂ))
    {x : ℝ} (hx : x ∈ spectrum ℝ A) : x ≤ c := by
  have hnon :
      0 ≤ (algebraMap ℝ (CStarMatrix ι ι ℂ) c - A) := by
    simpa [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mpr hLe
  have hxsub : c - x ∈ ({c} : Set ℝ) - spectrum ℝ A := by
    refine ⟨c, by simp, x, hx, ?_⟩
    ring
  have hxdiff :
      c - x ∈ spectrum ℝ
        ((algebraMap ℝ (CStarMatrix ι ι ℂ)) c - A) := by
    rw [← spectrum.singleton_sub_eq A c]
    exact hxsub
  have hnonx : 0 ≤ c - x :=
    cstarMatrix_spectrum_nonneg_of_nonneg hnon hxdiff
  linarith

/-- Operator logarithm is monotone for strictly positive complex C⋆-matrices.

This is a repository-local wrapper around mathlib's `CFC.log_le_log`, isolated
so that the trace-MGF bottleneck can cite a stable theorem name. -/
theorem cstarMatrix_log_le_log
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CStarMatrix ι ι ℂ) (hAB : A ≤ B)
    (hA : IsStrictlyPositive A) :
    CFC.log A ≤ CFC.log B := by
  exact CFC.log_le_log hAB hA

/-- On self-adjoint finite complex C⋆-matrices, the operator logarithm
inverts the normed-algebra exponential. -/
theorem cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (hX : IsSelfAdjoint X) :
    CFC.log (NormedSpace.exp X) = X := by
  simpa using (CFC.log_exp (A := CStarMatrix ι ι ℂ) X hX)

/-- The same `log(exp X) = X` identity using the complex continuous
functional-calculus exponential. -/
theorem cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (hX : IsSelfAdjoint X) :
    CFC.log (cfc (p := IsStarNormal) Complex.exp X) = X := by
  rw [CFC.complex_exp_eq_normedSpace_exp]
  exact cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint X hX

/-- The same `log(exp X) = X` identity using the real continuous
functional-calculus exponential on self-adjoint matrices. -/
theorem cstarMatrix_log_cfc_real_exp_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (hX : IsSelfAdjoint X) :
    CFC.log (cfc (p := IsSelfAdjoint) Real.exp X) = X := by
  rw [show cfc (p := IsSelfAdjoint) Real.exp X = NormedSpace.exp X from
    CFC.real_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ) (a := X) hX]
  exact cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint X hX

/-- On self-adjoint finite complex C⋆-matrices, the normed-algebra
exponential is strictly positive.

This is the domain lemma needed before forming `log (E[exp X])` in the
Tropp/Lieb route: the exponential is nonnegative by functional calculus and
invertible by the Banach-algebra exponential API. -/
theorem cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (hX : IsSelfAdjoint X) :
    IsStrictlyPositive (NormedSpace.exp X) := by
  letI : NormedAlgebra ℚ (CStarMatrix ι ι ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (CStarMatrix ι ι ℂ)
  exact IsStrictlyPositive.iff_of_unital.mpr
    ⟨hX.exp_nonneg, NormedSpace.isUnit_exp X⟩

/-- The real continuous-functional-calculus exponential of a self-adjoint
finite complex C⋆-matrix is strictly positive. -/
theorem cstarMatrix_cfc_real_exp_isStrictlyPositive_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (hX : IsSelfAdjoint X) :
    IsStrictlyPositive (cfc (p := IsSelfAdjoint) Real.exp X) := by
  have hEq : cfc (p := IsSelfAdjoint) Real.exp X = NormedSpace.exp X :=
    CFC.real_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ) (a := X) hX
  exact hEq.symm ▸
    cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint X hX

/-- The complex continuous-functional-calculus exponential of a self-adjoint
finite complex C⋆-matrix is strictly positive. -/
theorem cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CStarMatrix ι ι ℂ) (hX : IsSelfAdjoint X) :
    IsStrictlyPositive (cfc (p := IsStarNormal) Complex.exp X) := by
  have hEq : cfc (p := IsStarNormal) Complex.exp X = NormedSpace.exp X :=
    CFC.complex_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ)
      (p := IsStarNormal) (a := X) hX.isStarNormal
  exact hEq.symm ▸
    cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint X hX

/-- On strictly positive finite complex C⋆-matrices, the normed-algebra
exponential inverts the operator logarithm. -/
theorem cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (hA : IsStrictlyPositive A) :
    NormedSpace.exp (CFC.log A) = A := by
  simpa using (CFC.exp_log (A := CStarMatrix ι ι ℂ) A hA)

/-- The same `exp(log A) = A` identity using the complex continuous
functional-calculus exponential. -/
theorem cstarMatrix_cfc_complex_exp_log_of_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (hA : IsStrictlyPositive A) :
    cfc (p := IsStarNormal) Complex.exp (CFC.log A) = A := by
  rw [show cfc (p := IsStarNormal) Complex.exp (CFC.log A) =
      NormedSpace.exp (CFC.log A) from
    CFC.complex_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ)
      (p := IsStarNormal) (a := CFC.log A)
      (IsSelfAdjoint.cfc.isStarNormal)]
  exact cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive A hA

/-- The same `exp(log A) = A` identity using the real continuous
functional-calculus exponential. -/
theorem cstarMatrix_cfc_real_exp_log_of_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (hA : IsStrictlyPositive A) :
    cfc (p := IsSelfAdjoint) Real.exp (CFC.log A) = A := by
  rw [show cfc (p := IsSelfAdjoint) Real.exp (CFC.log A) =
      NormedSpace.exp (CFC.log A) from
    CFC.real_exp_eq_normedSpace_exp (A := CStarMatrix ι ι ℂ)
      (a := CFC.log A) IsSelfAdjoint.cfc]
  exact cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive A hA

/-- Repository-native finite Loewner inequalities become operator-log
inequalities after adding a strictly positive scalar identity regularization.

This closes the strict-positive regularization dependency for applying
`cstarMatrix_log_le_log` to embedded finite real matrices.  It is still a
deterministic functional-calculus adapter, not trace-MGF domination. -/
theorem finiteComplexCStarMatrix_regularized_log_le_log_of_finiteLoewnerLe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (hN : IsSymmetricFiniteMatrix N)
    (hPSD : finitePSD M) (hLe : finiteLoewnerLe M N)
    {eps : ℝ} (heps : 0 < eps) :
    CFC.log
        (finiteComplexCStarMatrix M + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) ≤
      CFC.log
        (finiteComplexCStarMatrix N + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
  exact cstarMatrix_log_le_log
    (finiteComplexCStarMatrix M + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ))
    (finiteComplexCStarMatrix N + (eps : ℂ) • (1 : CStarMatrix ι ι ℂ))
    (finiteComplexCStarMatrix_add_smul_one_le_of_finiteLoewnerLe
      M N hM hN hLe eps)
    (finiteComplexCStarMatrix_add_pos_smul_one_isStrictlyPositive_of_finitePSD
      M hM hPSD heps)

end NumStability
