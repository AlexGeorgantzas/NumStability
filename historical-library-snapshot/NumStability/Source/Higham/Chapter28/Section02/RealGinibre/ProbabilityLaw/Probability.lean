import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter28 Section02 RealGinibre ProbabilityLaw Probability

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Probability` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory Filter ProbabilityTheory

noncomputable def realEigenvalueCount (n : ℕ) (A : RSqMat n) : ℕ :=
  (Matrix.charpoly A).roots.card

def strictlyPositiveMatrixSet (n : ℕ) : Set (RSqMat n) :=
  {A | ∀ i j, 0 < A i j}

def HasPositiveDominantEigenvalue {n : ℕ} (A : RSqMat n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ (Matrix.charpoly A).IsRoot r ∧
    ∀ z : ℂ, ((Matrix.charpoly A).map Complex.ofRealHom).IsRoot z → ‖z‖ ≤ r

def positiveDominantEigenvalueSet (n : ℕ) : Set (RSqMat n) :=
  {A | HasPositiveDominantEigenvalue A}

/-- The strict-positivity event is genuinely inhabited in every dimension;
the all-ones matrix is a concrete witness. -/
theorem strictlyPositiveMatrixSet_nonempty (n : ℕ) :
    (strictlyPositiveMatrixSet n).Nonempty := by
  refine ⟨fun _ _ => 1, ?_⟩
  simp [strictlyPositiveMatrixSet]

/-- Every positive-dimensional entrywise-positive real matrix has a positive
real eigenvalue that dominates the moduli of all roots of its complexified
characteristic polynomial.  This is the deterministic Perron bridge needed
by the iid-uniform almost-sure statement below. -/
theorem hasPositiveDominantEigenvalue_of_strictlyPositive
    {n : ℕ} (hn : 0 < n) (A : RSqMat n)
    (hA : A ∈ strictlyPositiveMatrixSet n) :
    HasPositiveDominantEigenvalue A := by
  have hIrred : Matrix.IsIrreducible
      (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) :=
    ch7_matrix_isIrreducible_of_pos_entries A hA
  obtain ⟨mu, _z, _x, y, _hz_ne, _hx_ne, _hx_nonneg, hy_pos,
      _heig_complex, _hrad, _hsubx, heig_real⟩ :=
    ch7_exists_spectralRadius_attaining_positive_eigenvector hn A hIrred
  let r : ℝ := ‖mu‖
  have hA_nonneg : ∀ i j : Fin n, 0 ≤ A i j :=
    fun i j => le_of_lt (hA i j)
  have hr_pos : 0 < r :=
    ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector
      hn A r y hA_nonneg hIrred hy_pos heig_real
  have hy_ne : y ≠ 0 := by
    intro hy
    have h0 := congrFun hy ⟨0, hn⟩
    exact (ne_of_gt (hy_pos ⟨0, hn⟩)) h0
  have heig_matrix :
      Matrix.mulVec (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) y = r • y := by
    rw [ch7_matrix_mulVec_eq_matMulVec]
    ext i
    simpa [Pi.smul_apply, smul_eq_mul] using heig_real i
  have hhas : Module.End.HasEigenvalue
      (Matrix.toLin' (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)) r := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hy_ne⟩
    simpa [Matrix.toLin'_apply] using heig_matrix
  have hroot : (Matrix.charpoly A).IsRoot r := by
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hhas
  have hradius : ch7IsComplexEigenvalueRadius A r :=
    ch7_isComplexEigenvalueRadius_of_positive_real_eigenvector
      hn A r y hA_nonneg hy_pos heig_real
  refine ⟨r, hr_pos, hroot, ?_⟩
  intro w hw
  have hcharpoly_complex :
      (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix A).charpoly =
        (Matrix.charpoly A).map Complex.ofRealHom := by
    simpa [realRectToCMatrix, RingHom.mapMatrix_apply] using
      Matrix.charpoly_map (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)
        Complex.ofRealHom
  have hwroot :
      (show Matrix (Fin n) (Fin n) ℂ from
        realRectToCMatrix A).charpoly.IsRoot w := by
    rwa [hcharpoly_complex]
  have hwspec_matrix : w ∈ spectrum ℂ
      (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix A) :=
    Matrix.mem_spectrum_of_isRoot_charpoly hwroot
  have hwspec : w ∈ spectrum ℂ
      (Matrix.toLin'
        (show Matrix (Fin n) (Fin n) ℂ from realRectToCMatrix A)) := by
    rwa [Matrix.spectrum_toLin']
  have hgreatest :=
    ch7_toLin_spectrum_modulusSet_isGreatest_of_isComplexEigenvalueRadius hradius
  exact hgreatest.2 ⟨w, hwspec, rfl⟩

end NumStability
