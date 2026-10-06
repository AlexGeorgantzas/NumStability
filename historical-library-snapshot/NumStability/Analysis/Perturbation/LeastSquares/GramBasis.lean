import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.GramBasis
import NumStability.Analysis.SingularValues.RectangularGram
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# GramBasis

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    source-dimension branch handoff specialized to the existing real
    right-Gram SVD basis.  The theorem now constructs the singular-vector
    branches `u` and `v` from `A` itself; the remaining source obligation is
    the orthonormal left-nullspace branch `w` for the `m-n` zero-left
    directions. -/
theorem
    lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_branch_data
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n ≤ m)
    {alpha : ℝ} {A : Fin m → Fin n → ℝ}
    {w : Fin (m - n) → Fin m → ℝ}
    (hpos : ∀ i : Fin n, 0 < rectRightGramBasisSingularValue A i)
    (hw : ∀ k : Fin (m - n), vecNorm2Sq (w k) = 1)
    (hnull : ∀ k l : Fin (m - n),
      k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hATw : ∀ k : Fin (m - n), ∀ j : Fin n,
      ∑ r : Fin m, A r j * w k r = 0)
    (halpha :
      alpha = lsScaledAugmentedBranchSigmaMin
        (rectRightGramBasisSingularValue A) / Real.sqrt 2) :
    Real.sqrt 2 *
          (lsScaledAugmentedBranchSigmaMax (rectRightGramBasisSingularValue A) /
            lsScaledAugmentedBranchSigmaMin (rectRightGramBasisSingularValue A)) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
            (rectRightGramBasisSingularValue A)
            (fun a r => rectRightGramLeftSingularFromEigenbasis A r a)
            (fun a j => rectRightGramEigenbasis A j a) w) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
            (rectRightGramBasisSingularValue A)
            (fun a r => rectRightGramLeftSingularFromEigenbasis A r a)
            (fun a j => rectRightGramEigenbasis A j a) w) ≤
        2 *
          (lsScaledAugmentedBranchSigmaMax (rectRightGramBasisSingularValue A) /
            lsScaledAugmentedBranchSigmaMin (rectRightGramBasisSingularValue A)) := by
  have hu : ∀ a : Fin n,
      vecNorm2Sq (fun r : Fin m =>
        rectRightGramLeftSingularFromEigenbasis A r a) = 1 := by
    intro a
    have h :=
      rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
        A hpos a a
    simpa [vecNorm2Sq, idMatrix, pow_two] using h
  have hv : ∀ a : Fin n,
      vecNorm2Sq (fun j : Fin n => rectRightGramEigenbasis A j a) = 1 := by
    intro a
    have h := rectRightGramEigenbasis_col_orthonormal A a a
    simpa [vecNorm2Sq, idMatrix, pow_two] using h
  have hleft : ∀ a b : Fin n, a ≠ b →
      (∑ r : Fin m,
        rectRightGramLeftSingularFromEigenbasis A r a *
          rectRightGramLeftSingularFromEigenbasis A r b) = 0 := by
    intro a b hab
    have h :=
      rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
        A hpos a b
    simpa [idMatrix, hab] using h
  have hright : ∀ a b : Fin n, a ≠ b →
      (∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          rectRightGramEigenbasis A j b) = 0 := by
    intro a b hab
    have h := rectRightGramEigenbasis_col_orthonormal A a b
    simpa [idMatrix, hab] using h
  have hAv : ∀ a : Fin n,
      rectMatMulVec A (fun j : Fin n => rectRightGramEigenbasis A j a) =
        fun r : Fin m =>
          rectRightGramBasisSingularValue A a *
            rectRightGramLeftSingularFromEigenbasis A r a := by
    intro a
    ext r
    have hf :=
      rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos
        A hpos r a
    simpa [rectMatMulVec, rectRightGramProjectedColumn] using hf.symm
  have hATu : ∀ a : Fin n,
      (fun j : Fin n => ∑ r : Fin m,
        A r j * rectRightGramLeftSingularFromEigenbasis A r a) =
          fun j =>
            rectRightGramBasisSingularValue A a *
              rectRightGramEigenbasis A j a :=
    rectRightGramLeftSingularFromEigenbasis_transpose_action_of_pos A hpos
  exact
    lsScaledAugmentedMatrix_kappa2_bounds_of_source_dimension_branch_data
      (m := m) (n := n) (hmn := hmn)
      (alpha := alpha) (A := A)
      (sigma := rectRightGramBasisSingularValue A)
      (u := fun a r => rectRightGramLeftSingularFromEigenbasis A r a)
      (v := fun a j => rectRightGramEigenbasis A j a)
      (w := w)
      hu hv hw hleft hright hnull hAv hATu hATw hpos halpha
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    injective-column-map version of the real right-Gram branch handoff.  Full
    column rank now supplies positivity of the basis-indexed singular branches;
    the remaining supplied data are only the orthonormal left-nullspace branch
    vectors and their transpose-null equations. -/
theorem
    lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_branch_data_of_rectMatMulVec_injective
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n ≤ m)
    {alpha : ℝ} {A : Fin m → Fin n → ℝ}
    {w : Fin (m - n) → Fin m → ℝ}
    (hinj : Function.Injective (rectMatMulVec A))
    (hw : ∀ k : Fin (m - n), vecNorm2Sq (w k) = 1)
    (hnull : ∀ k l : Fin (m - n),
      k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hATw : ∀ k : Fin (m - n), ∀ j : Fin n,
      ∑ r : Fin m, A r j * w k r = 0)
    (halpha :
      alpha = lsScaledAugmentedBranchSigmaMin
        (rectRightGramBasisSingularValue A) / Real.sqrt 2) :
    Real.sqrt 2 *
          (lsScaledAugmentedBranchSigmaMax (rectRightGramBasisSingularValue A) /
            lsScaledAugmentedBranchSigmaMin (rectRightGramBasisSingularValue A)) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
            (rectRightGramBasisSingularValue A)
            (fun a r => rectRightGramLeftSingularFromEigenbasis A r a)
            (fun a j => rectRightGramEigenbasis A j a) w) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
            (rectRightGramBasisSingularValue A)
            (fun a r => rectRightGramLeftSingularFromEigenbasis A r a)
            (fun a j => rectRightGramEigenbasis A j a) w) ≤
        2 *
          (lsScaledAugmentedBranchSigmaMax (rectRightGramBasisSingularValue A) /
            lsScaledAugmentedBranchSigmaMin (rectRightGramBasisSingularValue A)) := by
  exact
    lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_branch_data
      (m := m) (n := n) (hmn := hmn)
      (alpha := alpha) (A := A) (w := w)
      (fun i => rectRightGramBasisSingularValue_pos_of_rectMatMulVec_injective
        (A := A) hinj i)
      hw hnull hATw halpha
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    existential right-Gram condition-number handoff.  Under the source tall
    dimension condition and real full-column-rank injectivity, the theorem
    constructs the left-nullspace branch family and returns the balanced
    two-sided `kappa2` certificate for the corresponding reciprocal-diagonal
    inverse candidate. -/
theorem
    exists_lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_of_rectMatMulVec_injective
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n ≤ m)
    {alpha : ℝ} {A : Fin m → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec A))
    (halpha :
      alpha = lsScaledAugmentedBranchSigmaMin
        (rectRightGramBasisSingularValue A) / Real.sqrt 2) :
    ∃ w : Fin (m - n) → Fin m → ℝ,
      (∀ k : Fin (m - n), vecNorm2Sq (w k) = 1) ∧
        (∀ k l : Fin (m - n),
          k ≠ l → (∑ r : Fin m, w k r * w l r) = 0) ∧
        (∀ k : Fin (m - n), ∀ j : Fin n,
          ∑ r : Fin m, A r j * w k r = 0) ∧
        Real.sqrt 2 *
            (lsScaledAugmentedBranchSigmaMax (rectRightGramBasisSingularValue A) /
              lsScaledAugmentedBranchSigmaMin (rectRightGramBasisSingularValue A)) ≤
          kappa2 (lsScaledAugmentedMatrix alpha A)
            (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
              (rectRightGramBasisSingularValue A)
              (fun a r => rectRightGramLeftSingularFromEigenbasis A r a)
              (fun a j => rectRightGramEigenbasis A j a) w) ∧
        kappa2 (lsScaledAugmentedMatrix alpha A)
            (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
              (rectRightGramBasisSingularValue A)
              (fun a r => rectRightGramLeftSingularFromEigenbasis A r a)
              (fun a j => rectRightGramEigenbasis A j a) w) ≤
          2 *
            (lsScaledAugmentedBranchSigmaMax (rectRightGramBasisSingularValue A) /
              lsScaledAugmentedBranchSigmaMin (rectRightGramBasisSingularValue A)) := by
  obtain ⟨w, hw, hnull, hATw⟩ :=
    exists_rightGram_leftNull_branch_data_of_rectMatMulVec_injective
      (m := m) (n := n) hmn (A := A) hinj
  have hbounds :=
    lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_branch_data_of_rectMatMulVec_injective
      (m := m) (n := n) (hmn := hmn)
      (alpha := alpha) (A := A) (w := w)
      hinj hw hnull hATw halpha
  exact ⟨w, hw, hnull, hATw, hbounds⟩

end NumStability
