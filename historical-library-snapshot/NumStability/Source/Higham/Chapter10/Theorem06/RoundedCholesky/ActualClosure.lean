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
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
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
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic

/-!
# Chapter10 Theorem06 RoundedCholesky ActualClosure

Canonical destination for material split out of
`NumStability.Algorithms.Ch10ActualSourceClosure` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- The source diagonal scaling `H = D⁻¹ A D⁻¹`, with
`D = diag(sqrt (aᵢᵢ))`. -/
noncomputable def higham10SourceScaledMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j / (Real.sqrt (A i i) * Real.sqrt (A j j))

/-- The literal spectral condition number used in Theorem 10.6. -/
noncomputable def higham10SourceKappa2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  let H := higham10SourceScaledMatrix A
  opNorm2 H * opNorm2 (nonsingInv n H)

theorem higham10SourceScaledMatrix_isSymPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    IsSymPosDef n (higham10SourceScaledMatrix A) := by
  let dInv : Fin n → ℝ := fun i => (Real.sqrt (A i i))⁻¹
  have hdInv : ∀ i : Fin n, 0 < dInv i := by
    intro i
    exact inv_pos.mpr (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD i))
  have hcong := isSymPosDef_diagCongr n dInv A hdInv hSPD
  have heq : (fun i j => dInv i * A i j * dInv j) =
      higham10SourceScaledMatrix A := by
    funext i j
    have hi : Real.sqrt (A i i) ≠ 0 :=
      (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD i)).ne'
    have hj : Real.sqrt (A j j) ≠ 0 :=
      (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD j)).ne'
    simp only [dInv, higham10SourceScaledMatrix]
    field_simp [hi, hj]
  rwa [heq] at hcong

theorem higham10SourceScaledMatrix_diag {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) (i : Fin n) :
    higham10SourceScaledMatrix A i i = 1 := by
  have hs : Real.sqrt (A i i) ≠ 0 :=
    (Real.sqrt_pos.mpr (higham10_spd_diag_pos A hSPD i)).ne'
  have hsquare : Real.sqrt (A i i) * Real.sqrt (A i i) = A i i := by
    nlinarith [Real.sq_sqrt (le_of_lt (higham10_spd_diag_pos A hSPD i))]
  rw [higham10SourceScaledMatrix, hsquare]
  exact div_self (ne_of_gt (higham10_spd_diag_pos A hSPD i))

/-- The canonical inverse of the scaled SPD matrix acts as a left inverse on
vectors. -/
theorem higham10SourceScaledMatrix_nonsingInv_action {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A)
    (v : Fin n → ℝ) :
    matMulVec n (nonsingInv n (higham10SourceScaledMatrix A))
        (matMulVec n (higham10SourceScaledMatrix A) v) = v := by
  let H := higham10SourceScaledMatrix A
  have hHspd : IsSymPosDef n H := by
    simpa [H] using higham10SourceScaledMatrix_isSymPosDef A hSPD
  have hleft : IsLeftInverse n H (nonsingInv n H) :=
    (isInverse_nonsingInv_of_det_ne_zero n H
      (isSymPosDef_det_ne_zero H hHspd)).1
  have hmat : matMul n (nonsingInv n H) H = idMatrix n := by
    funext i j
    exact hleft i j
  have haction :
      matMulVec n (nonsingInv n H) (matMulVec n H v) = v := by
    funext i
    rw [← matMulVec_matMul n (nonsingInv n H) H v i, hmat]
    exact congrFun (matMulVec_id n v) i
  simpa [H] using haction

/-- The inverse operator norm is bounded by the literal condition number.
The positive dimension assumption supplies a unit diagonal entry of the scaled
matrix, hence `1 ≤ ‖H‖₂`. -/
theorem higham10SourceScaledMatrix_inverse_opNorm2Le_kappa2 {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    opNorm2Le (nonsingInv n (higham10SourceScaledMatrix A))
      (higham10SourceKappa2 A) := by
  let H := higham10SourceScaledMatrix A
  let Hinv := nonsingInv n H
  let i0 : Fin n := ⟨0, hn⟩
  have hH1 : 1 ≤ opNorm2 H := by
    have hdiag := diag_le_opNorm2Le H (opNorm2 H) (opNorm2Le_opNorm2 H) i0
    simpa [H, i0, higham10SourceScaledMatrix_diag A hSPD i0] using hdiag
  have hInv0 : 0 ≤ opNorm2 Hinv := opNorm2_nonneg Hinv
  have hnorm : opNorm2 Hinv ≤ opNorm2 H * opNorm2 Hinv := by
    nlinarith
  intro v
  calc
    vecNorm2 (matMulVec n Hinv v)
        ≤ opNorm2 Hinv * vecNorm2 v := opNorm2Le_opNorm2 Hinv v
    _ ≤ (opNorm2 H * opNorm2 Hinv) * vecNorm2 v :=
      mul_le_mul_of_nonneg_right hnorm (vecNorm2_nonneg v)
    _ = higham10SourceKappa2 A * vecNorm2 v := by
      simp [higham10SourceKappa2, H, Hinv]

end NumStability
