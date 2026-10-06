import Batteries.Data.Array.Scan
import Mathlib.Data.Vector.Basic
import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.FactorizationAndNorm
import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.TridiagonalInverseRuns

/-!
# ArrayExecution

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.LU.Higham15Problem15_6Operational`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# Higham15Problem15_6Operational (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.LU.Higham15Problem15_6Operational`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

namespace Higham15Problem15_6

open NumStability

theorem problem15_6_absInvMulOperational_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) :
    ∀ i : Fin n, problem15_6_absInvMulOperational T d i =
      ∑ j : Fin n, |A_inv i j| * d j := by
  rw [problem15_6_absInvMulOperational_eq]
  exact absInvMul_correct hn T A_inv hIrred hRight d

theorem problem15_6_infNormOperational_correct {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) :
    problem15_6_infNormOperational T d =
      infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) := by
  unfold problem15_6_infNormOperational
  apply congrArg infNormVec
  funext i
  exact problem15_6_absInvMulOperational_correct
    hn T A_inv hIrred hRight d i

theorem H15_Problem15_6_operational_of_irreducible_rightInverse
    {n : ℕ} (hn : 0 < n)
    (T : TridiagData n) (A_inv : Fin n → Fin n → ℝ)
    (hIrred : IsIrreducibleTridiag T)
    (hRight : IsRightInverse n (tridiag_to_matrix T) A_inv)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∀ i : Fin n,
      (problem15_6_operationalRun T d).factors.x.get i =
        A_inv i ⟨n - 1, by omega⟩ / A_inv ⟨0, hn⟩ ⟨n - 1, by omega⟩) ∧
    (∀ j : Fin n,
      (problem15_6_operationalRun T d).factors.y.get j =
        A_inv ⟨0, hn⟩ j) ∧
    (∀ i : Fin n, problem15_6_absInvMulOperational T d i =
      ∑ j : Fin n, |A_inv i j| * d j) ∧
    (∀ i : Fin n, 0 ≤ problem15_6_absInvMulOperational T d i) ∧
    problem15_6_infNormOperational T d =
      infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) ∧
    (2 ≤ n →
      (problem15_6_operationalRun T d).scalarOps = 29 * n - 26) ∧
    (problem15_6_operationalRun T d).scalarOps ≤ 29 * n := by
  have hx := x_correct hn T A_inv hIrred hRight
  have hy := y_correct hn T A_inv hIrred hRight
  have hz := problem15_6_absInvMulOperational_correct
    hn T A_inv hIrred hRight d
  have hznn : ∀ i : Fin n,
      0 ≤ problem15_6_absInvMulOperational T d i := by
    intro i
    rw [hz i]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hd j))
  refine ⟨?_, ?_, hz, hznn,
    problem15_6_infNormOperational_correct hn T A_inv hIrred hRight d,
    ?_, problem15_6_operationalRun_scalarOps_linear T d⟩
  · intro i
    simpa using hx i
  · intro j
    simpa using hy j
  · intro hn2
    exact problem15_6_operationalRun_scalarOps_exact T d hn2

end Higham15Problem15_6
end NumStability

end
