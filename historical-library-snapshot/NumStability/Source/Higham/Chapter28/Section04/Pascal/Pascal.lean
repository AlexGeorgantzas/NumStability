import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Pascal.Basic

/-!
# Chapter28 Section04 Pascal Pascal

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Pascal` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Polynomial

/-- The clockwise rotation of Higham's signed Pascal involution, before the
parity correction used by `pascal(n,2)`. -/
noncomputable def rotatedSignedPascal (n : ℕ) : RSqMat n :=
  fun i j => signedPascal n (Fin.rev j) i

@[simp]
theorem rotatedSignedPascal_apply {n : ℕ} (i j : Fin n) :
    rotatedSignedPascal n i j =
      (-1 : ℝ) ^ i.val * Nat.choose (n - 1 - j.val) i.val := by
  simp only [rotatedSignedPascal, signedPascal, Fin.rev]
  have hsub : n - (j.val + 1) = n - 1 - j.val := by omega
  rw [hsub]

/-- Higham, 2nd ed., Section 28.4, pp. 520-521: `pascal(n,2)` is obtained by
rotating the signed Pascal involution clockwise and multiplying by `-1` when
`n` is even.  The parity factor `(-1)^(n+1)` expresses exactly that rule. -/
noncomputable def pascalIdentityCubeRootCandidate (n : ℕ) : RSqMat n :=
  fun i j => (-1 : ℝ) ^ (n + 1) * signedPascal n (Fin.rev j) i

/-- Closed entry formula for the rotated signed-Pascal candidate. -/
@[simp]
theorem pascalIdentityCubeRootCandidate_apply
    {n : ℕ} (i j : Fin n) :
    pascalIdentityCubeRootCandidate n i j =
      (-1 : ℝ) ^ (n + 1 + i.val) *
        Nat.choose (n - 1 - j.val) i.val := by
  simp only [pascalIdentityCubeRootCandidate, signedPascal, Fin.rev]
  have hsub : n - (j.val + 1) = n - 1 - j.val := by omega
  rw [hsub, pow_add]
  ring

theorem pascalIdentityCubeRootCandidate_eq_smul (n : ℕ) :
    pascalIdentityCubeRootCandidate n =
      (-1 : ℝ) ^ (n + 1) • rotatedSignedPascal n := by
  ext i j
  rfl

end NumStability
