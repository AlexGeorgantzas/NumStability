import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.InverseRatioChain
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.LowerComparisonChain
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Problem04.ComparisonChains

This module formalizes the source-facing Chapter 13 statements for
`Problem04.ComparisonChains`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    the inverse-ratio source certificate is a specialization of the direct
    lower-comparison source certificate.

    The conversion uses the already-proved tail-history comparison and
    inverse-ratio lower-budget adapter at each Schur-tail step.  This keeps the
    optional inverse-ratio route integrated with the stronger direct
    lower-comparison source-chain API. -/
theorem Higham13Eq1322InverseRatioSourceChain.to_lowerComparisonSourceChain
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
        Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv := by
  intro m
  induction m with
  | zero =>
      intro Ablk pivotInv hcert
      cases hcert with
      | one hdet hNn =>
          exact Higham13Eq1322LowerComparisonSourceChain.one hdet hNn
  | succ m ih =>
      intro Ablk pivotInv hcert
      cases hcert with
      | succ hpivot hdetFlat hsn hNn hInvRatio hTail =>
          have hTailLower :
              Higham13Eq1322LowerComparisonSourceChain hr n m
                (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) :=
            ih hTail
          refine
            Higham13Eq1322LowerComparisonSourceChain.succ
              (hr := hr) (n := n) hpivot hdetFlat hsn hNn ?_ hTailLower
          have hTailPos :=
            maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
              hr Ablk pivotInv hpivot
          have hLower :=
            higham13_eq13_22_tail_lower_budget_le_full_from_inverse_ratio_matrix_stage_history_exact_kappa
              hr Ablk pivotInv hTailPos
              (by
                rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
                  (Nat.succ_pos m) hr]
                exact maxEntryNorm_pos_of_det_ne_zero _ _ hdetFlat)
              n hInvRatio
          simpa using hLower

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    nonterminal active pivot right-inverse data carried by the recursive
    inverse-ratio source certificate.

    This is inherited through the conversion to the direct lower-comparison
    source certificate. -/
theorem Higham13Eq1322InverseRatioSourceChain.nonterminal_pivot_right_inverse
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩)
            (pivotInv k) := by
  intro m Ablk pivotInv hcert
  exact
    Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_right_inverse
      (Higham13Eq1322InverseRatioSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    nonterminal active pivot determinant data carried by the recursive
    inverse-ratio source certificate. -/
theorem Higham13Eq1322InverseRatioSourceChain.nonterminal_pivot_det_ne_zero
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          Matrix.det
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert
  exact
    Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_det_ne_zero
      (Higham13Eq1322InverseRatioSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot right-inverse table for an inverse-ratio source chain,
    once the final one-block pivot is supplied separately. -/
theorem Higham13Eq1322InverseRatioSourceChain.pivot_right_inverse_of_final
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) := by
  intro m Ablk pivotInv hcert hfinal k hk
  by_cases hkm : k < m
  · exact
      Higham13Eq1322InverseRatioSourceChain.nonterminal_pivot_right_inverse
        hcert k hkm
  · have hle : k ≤ m := Nat.lt_succ_iff.mp hk
    have hmk : m ≤ k := Nat.le_of_not_gt hkm
    have hEq : k = m := Nat.le_antisymm hle hmk
    subst k
    simpa using hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for an inverse-ratio source chain,
    once the final one-block pivot determinant is supplied separately. -/
theorem Higham13Eq1322InverseRatioSourceChain.pivot_det_ne_zero_of_final
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hfinal
  exact
    Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final
      (Higham13Eq1322InverseRatioSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for an inverse-ratio source chain when
    the final one-block pivot is supplied as a right-inverse certificate. -/
theorem Higham13Eq1322InverseRatioSourceChain.pivot_det_ne_zero_of_final_right_inverse
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hfinal
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse
      Ablk pivotInv
      (Higham13Eq1322InverseRatioSourceChain.pivot_right_inverse_of_final
        hcert hfinal)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot right-inverse table for an inverse-ratio source chain when the
    terminal one-block pivot is the canonical `nonsingInv`. -/
theorem Higham13Eq1322InverseRatioSourceChain.pivot_right_inverse_of_final_nonsingInv
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) := by
  intro m Ablk pivotInv hcert hdet hfinalEq
  apply Higham13Eq1322InverseRatioSourceChain.pivot_right_inverse_of_final hcert
  simpa [hfinalEq] using
    (isInverse_nonsingInv_of_det_ne_zero r
      (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
        ⟨m, Nat.lt_succ_self m⟩
        ⟨m, Nat.lt_succ_self m⟩) hdet).2

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot determinant table for an inverse-ratio source chain when the
    terminal one-block pivot is the canonical `nonsingInv`.

    This is inherited through the canonical all-pivot right-inverse table. -/
theorem Higham13Eq1322InverseRatioSourceChain.pivot_det_ne_zero_of_final_nonsingInv
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hdet hfinalEq
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse
      Ablk pivotInv
      (Higham13Eq1322InverseRatioSourceChain.pivot_right_inverse_of_final_nonsingInv
        hcert hdet hfinalEq)

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    inverse-ratio source-chain form of the mixed matrix-`∞`/max-entry endpoint.

    The inverse-ratio source certificate specializes to the direct
    lower-comparison certificate, so this wrapper removes that intermediate
    source-chain conversion from callers of the mixed endpoint. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      (hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv) →
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
          2 * blockMaxNorm (Nat.succ_pos m) hr Ablk ∧
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
              pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                (Nat.succ_pos m) (fun i j a b => Ablk i j a b) hPrefix)) ≤
          2 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinal
  exact
    Higham13Eq1322LowerComparisonSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
      (r := r) (n := n) (hr := hr)
      (Higham13Eq1322InverseRatioSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot inverse-ratio source-chain form of the mixed
    matrix-`∞`/max-entry endpoint. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      (hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv) →
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
          2 * blockMaxNorm (Nat.succ_pos m) hr Ablk ∧
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
              pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                (Nat.succ_pos m) (fun i j a b => Ablk i j a b) hPrefix)) ≤
          2 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinalDet
    hFinalEq
  exact
    Higham13Eq1322LowerComparisonSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
      (r := r) (n := n) (hr := hr)
      (Higham13Eq1322InverseRatioSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    inverse-ratio source-chain point-row product witness from the mixed
    matrix-`∞`/max-entry BDD endpoint.

    This packages the mixed endpoint as the `rho <= 2` input to the existing
    inverse-ratio Eq.13.23 witness.  The inverse-ratio comparisons, BDD
    leading-prefix data, and terminal pivot right-inverse remain explicit
    source obligations. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound hPrefix hDomInf hBound hFinal
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322InverseRatioSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2 := by
    have hEndpoint :=
      Higham13Eq1322InverseRatioSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
        (r := r) (n := n) (hr := hr) hcert
        invDiagBound hPrefix hDomInf hBound hFinal
    simpa [hm, hN, A0, G, hApos] using hEndpoint.2
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) (n := n) hr hcert hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    canonical-terminal-pivot form of
    `Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass`. -/
theorem
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_nonsingInv_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq
  let hFinalRight :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) := by
    simpa [hFinalEq] using
      (isInverse_nonsingInv_of_det_ne_zero r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩) hFinalDet).2
  exact
    Higham13Eq1322InverseRatioSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
      (r := r) (n := n) hr hcert
      invDiagBound hPrefix hDomInf hBound hFinalRight

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    recursive source certificate for the stronger base/inverse comparison
    route.

    Each nonterminal Schur-tail step records the explicit comparison pair
    `||A_full||_max <= ||A_tail||_max` and
    `||A_tail^{-1}||_max <= ||A_full^{-1}||_max`.  These comparisons imply
    the inverse-ratio lower-budget condition, hence the existing direct
    lower-comparison source certificate, but they remain visible source
    obligations rather than hidden in an ambient budget chain. -/
inductive Higham13Eq1322BaseInverseSourceChain {r : ℕ} (hr : 0 < r)
    (n : ℕ) :
    (m : ℕ) →
      (Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) →
      (ℕ → Matrix (Fin r) (Fin r) ℝ) → Prop
  | one {Ablk : Fin 1 → Fin 1 → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hdet :
        Matrix.det (blockMatrixFlatFin Ablk :
          Matrix (Fin (1 * r)) (Fin (1 * r)) ℝ) ≠ 0)
      (hNn : (((1 * r : ℕ) : ℝ) ≤ (n : ℝ))) :
      Higham13Eq1322BaseInverseSourceChain hr n 0 Ablk pivotInv
  | succ {m : ℕ}
      {Ablk : Fin ((m + 1) + 1) → Fin ((m + 1) + 1) →
        Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      [Invertible (blockMatrixFirstSplitA11 Ablk)]
      [Invertible (blockMatrixFirstSplitA22 Ablk -
        blockMatrixFirstSplitA21 Ablk * ⅟(blockMatrixFirstSplitA11 Ablk) *
          blockMatrixFirstSplitA12 Ablk)]
      [Invertible (Matrix.fromBlocks
        (blockMatrixFirstSplitA11 Ablk)
        (blockMatrixFirstSplitA12 Ablk)
        (blockMatrixFirstSplitA21 Ablk)
        (blockMatrixFirstSplitA22 Ablk))]
      (hpivot : pivotInv 0 = ⅟(blockMatrixFirstSplitA11 Ablk))
      (hdetFlat :
        Matrix.det (blockMatrixFlatFin Ablk :
          Matrix (Fin (((m + 1) + 1) * r)) (Fin (((m + 1) + 1) * r)) ℝ) ≠ 0)
      (hsn : (((m + 1) * r : ℕ) : ℝ) ≤ (n : ℝ))
      (hNn : ((((m + 1) + 1) * r : ℕ) : ℝ) ≤ (n : ℝ)) :
      (let hmTail : 0 < m + 1 := Nat.succ_pos m
       let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
       let hNSplit : 0 < r + (m + 1) * r :=
        Nat.add_pos_left hr ((m + 1) * r)
       let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
       let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        blockMatrixFirstSplitFlat Ablk
       maxEntryNormRect hNSplit hNSplit ASplit ≤
        maxEntryNormRect hNTail hNTail Atail) →
      (let hmTail : 0 < m + 1 := Nat.succ_pos m
       let hNTail : 0 < (m + 1) * r := Nat.mul_pos hmTail hr
       let hNSplit : 0 < r + (m + 1) * r :=
        Nat.add_pos_left hr ((m + 1) * r)
       let Atail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))
       let AinvTail : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) Atail
       let ASplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        blockMatrixFirstSplitFlat Ablk
       let AinvSplit : Fin (r + (m + 1) * r) → Fin (r + (m + 1) * r) → ℝ :=
        nonsingInv (r + (m + 1) * r) ASplit
       maxEntryNormRect hNTail hNTail AinvTail ≤
        maxEntryNormRect hNSplit hNSplit AinvSplit) →
      Higham13Eq1322BaseInverseSourceChain hr n m
        (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) →
      Higham13Eq1322BaseInverseSourceChain hr n (m + 1) Ablk pivotInv

/-- The base/inverse source-chain certificate carries determinant
    nonsingularity for its current block matrix. -/
theorem Higham13Eq1322BaseInverseSourceChain.det_ne_zero {r n : ℕ}
    {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
        Matrix.det (blockMatrixFlatFin Ablk :
          Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 := by
  intro m Ablk pivotInv hcert
  cases hcert with
  | one hdet _ =>
      simpa using hdet
  | succ _ hdetFlat _ _ _ _ _ =>
      simpa using hdetFlat

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    the base/inverse source certificate specializes to the inverse-ratio
    source certificate.

    Each nonterminal step uses the elementary order bridge
    `maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le`, so the
    source-side base and inverse comparisons remain explicit while downstream
    APIs can consume the already established inverse-ratio chain. -/
theorem Higham13Eq1322BaseInverseSourceChain.to_inverseRatioSourceChain
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
        Higham13Eq1322InverseRatioSourceChain hr n m Ablk pivotInv := by
  intro m
  induction m with
  | zero =>
      intro Ablk pivotInv hcert
      cases hcert with
      | one hdet hNn =>
          exact Higham13Eq1322InverseRatioSourceChain.one hdet hNn
  | succ m ih =>
      intro Ablk pivotInv hcert
      cases hcert with
      | succ hpivot hdetFlat hsn hNn hBase hInv hTail =>
          have hTailRatio :
              Higham13Eq1322InverseRatioSourceChain hr n m
                (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) :=
            ih hTail
          refine
            Higham13Eq1322InverseRatioSourceChain.succ
              (hr := hr) (n := n) hpivot hdetFlat hsn hNn ?_ hTailRatio
          have hInvRatio :=
            maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le
              (Nat.mul_pos (Nat.succ_pos m) hr)
              (Nat.add_pos_left hr ((m + 1) * r))
              (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0)))
              (nonsingInv ((m + 1) * r)
                (blockMatrixFlatFin (blockSchur Ablk (pivotInv 0))))
              (blockMatrixFirstSplitFlat Ablk)
              (nonsingInv (r + (m + 1) * r)
                (blockMatrixFirstSplitFlat Ablk))
              hBase hInv
          simpa using hInvRatio

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    the base/inverse source certificate is a specialization of the direct
    lower-comparison source certificate.

    The conversion uses the already-proved base/inverse lower-budget adapter
    at each Schur-tail step, while keeping the base and inverse comparisons
    as the explicit source-side obligations. -/
theorem Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
        Higham13Eq1322LowerComparisonSourceChain hr n m Ablk pivotInv := by
  intro m
  induction m with
  | zero =>
      intro Ablk pivotInv hcert
      cases hcert with
      | one hdet hNn =>
          exact Higham13Eq1322LowerComparisonSourceChain.one hdet hNn
  | succ m ih =>
      intro Ablk pivotInv hcert
      cases hcert with
      | succ hpivot hdetFlat hsn hNn hBase hInv hTail =>
          have hTailLower :
              Higham13Eq1322LowerComparisonSourceChain hr n m
                (blockSchur Ablk (pivotInv 0)) (fun q => pivotInv (q + 1)) :=
            ih hTail
          refine
            Higham13Eq1322LowerComparisonSourceChain.succ
              (hr := hr) (n := n) hpivot hdetFlat hsn hNn ?_ hTailLower
          have hTailPos :=
            maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
              hr Ablk pivotInv hpivot
          have hLower :=
            higham13_eq13_22_tail_lower_budget_le_full_from_base_inverse_matrix_stage_history_exact_kappa
              hr Ablk pivotInv hTailPos
              (by
                rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
                  (Nat.succ_pos m) hr]
                exact maxEntryNorm_pos_of_det_ne_zero _ _ hdetFlat)
              n hBase hInv
          simpa using hLower

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    nonterminal active pivot right-inverse data carried by the recursive
    base/inverse source certificate. -/
theorem Higham13Eq1322BaseInverseSourceChain.nonterminal_pivot_right_inverse
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩)
            (pivotInv k) := by
  intro m Ablk pivotInv hcert
  exact
    Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_right_inverse
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    nonterminal active pivot determinant data carried by the recursive
    base/inverse source certificate. -/
theorem Higham13Eq1322BaseInverseSourceChain.nonterminal_pivot_det_ne_zero
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
        ∀ k : ℕ, ∀ hk : k < m,
          Matrix.det
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩
              ⟨k, Nat.lt_trans hk (Nat.lt_succ_self m)⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert
  exact
    Higham13Eq1322LowerComparisonSourceChain.nonterminal_pivot_det_ne_zero
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot right-inverse table for a base/inverse source chain,
    once the final one-block pivot is supplied separately. -/
theorem Higham13Eq1322BaseInverseSourceChain.pivot_right_inverse_of_final
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) := by
  intro m Ablk pivotInv hcert hfinal
  exact
    Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for a base/inverse source chain, once
    the final one-block pivot determinant is supplied separately. -/
theorem Higham13Eq1322BaseInverseSourceChain.pivot_det_ne_zero_of_final
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
      Matrix.det
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hfinal
  exact
    Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      hfinal

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    full active pivot determinant table for a base/inverse source chain when
    the final one-block pivot is supplied as a right-inverse certificate. -/
theorem Higham13Eq1322BaseInverseSourceChain.pivot_det_ne_zero_of_final_right_inverse
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hfinal
  exact
    higham13_algorithm13_3_pivot_det_ne_zero_of_pivot_right_inverse
      Ablk pivotInv
      (Higham13Eq1322BaseInverseSourceChain.pivot_right_inverse_of_final
        hcert hfinal)

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot right-inverse table for a base/inverse source chain when the
    terminal one-block pivot is the canonical `nonsingInv`. -/
theorem Higham13Eq1322BaseInverseSourceChain.pivot_right_inverse_of_final_nonsingInv
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) := by
  intro m Ablk pivotInv hcert hdet hfinalEq
  exact
    Higham13Eq1322LowerComparisonSourceChain.pivot_right_inverse_of_final_nonsingInv
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      hdet hfinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    all-pivot determinant table for a base/inverse source chain when the
    terminal one-block pivot is the canonical `nonsingInv`. -/
theorem Higham13Eq1322BaseInverseSourceChain.pivot_det_ne_zero_of_final_nonsingInv
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∀ k : ℕ, ∀ hk : k < m + 1,
        Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩) ≠ 0 := by
  intro m Ablk pivotInv hcert hdet hfinalEq
  exact
    Higham13Eq1322LowerComparisonSourceChain.pivot_det_ne_zero_of_final_nonsingInv
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      hdet hfinalEq

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    base/inverse source-chain form of the mixed matrix-`∞`/max-entry endpoint.

    The stronger source certificate specializes to the direct lower-comparison
    source chain, so callers of this route can use the Eq.13.21/Eq.13.23 mixed
    endpoint without separately materializing that conversion. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      (hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv) →
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
          2 * blockMaxNorm (Nat.succ_pos m) hr Ablk ∧
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
              pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                (Nat.succ_pos m) (fun i j a b => Ablk i j a b) hPrefix)) ≤
          2 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinal
  exact
    Higham13Eq1322LowerComparisonSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
      (r := r) (n := n) (hr := hr)
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      invDiagBound hPrefix hDomInf hBound hFinal

/-- Higham, 2nd ed., Chapter 13, equations (13.21) and (13.23):
    canonical-terminal-pivot base/inverse source-chain form of the mixed
    matrix-`∞`/max-entry endpoint. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
    {r n : ℕ} {hr : 0 < r} :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ},
      (hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv) →
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      blockMaxNorm (Nat.succ_pos m) hr
          (higham13_algorithm13_3_upperFromMatrixStages Ablk pivotInv) ≤
          2 * blockMaxNorm (Nat.succ_pos m) hr Ablk ∧
        growthFactorEntry (Nat.mul_pos (Nat.succ_pos m) hr)
            (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              (Nat.mul_pos (Nat.succ_pos m) hr) (Nat.succ_pos m) hr Ablk
              pivotInv)
            (maxEntryNorm_pos_of_det_ne_zero
              (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin Ablk)
              (higham13_blockMatrixFlatFin_det_ne_zero_of_all_leadingBlockPrefixes
                (Nat.succ_pos m) (fun i j a b => Ablk i j a b) hPrefix)) ≤
          2 := by
  intro m Ablk pivotInv hcert invDiagBound hPrefix hDomInf hBound hFinalDet
    hFinalEq
  exact
    Higham13Eq1322LowerComparisonSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_nonsingInv_mixed_column_mass
      (r := r) (n := n) (hr := hr)
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)
      invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    a recursive base/inverse source certificate instantiates the ambient
    exact-κ budget chain.

    This is the direct budget-chain connector for the stronger source route:
    each recursive step keeps the explicit base and inverse comparisons as the
    source-side mathematical obligations, while downstream Eq.13.22/Eq.13.23
    wrappers can consume the same ambient budget chain as the lower-comparison
    route. -/
theorem Higham13Eq1322BaseInverseSourceChain.to_blockLUBudgetChain
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      let hApos : 0 < maxEntryNorm hN A0 :=
        maxEntryNorm_pos_of_det_ne_zero hN A0
          (Higham13Eq1322BaseInverseSourceChain.det_ne_zero hcert)
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m Ablk pivotInv := by
  intro m Ablk pivotInv hcert
  simpa using
    Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain
      (r := r) (n := n) hr
      (Higham13Eq1322BaseInverseSourceChain.to_lowerComparisonSourceChain
        (r := r) (n := n) hr hcert)

/-- Higham, 2nd ed., Chapter 13, equation (13.22):
    full recursive Eq.13.22 product witness from the base/inverse source
    certificate. -/
theorem Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      let hApos : 0 < maxEntryNorm hN A0 :=
        maxEntryNorm_pos_of_det_ne_zero hN A0
          (Higham13Eq1322BaseInverseSourceChain.det_ne_zero hcert)
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            (n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 3 *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322BaseInverseSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m Ablk pivotInv := by
    simpa [hm, hN, A0, G, Ainv, hApos] using
      Higham13Eq1322BaseInverseSourceChain.to_blockLUBudgetChain
        (r := r) (n := n) hr hcert
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa
      (r := r) hr (hN := hN) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    full recursive point-row product witness from the base/inverse source
    certificate plus the remaining source-side `rho <= 2` theorem. -/
theorem Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      let hApos : 0 < maxEntryNorm hN A0 :=
        maxEntryNorm_pos_of_det_ne_zero hN A0
          (Higham13Eq1322BaseInverseSourceChain.det_ne_zero hcert)
      growthFactorEntry hN A0 G hApos ≤ 2 →
        ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
          BlockLUFactSpec (m + 1) r Ablk L U ∧
            blockMaxNorm (Nat.succ_pos m) hr L *
                blockMaxNorm (Nat.succ_pos m) hr U ≤
              8 * (n : ℝ) *
                (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
                maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro hRho_le_two
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322BaseInverseSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m Ablk pivotInv := by
    simpa [hm, hN, A0, G, Ainv, hApos] using
      Higham13Eq1322BaseInverseSourceChain.to_blockLUBudgetChain
        (r := r) (n := n) hr hcert
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hN) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    base/inverse source-chain point-row product witness from the mixed
    matrix-`∞`/max-entry BDD endpoint.

    This packages the mixed endpoint as the `rho <= 2` input to the existing
    base/inverse Eq.13.23 witness.  The stronger base/inverse source
    comparisons, BDD leading-prefix data, and terminal pivot right-inverse
    remain explicit mathematical obligations. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound hPrefix hDomInf hBound hFinal
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322BaseInverseSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hRho_le_two : growthFactorEntry hN A0 G hApos ≤ 2 := by
    have hEndpoint :=
      Higham13Eq1322BaseInverseSourceChain.upperFromMatrixStages_eq13_21_and_matrixStageHistoryGrowthFactor_le_two_of_final_right_inverse_mixed_column_mass
        (r := r) (n := n) (hr := hr) hcert
        invDiagBound hPrefix hDomInf hBound hFinal
    simpa [hm, hN, A0, G, hApos] using hEndpoint.2
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) (n := n) hr hcert hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    canonical-terminal-pivot form of
    `Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass`. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_nonsingInv_mixed_column_mass
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
        BlockMatrixNonsingular
          (leadingBlockPrefix13_2 (fun i j a b => Ablk i j a b) p hp)) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      Matrix.det
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) ≠ 0 →
      pivotInv m =
        nonsingInv r
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
            ⟨m, Nat.lt_succ_self m⟩
            ⟨m, Nat.lt_succ_self m⟩) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound hPrefix hDomInf hBound hFinalDet hFinalEq
  let hFinalRight :
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩)
        (pivotInv m) := by
    simpa [hFinalEq] using
      (isInverse_nonsingInv_of_det_ne_zero r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv m
          ⟨m, Nat.lt_succ_self m⟩
          ⟨m, Nat.lt_succ_self m⟩) hFinalDet).2
  exact
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_final_right_inverse_mixed_column_mass
      (r := r) (n := n) hr hcert
      invDiagBound hPrefix hDomInf hBound hFinalRight

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    full recursive point-row product witness from the base/inverse source
    certificate, with `rho <= 2` supplied by the matrix-stage
    product-bound/diagonal-update BDD route.

    This is the product/update companion to
    `Higham13Eq1322BaseInverseSourceChain.to_blockLUBudgetChain`: it consumes the
    ambient exact-`κ` budget chain directly, while the source-side base/inverse
    comparisons and BDD product/update data remain explicit obligations. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      (∀ k : ℕ, ∀ hk : k < m + 1,
        maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  let hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0 :=
    Higham13Eq1322BaseInverseSourceChain.det_ne_zero hcert
  let hm : 0 < m + 1 := Nat.succ_pos m
  let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
  let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ := blockMatrixFlatFin Ablk
  let G : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    higham13_algorithm13_3_matrixStageHistoryGrowthMatrix hN hm hr Ablk pivotInv
  let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
    nonsingInv ((m + 1) * r) A0
  let hApos : 0 < maxEntryNorm hN A0 :=
    maxEntryNorm_pos_of_det_ne_zero hN A0 hdet
  have hchain :
      Higham13BlockLUBudgetChain hr
        ((n : ℝ) * (growthFactorEntry hN A0 G hApos) ^ 2 *
          (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv))
        (growthFactorEntry hN A0 G hApos * maxEntryNormRect hN hN A0)
        m Ablk pivotInv := by
    simpa [hm, hN, A0, G, Ainv, hApos] using
      Higham13Eq1322BaseInverseSourceChain.to_blockLUBudgetChain
        (r := r) (n := n) hr hcert
  have hRho_le_two :
      growthFactorEntry hN A0 G hApos ≤ 2 := by
    simpa [hm, hN, A0, G, Ainv, hApos] using
      higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update
        hm hr Ablk pivotInv hApos invDiagBound stageInvDiagBound
        hDom hDiagBound hInitInv hPivotInvBound hProduct hDiagUpdate
  simpa [hm, hN, A0, G, Ainv, hApos] using
    Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa
      (r := r) hr (hN := hN) (A0 := A0) (G := G) (Ainv := Ainv)
      hApos n hchain hRho_le_two

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table form of the base/inverse source-chain point-row product
    witness.

    The base/inverse comparisons, structured product estimate, and diagonal
    update remain explicit source obligations; the active pivot table may now
    be supplied as the reciprocal equality used in the printed proof chain. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j => maxEntryNorm hr (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ maxEntryNorm hr (Ablk j j)) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDom hDiagBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      hDom hDiagBound hInitInv
      (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k))
        hReciprocal)
      hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    matrix-`∞` BDD form of the base/inverse source-chain product/update
    witness.

    This source-norm adapter derives the max-entry BDD premise required by the
    compiled product/update route from the printed matrix-`∞` column BDD
    surface.  The base/inverse comparisons, structured product estimate, and
    diagonal-update table remain explicit source obligations. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_infNorm
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      (∀ k : ℕ, ∀ hk : k < m + 1,
        maxEntryNorm hr (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDomInf hBound hInitInv
    hPivotInvBound hProduct hDiagUpdate
  exact
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr Ablk invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j)))
      hInitInv hPivotInvBound hProduct hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, equation (13.23):
    reciprocal-table/matrix-`∞` BDD form of the base/inverse source-chain
    product/update witness. -/
theorem
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal_infNorm
    {r n : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      {Ablk : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ}
      {pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ}
      (_hcert : Higham13Eq1322BaseInverseSourceChain hr n m Ablk pivotInv),
      let hm : 0 < m + 1 := Nat.succ_pos m
      let hN : 0 < (m + 1) * r := Nat.mul_pos hm hr
      let A0 : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        blockMatrixFlatFin Ablk
      let Ainv : Fin ((m + 1) * r) → Fin ((m + 1) * r) → ℝ :=
        nonsingInv ((m + 1) * r) A0
      (invDiagBound : Fin (m + 1) → ℝ) →
      (stageInvDiagBound : ℕ → Fin (m + 1) → ℝ) →
      IsBlockDiagDomCol (m + 1)
        (fun i j : Fin (m + 1) => infNorm (Ablk i j)) invDiagBound →
      (∀ j : Fin (m + 1), invDiagBound j ≤ 0) →
      (∀ j : Fin (m + 1), stageInvDiagBound 0 j = invDiagBound j) →
      SchurStageActivePivotInvReciprocal13_7
        stageInvDiagBound (fun k => maxEntryNorm hr (pivotInv k)) →
      (∀ k : ℕ, ∀ hk : k < m + 1, ∀ i j : Fin (m + 1),
        k + 1 ≤ i.val → k + 1 ≤ j.val →
          maxEntryNorm hr
            (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
              ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j) ≤
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i
                ⟨k, hk⟩) *
            maxEntryNorm hr (pivotInv k) *
            maxEntryNorm hr
              (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
                ⟨k, hk⟩ j)) →
      SchurStageActiveDiagLowerUpdate13_7
        (fun k i j => maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k i j))
        stageInvDiagBound
        (fun k => maxEntryNorm hr (pivotInv k)) →
      ∃ L U : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ,
        BlockLUFactSpec (m + 1) r Ablk L U ∧
          blockMaxNorm (Nat.succ_pos m) hr L *
              blockMaxNorm (Nat.succ_pos m) hr U ≤
            8 * (n : ℝ) *
              (maxEntryNormRect hN hN A0 * maxEntryNormRect hN hN Ainv) *
              maxEntryNormRect hN hN A0 := by
  intro m Ablk pivotInv hcert
  dsimp only
  intro invDiagBound stageInvDiagBound hDomInf hBound hInitInv
    hReciprocal hProduct hDiagUpdate
  exact
    Higham13Eq1322BaseInverseSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa_of_product_bound_diag_update_reciprocal
      (r := r) (n := n) hr hcert invDiagBound stageInvDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr Ablk invDiagBound hDomInf)
      (fun j => le_trans (hBound j) (maxEntryNorm_nonneg hr (Ablk j j)))
      hInitInv hReciprocal hProduct hDiagUpdate

end NumStability
