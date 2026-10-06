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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Equation18
import NumStability.Source.Higham.Chapter13.Equation19
import NumStability.Source.Higham.Chapter13.Section01.NormConventions
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence

/-!
# Source.Higham.Chapter13.Section03.SchurStageAnalysis

This module formalizes the source-facing Chapter 13 statements for
`Section03.SchurStageAnalysis`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- The column-sum invariant used in Higham's Theorem 13.8 proof.
    `stageNorm k i j` abstracts `‖Aᵢⱼ^(k)‖`, while `blockNorm` is the original
    block-norm table.  The source obtains this invariant by induction using
    Theorem 13.7; this predicate exposes it as the remaining stage-sequence
    obligation. -/
def SchurStageColumnBound13_8 {m : ℕ}
    (stageNorm : Fin m → Fin m → Fin m → ℝ)
    (blockNorm : Fin m → Fin m → ℝ) : Prop :=
  ∀ k j : Fin m, ∑ i : Fin m, stageNorm k i j ≤ ∑ i : Fin m, blockNorm i j

/-- The active block indices in the source statement of Theorem 13.8:
    at stage `k`, the remaining Schur-stage blocks satisfy `k ≤ i`.
    The source uses one-based indices; this zero-based version uses
    `i.val ≥ k`. -/
noncomputable def activeBlockIndices13_8 (m k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i : Fin m => k ≤ i.val)

lemma activeBlockIndices13_8_zero (m : ℕ) :
    activeBlockIndices13_8 m 0 = Finset.univ := by
  ext i
  simp [activeBlockIndices13_8]

/-- Active column block diagonal dominance for the Schur-stage sequence in
    Higham's Theorem 13.7.  At stage `k`, only blocks with global indices
    `k ≤ i,j` remain in the Schur complement. -/
def SchurStageActiveColumnDom13_7 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ) : Prop :=
  ∀ k : ℕ, ∀ j : Fin m, k ≤ j.val →
    ∑ i ∈ activeBlockIndices13_8 m k,
        (if i = j then 0 else stageNorm k i j) ≤ stageInvDiagBound k j

/-- One-step active column-dominance inheritance for Theorem 13.7.
    This is the precise induction step supplied by the one-step Schur-complement
    analysis; it is intentionally weaker than assuming the full staged theorem. -/
def SchurStageActiveColumnDomStep13_7 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ) : Prop :=
  ∀ k : ℕ,
    (∀ j : Fin m, k ≤ j.val →
      ∑ i ∈ activeBlockIndices13_8 m k,
          (if i = j then 0 else stageNorm k i j) ≤ stageInvDiagBound k j) →
    ∀ j : Fin m, k + 1 ≤ j.val →
      ∑ i ∈ activeBlockIndices13_8 m (k + 1),
          (if i = j then 0 else stageNorm (k + 1) i j) ≤
        stageInvDiagBound (k + 1) j

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    active-stage column block diagonal dominance follows by induction from
    initial column block diagonal dominance and the one-step active Schur
    inheritance rule.  The remaining source obligation is to instantiate the
    one-step rule from the actual Schur-complement construction and
    nonsingularity argument. -/
theorem higham13_theorem13_7_active_column_dominance_of_steps {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStep : SchurStageActiveColumnDomStep13_7 stageNorm stageInvDiagBound) :
    SchurStageActiveColumnDom13_7 stageNorm stageInvDiagBound := by
  intro k
  induction k with
  | zero =>
      intro j _hj
      calc
        ∑ i ∈ activeBlockIndices13_8 m 0,
            (if i = j then 0 else stageNorm 0 i j)
            = ∑ i : Fin m, (if i = j then 0 else blockNorm i j) := by
                rw [activeBlockIndices13_8_zero]
                apply Finset.sum_congr rfl
                intro i _hi
                split_ifs <;> simp [hInitNorm i j]
        _ ≤ invDiagBound j := hDom j
        _ = stageInvDiagBound 0 j := by rw [hInitInv j]
  | succ k ih =>
      intro j hj
      exact hStep k ih j hj

/-- Active row block diagonal dominance for the Schur-stage sequence in
    Higham's Theorem 13.7, using the same active global index set as the column
    version. -/
def SchurStageActiveRowDom13_7 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ) : Prop :=
  ∀ k : ℕ, ∀ i : Fin m, k ≤ i.val →
    ∑ j ∈ activeBlockIndices13_8 m k,
        (if i = j then 0 else stageNorm k i j) ≤ stageInvDiagBound k i

/-- One-step active row-dominance inheritance for Theorem 13.7. -/
def SchurStageActiveRowDomStep13_7 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ) : Prop :=
  ∀ k : ℕ,
    (∀ i : Fin m, k ≤ i.val →
      ∑ j ∈ activeBlockIndices13_8 m k,
          (if i = j then 0 else stageNorm k i j) ≤ stageInvDiagBound k i) →
    ∀ i : Fin m, k + 1 ≤ i.val →
      ∑ j ∈ activeBlockIndices13_8 m (k + 1),
          (if i = j then 0 else stageNorm (k + 1) i j) ≤
        stageInvDiagBound (k + 1) i

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    row block diagonal dominance propagates through active Schur stages by the
    same induction pattern as the column case.  The one-step row inheritance
    premise is the separate Schur-complement obligation. -/
theorem higham13_theorem13_7_active_row_dominance_of_steps {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomRow m blockNorm invDiagBound)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ i : Fin m, stageInvDiagBound 0 i = invDiagBound i)
    (hStep : SchurStageActiveRowDomStep13_7 stageNorm stageInvDiagBound) :
    SchurStageActiveRowDom13_7 stageNorm stageInvDiagBound := by
  intro k
  induction k with
  | zero =>
      intro i _hi
      calc
        ∑ j ∈ activeBlockIndices13_8 m 0,
            (if i = j then 0 else stageNorm 0 i j)
            = ∑ j : Fin m, (if i = j then 0 else blockNorm i j) := by
                rw [activeBlockIndices13_8_zero]
                apply Finset.sum_congr rfl
                intro j _hj
                split_ifs <;> simp [hInitNorm i j]
        _ ≤ invDiagBound i := hDom i
        _ = stageInvDiagBound 0 i := by rw [hInitInv i]

  | succ k ih =>
      intro i hi
      exact hStep k ih i hi

/-- The one-step active-column inequality used in Higham's Theorem 13.8 proof:
    the active column sum after one Schur step is bounded by the previous active
    column sum.  This is the induction input supplied by Theorem 13.7 and the
    one-step estimate in the source proof. -/
def SchurStageActiveColumnStep13_8 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ) : Prop :=
  ∀ k : ℕ, ∀ j : Fin m,
    ∑ i ∈ activeBlockIndices13_8 m (k + 1), stageNorm (k + 1) i j ≤
      ∑ i ∈ activeBlockIndices13_8 m k, stageNorm k i j

/-- Source-shaped active-column invariant in Higham's Theorem 13.8 proof:
    `∑_{i=k}^m ‖Aᵢⱼ^(k)‖ ≤ ∑_{i=1}^m ‖Aᵢⱼ‖`, written with zero-based stage
    indices and the active index set `activeBlockIndices13_8`. -/
def SchurStageActiveColumnBound13_8 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (blockNorm : Fin m → Fin m → ℝ) : Prop :=
  ∀ k : ℕ, ∀ j : Fin m,
    ∑ i ∈ activeBlockIndices13_8 m k, stageNorm k i j ≤
      ∑ i : Fin m, blockNorm i j

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8 proof:
    the active-column bound follows by induction from the one-step Schur-stage
    column-sum inequality and the initial stage `A^(1) = A`.

    This proves the induction layer of the source proof.  The separate source
    obligation is to instantiate `SchurStageActiveColumnStep13_8` from the actual
    Algorithm 13.3 Schur-complement stage relation and Theorem 13.7. -/
theorem higham13_theorem13_8_active_column_bound_of_steps {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (blockNorm : Fin m → Fin m → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStep : SchurStageActiveColumnStep13_8 stageNorm) :
    SchurStageActiveColumnBound13_8 stageNorm blockNorm := by
  intro k
  induction k with
  | zero =>
      intro j
      calc
        ∑ i ∈ activeBlockIndices13_8 m 0, stageNorm 0 i j
            = ∑ i : Fin m, blockNorm i j := by
                rw [activeBlockIndices13_8_zero]
                exact Finset.sum_congr rfl (fun i _ => hInit i j)
        _ ≤ ∑ i : Fin m, blockNorm i j := le_rfl
  | succ k ih =>
      intro j
      exact le_trans (hStep k j) (ih j)

/-- **Theorem 13.8, active-stage max-bound wrapper**.
    This is the source-shaped final step after the active-column induction:
    for active blocks `k ≤ i,j`, each stage block is bounded by
    `2 * max ‖Aᵢⱼ‖`.  The theorem keeps the active-stage column invariant
    explicit rather than assuming the full Theorem 13.8 conclusion. -/
theorem higham13_theorem13_8_active_stage_block_bound {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hStageColumn : SchurStageActiveColumnBound13_8 stageNorm blockNorm)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (_hjk : k ≤ j.val) :
    stageNorm k i j ≤ 2 * normMax := by
  have hi_mem : i ∈ activeBlockIndices13_8 m k := by
    simp [activeBlockIndices13_8, hik]
  have hsingle :
      stageNorm k i j ≤
        ∑ i' ∈ activeBlockIndices13_8 m k, stageNorm k i' j :=
    Finset.single_le_sum (fun i' _ => hStageNonneg k i' j) hi_mem
  have hstage :
      ∑ i' ∈ activeBlockIndices13_8 m k, stageNorm k i' j ≤
        ∑ i' : Fin m, blockNorm i' j :=
    hStageColumn k j
  have hcol : ∑ i' : Fin m, blockNorm i' j ≤ 2 * normMax :=
    col_sum_le_twice_diag blockNorm invDiagBound hDom hDiagBound normMax hMax j
  exact le_trans hsingle (le_trans hstage hcol)

/-- **Theorem 13.8, active-stage bound from step inequalities**.
    This combines the source-shaped active-column induction with the final
    block diagonal-dominance max-bound step: from the initial stage
    `A^(0) = A` and the one-step active-column Schur inequalities, every active
    stage block satisfies the displayed `2 * max ‖Aᵢⱼ‖` bound.

    The remaining source obligation is still explicit in `hStep`: this wrapper
    does not construct the Algorithm 13.3 Schur-stage sequence or prove the
    one-step inequality from Theorem 13.7. -/
theorem higham13_theorem13_8_active_stage_block_bound_of_steps {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStep : SchurStageActiveColumnStep13_8 stageNorm)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    stageNorm k i j ≤ 2 * normMax := by
  exact higham13_theorem13_8_active_stage_block_bound
    blockNorm invDiagBound hDom hDiagBound stageNorm hStageNonneg
    (higham13_theorem13_8_active_column_bound_of_steps
      stageNorm blockNorm hInit hStep)
    normMax hMax k i j hik hjk

lemma activeBlockIndices13_8_succ_insert {m k : ℕ} (hk : k < m) :
    activeBlockIndices13_8 m k =
      insert ⟨k, hk⟩ (activeBlockIndices13_8 m (k + 1)) := by
  ext i
  simp [activeBlockIndices13_8]
  constructor
  · intro hki
    rcases lt_or_eq_of_le hki with hlt | heq
    · exact Or.inr (Nat.succ_le_of_lt hlt)
    · exact Or.inl (Fin.ext heq.symm)
  · rintro (rfl | hsucc)
    · exact le_rfl
    · exact Nat.le_of_succ_le hsucc

lemma activeBlockIndices13_8_succ_not_mem {m k : ℕ} (hk : k < m) :
    (⟨k, hk⟩ : Fin m) ∉ activeBlockIndices13_8 m (k + 1) := by
  simp [activeBlockIndices13_8]

/-- Source-faithful one-step active-column inequality for Higham's Theorem
    13.8.  The printed proof only needs columns still present in the next
    active Schur stage, so this predicate requires the step inequality under
    `k + 1 ≤ j`. -/
def SchurStageActiveColumnStepOnActive13_8 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ) : Prop :=
  ∀ k : ℕ, ∀ j : Fin m, k + 1 ≤ j.val →
    ∑ i ∈ activeBlockIndices13_8 m (k + 1), stageNorm (k + 1) i j ≤
      ∑ i ∈ activeBlockIndices13_8 m k, stageNorm k i j

/-- Source-faithful active-column invariant for Higham's Theorem 13.8:
    the active column sum is compared with the original column only for columns
    still in the active Schur stage. -/
def SchurStageActiveColumnBoundOnActive13_8 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (blockNorm : Fin m → Fin m → ℝ) : Prop :=
  ∀ k : ℕ, ∀ j : Fin m, k ≤ j.val →
    ∑ i ∈ activeBlockIndices13_8 m k, stageNorm k i j ≤
      ∑ i : Fin m, blockNorm i j

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8 proof:
    active-column induction using only the source-relevant active columns. -/
theorem higham13_theorem13_8_active_column_bound_on_active_of_steps {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (blockNorm : Fin m → Fin m → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStep : SchurStageActiveColumnStepOnActive13_8 stageNorm) :
    SchurStageActiveColumnBoundOnActive13_8 stageNorm blockNorm := by
  intro k
  induction k with
  | zero =>
      intro j _hj
      calc
        ∑ i ∈ activeBlockIndices13_8 m 0, stageNorm 0 i j
            = ∑ i : Fin m, blockNorm i j := by
                rw [activeBlockIndices13_8_zero]
                exact Finset.sum_congr rfl (fun i _ => hInit i j)
        _ ≤ ∑ i : Fin m, blockNorm i j := le_rfl
  | succ k ih =>
      intro j hj
      exact le_trans (hStep k j hj) (ih j (Nat.le_of_succ_le hj))

/-- **Theorem 13.8, active-column final bound**:
    from the active-column-only induction invariant, every active stage block
    satisfies the source's `2 * max ‖Aᵢⱼ‖` bound. -/
theorem higham13_theorem13_8_active_stage_block_bound_on_active {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hStageColumn : SchurStageActiveColumnBoundOnActive13_8 stageNorm blockNorm)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    stageNorm k i j ≤ 2 * normMax := by
  have hi_mem : i ∈ activeBlockIndices13_8 m k := by
    simp [activeBlockIndices13_8, hik]
  have hsingle :
      stageNorm k i j ≤
        ∑ i' ∈ activeBlockIndices13_8 m k, stageNorm k i' j :=
    Finset.single_le_sum (fun i' _ => hStageNonneg k i' j) hi_mem
  have hstage :
      ∑ i' ∈ activeBlockIndices13_8 m k, stageNorm k i' j ≤
        ∑ i' : Fin m, blockNorm i' j :=
    hStageColumn k j hjk
  have hcol : ∑ i' : Fin m, blockNorm i' j ≤ 2 * normMax :=
    col_sum_le_twice_diag blockNorm invDiagBound hDom hDiagBound normMax hMax j
  exact le_trans hsingle (le_trans hstage hcol)

/-- **Theorem 13.8, active-column bound from active one-step inequalities**.
    This version uses the weaker, source-relevant active-column step predicate
    instead of requiring the one-step inequality for inactive columns. -/
theorem higham13_theorem13_8_active_stage_block_bound_on_active_of_steps {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStep : SchurStageActiveColumnStepOnActive13_8 stageNorm)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    stageNorm k i j ≤ 2 * normMax := by
  exact higham13_theorem13_8_active_stage_block_bound_on_active
    blockNorm invDiagBound hDom hDiagBound stageNorm hStageNonneg
    (higham13_theorem13_8_active_column_bound_on_active_of_steps
      stageNorm blockNorm hInit hStep)
    normMax hMax k i j hik hjk

/-- Local Schur-complement block-norm estimate for one active stage of
    Higham's Theorem 13.8.  With pivot block `k`, every next-stage active block
    is bounded by the old block plus the product through the pivot column/row. -/
def SchurStageActiveLocalSchurBound13_8 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
    k + 1 ≤ i.val → k + 1 ≤ j.val →
      stageNorm (k + 1) i j ≤
        stageNorm k i j +
          stageNorm k i ⟨k, hk⟩ * pivotInvNorm k * stageNorm k ⟨k, hk⟩ j

/-- Exact active Schur-complement update relation for Higham's Theorem 13.8.
    At pivot stage `k`, every block still active in the next Schur complement is
    the old block minus the pivot-column / inverse-pivot / pivot-row product.
    This is the source formula behind the local norm estimate. -/
def SchurStageActiveExactUpdate13_8 {m : ℕ} {α : Type*} [Sub α] [Mul α]
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α) : Prop :=
  ∀ k : ℕ, ∀ hk : k < m, ∀ i j : Fin m,
    k + 1 ≤ i.val → k + 1 ≤ j.val →
      stageBlock (k + 1) i j =
        stageBlock k i j -
          stageBlock k i ⟨k, hk⟩ * pivotInv k * stageBlock k ⟨k, hk⟩ j

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    concrete active Schur-stage block table.

    `stage 0` is the input block table.  At pivot stage `k`, blocks still active
    in the next trailing Schur complement are updated by
    `Aᵢⱼ ← Aᵢⱼ - Aᵢₖ Aₖₖ⁻¹ Aₖⱼ`.  Inactive entries are carried forward; the
    theorem below only reads active entries, matching the source proof.  The
    total `pivotInv` input keeps the separate nonsingularity/pivot-certificate
    obligation visible. -/
noncomputable def higham13_algorithm13_3_schurStageBlock {m : ℕ}
    {α : Type*} [Sub α] [Mul α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    ℕ → Fin m → Fin m → α
  | 0, i, j => A i j
  | k + 1, i, j =>
      if hk : k < m then
        if _hactive : k + 1 ≤ i.val ∧ k + 1 ≤ j.val then
          higham13_algorithm13_3_schurStageBlock A pivotInv k i j -
            higham13_algorithm13_3_schurStageBlock A pivotInv k i ⟨k, hk⟩ *
              pivotInv k *
              higham13_algorithm13_3_schurStageBlock A pivotInv k ⟨k, hk⟩ j
        else
          higham13_algorithm13_3_schurStageBlock A pivotInv k i j
      else
        higham13_algorithm13_3_schurStageBlock A pivotInv k i j

/-- Algorithm 13.3 Schur stages start from the original block table. -/
theorem higham13_algorithm13_3_schurStageBlock_zero {m : ℕ}
    {α : Type*} [Sub α] [Mul α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    ∀ i j : Fin m,
      higham13_algorithm13_3_schurStageBlock A pivotInv 0 i j = A i j := by
  intro i j
  rfl

/-- Algorithm 13.3 Schur stages satisfy the exact active Schur-complement
    update relation used by the Theorem 13.7--13.8 proof chain. -/
theorem higham13_algorithm13_3_schurStageBlock_exact_update {m : ℕ}
    {α : Type*} [Sub α] [Mul α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    SchurStageActiveExactUpdate13_8
      (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv := by
  intro k hk i j hi hj
  simp [higham13_algorithm13_3_schurStageBlock, hk, hi, hj]

/-- Matrix-product specialization of the concrete Algorithm 13.3 Schur-stage
    block table.

    The generic stage table above is useful over abstract multiplicative block
    types.  This wrapper fixes the block type to square matrices so `*` is the
    source block-matrix product, not pointwise function multiplication. -/
noncomputable def higham13_algorithm13_3_schurStageMatrixBlock {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    ℕ → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
  higham13_algorithm13_3_schurStageBlock A pivotInv

/-- The first active tail of the matrix-product Algorithm 13.3 Schur-stage
    table is exactly the source block Schur complement. -/
theorem higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (hpivot : pivotInv 0 = A11_inv) :
    (fun i j =>
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv 1
        (Fin.succ i) (Fin.succ j)) =
      blockSchur A A11_inv := by
  ext i j s t
  have hpos : 0 < m + 1 := Nat.succ_pos m
  simp [higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock, blockSchur, hpivot, hpos,
    Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- If a block is not in the active trailing submatrix for pivot `k`, the
    matrix-product Algorithm 13.3 stage table carries it forward unchanged. -/
theorem higham13_algorithm13_3_schurStageMatrixBlock_inactive
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {k : ℕ} (hk : k < m) {i j : Fin m}
    (hnot : ¬ (k + 1 ≤ i.val ∧ k + 1 ≤ j.val)) :
    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j =
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j := by
  have hnot_lt : ¬ (k < i.val ∧ k < j.val) := by
    intro h
    exact hnot ⟨Nat.succ_le_of_lt h.1, Nat.succ_le_of_lt h.2⟩
  simp [higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock, hk, hnot_lt]

/-- Past the last pivot index, the total matrix-product Algorithm 13.3 stage
    table is constant. -/
theorem higham13_algorithm13_3_schurStageMatrixBlock_past_last
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    {k : ℕ} (hk : ¬ k < m) (i j : Fin m) :
    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1) i j =
      higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j := by
  simp [higham13_algorithm13_3_schurStageMatrixBlock,
    higham13_algorithm13_3_schurStageBlock, hk]

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3:
    after eliminating the first block, the recursive matrix-product Schur-stage
    table on `blockSchur A (pivotInv 0)` is the tail of the original stage
    table with all pivot indices shifted by one. -/
theorem higham13_algorithm13_3_schurStageMatrixBlock_tail_shift
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    ∀ k : ℕ, ∀ i j : Fin m,
      higham13_algorithm13_3_schurStageMatrixBlock
          (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) k i j =
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
          (Fin.succ i) (Fin.succ j) := by
  intro k
  induction k with
  | zero =>
      intro i j
      have h :=
        higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur
          A pivotInv (pivotInv 0) rfl
      exact (congr_fun (congr_fun h i) j).symm
  | succ k ih =>
      intro i j
      by_cases hk : k < m
      · have hkFull : k + 1 < m + 1 := Nat.succ_lt_succ hk
        have hpivot :
            (⟨k + 1, hkFull⟩ : Fin (m + 1)) =
              Fin.succ (⟨k, hk⟩ : Fin m) := by
          ext
          rfl
        by_cases hact : k + 1 ≤ i.val ∧ k + 1 ≤ j.val
        · have hactFull :
              k + 1 + 1 ≤ (Fin.succ i).val ∧
                k + 1 + 1 ≤ (Fin.succ j).val := by
            constructor <;> simp [Fin.val_succ] <;> omega
          let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
            blockSchur A (pivotInv 0)
          have hL :=
            (higham13_algorithm13_3_schurStageBlock_exact_update
              S (fun q => pivotInv (q + 1)))
              k hk i j hact.1 hact.2
          have hR :=
            (higham13_algorithm13_3_schurStageBlock_exact_update
              A pivotInv)
              (k + 1) hkFull (Fin.succ i) (Fin.succ j)
              hactFull.1 hactFull.2
          have hL' :
              higham13_algorithm13_3_schurStageMatrixBlock
                  (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                  (k + 1) i j =
                higham13_algorithm13_3_schurStageMatrixBlock
                    (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                    k i j -
                  higham13_algorithm13_3_schurStageMatrixBlock
                      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                      k i ⟨k, hk⟩ *
                      pivotInv (k + 1) *
                    higham13_algorithm13_3_schurStageMatrixBlock
                      (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                      k ⟨k, hk⟩ j := by
            simpa [S, higham13_algorithm13_3_schurStageMatrixBlock] using hL
          have hR' :
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1 + 1)
                  (Fin.succ i) (Fin.succ j) =
                higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                    (Fin.succ i) (Fin.succ j) -
                  higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                      (Fin.succ i) ⟨k + 1, hkFull⟩ * pivotInv (k + 1) *
                    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                      ⟨k + 1, hkFull⟩ (Fin.succ j) := by
            simpa [higham13_algorithm13_3_schurStageMatrixBlock] using hR
          calc
            higham13_algorithm13_3_schurStageMatrixBlock
                (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                (k + 1) i j
                =
              higham13_algorithm13_3_schurStageMatrixBlock
                  (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                  k i j -
                higham13_algorithm13_3_schurStageMatrixBlock
                    (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                    k i ⟨k, hk⟩ *
                    pivotInv (k + 1) *
                  higham13_algorithm13_3_schurStageMatrixBlock
                    (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                    k ⟨k, hk⟩ j := hL'
            _ =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                  (Fin.succ i) (Fin.succ j) -
                higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                    (Fin.succ i) ⟨k + 1, hkFull⟩ * pivotInv (k + 1) *
                  higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                    ⟨k + 1, hkFull⟩ (Fin.succ j) := by
                rw [ih i j, ih i ⟨k, hk⟩, ih ⟨k, hk⟩ j, hpivot]
            _ =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1 + 1)
                (Fin.succ i) (Fin.succ j) := hR'.symm
        · have hactFull :
              ¬ (k + 1 + 1 ≤ (Fin.succ i).val ∧
                k + 1 + 1 ≤ (Fin.succ j).val) := by
            intro h
            apply hact
            constructor <;> simp [Fin.val_succ] at h ⊢ <;> omega
          calc
            higham13_algorithm13_3_schurStageMatrixBlock
                (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                (k + 1) i j =
              higham13_algorithm13_3_schurStageMatrixBlock
                (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
                k i j := by
                exact
                  higham13_algorithm13_3_schurStageMatrixBlock_inactive
                    (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) hk hact
            _ =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                (Fin.succ i) (Fin.succ j) := ih i j
            _ =
              higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1 + 1)
                (Fin.succ i) (Fin.succ j) := by
                exact
                  (higham13_algorithm13_3_schurStageMatrixBlock_inactive
                    A pivotInv hkFull hactFull).symm
      · have hkFull : ¬ k + 1 < m + 1 := by
          exact fun h => hk (Nat.lt_of_succ_lt_succ h)
        calc
          higham13_algorithm13_3_schurStageMatrixBlock
              (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
              (k + 1) i j =
            higham13_algorithm13_3_schurStageMatrixBlock
              (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1))
              k i j := by
              exact
                higham13_algorithm13_3_schurStageMatrixBlock_past_last
                  (blockSchur A (pivotInv 0)) (fun q => pivotInv (q + 1)) hk i j
          _ =
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
              (Fin.succ i) (Fin.succ j) := ih i j
          _ =
            higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1 + 1)
              (Fin.succ i) (Fin.succ j) := by
              exact
                (higham13_algorithm13_3_schurStageMatrixBlock_past_last
                  A pivotInv hkFull (Fin.succ i) (Fin.succ j)).symm

/-- Higham, 2nd ed., Chapter 13, Theorems 13.2 and 13.7:
    an all-leading-prefix nonsingularity table contains a two-sided inverse for
    the first block.  Unlike the first-`m-1` condition in Theorem 13.2, this
    table includes the full matrix, as required by the nonsingularity
    hypothesis of Theorem 13.7. -/
theorem higham13_first_block_inverse_of_all_leadingBlockPrefixes {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp)) :
    ∃ A11_inv : Matrix (Fin r) (Fin r) ℝ,
      IsLeftInverse r (A 0 0) A11_inv ∧
        IsRightInverse r (A 0 0) A11_inv := by
  rcases hPrefix 0 (Nat.succ_pos m) with ⟨Ainv, hInv⟩
  refine ⟨Ainv 0 0, ?_, ?_⟩
  · intro s t
    have h := hInv.1 0 0 s t
    rw [Fin.sum_univ_one] at h
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using h
  · intro s t
    have h := hInv.2 0 0 s t
    rw [Fin.sum_univ_one] at h
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using h

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof dependency:
    eliminating the first block transports an all-leading-prefix
    nonsingularity table to the recursively generated Schur tail. -/
theorem higham13_all_leadingBlockPrefixes_blockSchur {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (hInvLeft : IsLeftInverse r (A 0 0) A11_inv)
    (hInvRight : IsRightInverse r (A 0 0) A11_inv)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m + 1,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp)) :
    ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular
        (leadingBlockPrefix13_2 (blockSchur A A11_inv) p hp) := by
  intro p hp
  cases m with
  | zero => omega
  | succ m =>
      have hpFull : p + 1 < m + 2 := Nat.succ_lt_succ hp
      have hA_prefix := hPrefix (p + 1) hpFull
      have hInvLeft_prefix :
          IsLeftInverse r
            (leadingBlockPrefix13_2 A (p + 1) hpFull 0 0) A11_inv := by
        intro s t
        simpa [leadingBlockPrefix13_2] using hInvLeft s t
      have hInvRight_prefix :
          IsRightInverse r
            (leadingBlockPrefix13_2 A (p + 1) hpFull 0 0) A11_inv := by
        intro s t
        simpa [leadingBlockPrefix13_2] using hInvRight s t
      rw [leadingBlockPrefix13_2_blockSchur A A11_inv p hp]
      exact blockSchur_nonsingular_of_nonsingular_of_first_block_inverse
        hInvLeft_prefix hInvRight_prefix hA_prefix

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.7:
    if every leading block prefix is nonsingular, there is a recursively
    compatible pivot-inverse table whose entry at each active stage is an
    exact right inverse of that stage's diagonal pivot block.

    This constructs the formerly external pivot table used by the source
    Eq.13.21/Eq.13.23 growth route.  It does not assume a prebuilt Algorithm
    13.3 execution or any inverse-norm comparison. -/
theorem
    higham13_algorithm13_3_exists_pivotInv_right_inverse_of_all_leadingBlockPrefixes
    {m r : ℕ}
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp)) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      ∀ k : ℕ, ∀ hk : k < m,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k) := by
  induction m with
  | zero =>
      refine ⟨fun _ => 0, ?_⟩
      intro k hk
      omega
  | succ m ih =>
      rcases higham13_first_block_inverse_of_all_leadingBlockPrefixes A hPrefix with
        ⟨A11_inv, hInvLeft, hInvRight⟩
      let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
        blockSchur A A11_inv
      have hTailPrefix : ∀ p : ℕ, ∀ hp : p < m,
          BlockMatrixNonsingular (leadingBlockPrefix13_2 S p hp) := by
        simpa [S] using
          higham13_all_leadingBlockPrefixes_blockSchur
            A A11_inv hInvLeft hInvRight hPrefix
      rcases ih S hTailPrefix with ⟨tailInv, hTailInv⟩
      let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ
        | 0 => A11_inv
        | k + 1 => tailInv k
      refine ⟨pivotInv, ?_⟩
      intro k hk
      cases k with
      | zero =>
          simpa [pivotInv, higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock] using hInvRight
      | succ k =>
          have hkTail : k < m := Nat.lt_of_succ_lt_succ hk
          have hStage :
              higham13_algorithm13_3_schurStageMatrixBlock S tailInv k
                  ⟨k, hkTail⟩ ⟨k, hkTail⟩ =
                higham13_algorithm13_3_schurStageMatrixBlock A pivotInv (k + 1)
                  ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ := by
            simpa [S, pivotInv] using
              (higham13_algorithm13_3_schurStageMatrixBlock_tail_shift
                A pivotInv k ⟨k, hkTail⟩ ⟨k, hkTail⟩)
          rw [← hStage]
          simpa [pivotInv] using hTailInv k hkTail

/-- Norm table associated with the concrete Algorithm 13.3 Schur-stage blocks. -/
noncomputable def higham13_algorithm13_3_schurStageNorm {m : ℕ}
    {α : Type*} [Sub α] [Mul α] [Norm α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    ℕ → Fin m → Fin m → ℝ :=
  fun k i j => ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖

/-- Norm table associated with the supplied Algorithm 13.3 pivot inverses. -/
noncomputable def higham13_algorithm13_3_pivotInvNorm {α : Type*} [Norm α]
    (pivotInv : ℕ → α) : ℕ → ℝ :=
  fun k => ‖pivotInv k‖

/-- The concrete Algorithm 13.3 Schur-stage norm table is nonnegative. -/
theorem higham13_algorithm13_3_schurStageNorm_nonneg {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    ∀ k : ℕ, ∀ i j : Fin m,
      0 ≤ higham13_algorithm13_3_schurStageNorm A pivotInv k i j := by
  intro k i j
  simp [higham13_algorithm13_3_schurStageNorm]

/-- The concrete Algorithm 13.3 pivot-inverse norm table is nonnegative. -/
theorem higham13_algorithm13_3_pivotInvNorm_nonneg
    {α : Type*} [SeminormedRing α] (pivotInv : ℕ → α) :
    ∀ k : ℕ, 0 ≤ higham13_algorithm13_3_pivotInvNorm pivotInv k := by
  intro k
  simp [higham13_algorithm13_3_pivotInvNorm]

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8 proof:
    the exact Schur-complement block update implies the local Schur norm
    estimate by the triangle inequality and norm submultiplicativity.

    This replaces the local Schur bound as an assumed proof step whenever a
    concrete Schur-stage block sequence has been constructed. -/
theorem higham13_theorem13_8_active_local_schur_bound_of_exact_update {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv) :
    SchurStageActiveLocalSchurBound13_8 stageNorm pivotInvNorm := by
  intro k hk i j hik hjk
  let p : Fin m := ⟨k, hk⟩
  have hmul :
      ‖stageBlock k i p * pivotInv k * stageBlock k p j‖ ≤
        ‖stageBlock k i p‖ * ‖pivotInv k‖ * ‖stageBlock k p j‖ := by
    calc
      ‖stageBlock k i p * pivotInv k * stageBlock k p j‖
          ≤ ‖stageBlock k i p * pivotInv k‖ * ‖stageBlock k p j‖ :=
            norm_mul_le _ _
      _ ≤ (‖stageBlock k i p‖ * ‖pivotInv k‖) * ‖stageBlock k p j‖ := by
            exact mul_le_mul_of_nonneg_right
              (norm_mul_le (stageBlock k i p) (pivotInv k)) (norm_nonneg _)
      _ = ‖stageBlock k i p‖ * ‖pivotInv k‖ * ‖stageBlock k p j‖ := by
            ring
  calc
    stageNorm (k + 1) i j
        = ‖stageBlock (k + 1) i j‖ := hStageNorm (k + 1) i j
    _ = ‖stageBlock k i j - stageBlock k i p * pivotInv k * stageBlock k p j‖ := by
        rw [hUpdate k hk i j hik hjk]
    _ ≤ ‖stageBlock k i j‖ +
          ‖stageBlock k i p * pivotInv k * stageBlock k p j‖ :=
        norm_sub_le _ _
    _ ≤ ‖stageBlock k i j‖ +
          ‖stageBlock k i p‖ * ‖pivotInv k‖ * ‖stageBlock k p j‖ :=
        by
          have := add_le_add_left hmul ‖stageBlock k i j‖
          simpa [add_comm, add_left_comm, add_assoc] using this
    _ = stageNorm k i j +
          stageNorm k i p * pivotInvNorm k * stageNorm k p j := by
        rw [hStageNorm k i j, hStageNorm k i p, hPivotInvNorm k, hStageNorm k p j]

/-- Concrete Algorithm 13.3 Schur stages instantiate the local Schur norm
    estimate used in the Theorem 13.8 proof.  The remaining source obligations
    are the pivot inverse data, reciprocal/diagonal certificates, and dominance
    hypotheses; this theorem only closes the stage-construction/update part. -/
theorem higham13_algorithm13_3_schurStage_local_schur_bound {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (A : Fin m → Fin m → α) (pivotInv : ℕ → α) :
    SchurStageActiveLocalSchurBound13_8
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (higham13_algorithm13_3_pivotInvNorm pivotInv) := by
  exact higham13_theorem13_8_active_local_schur_bound_of_exact_update
    (higham13_algorithm13_3_schurStageBlock A pivotInv) pivotInv
    (higham13_algorithm13_3_schurStageNorm A pivotInv)
    (higham13_algorithm13_3_pivotInvNorm pivotInv)
    (by
      intro k i j
      simp [higham13_algorithm13_3_schurStageNorm])
    (by
      intro k
      rfl)
    (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)

/-- Source-facing reciprocal certificate for the active pivot inverse in
    Higham's Theorem 13.7--13.8 proof chain.

    At stage `k`, the diagonal dominance budget at the pivot block is the
    reciprocal of the pivot inverse norm.  This records the scalar algebraic
    premise `‖A_kk^{-1}‖ * ‖A_kk^{-1}‖^{-1} ≤ 1` without claiming that the
    concrete pivot inverse or nonsingularity has already been constructed. -/
def SchurStageActivePivotInvReciprocal13_7 {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ hk : k < m,
    stageInvDiagBound k ⟨k, hk⟩ = (pivotInvNorm k)⁻¹

/-- Source-facing one-sided pivot certificate for the active Schur-stage proof.

    In Higham's equation (13.18) proof chain, the diagonal certificate carried
    by the Schur complement is a lower bound for the reciprocal norm of the
    active pivot inverse.  This predicate records exactly that one-sided fact;
    it is weaker than the reciprocal equality above but strong enough for the
    product estimate used by Theorems 13.7--13.8. -/
def SchurStageActivePivotInvDiagLower13_7 {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ hk : k < m,
    stageInvDiagBound k ⟨k, hk⟩ ≤ (pivotInvNorm k)⁻¹

/-- A reciprocal active-pivot certificate immediately supplies the weaker
    one-sided diagonal-lower certificate used by the direct pivot-bound route. -/
theorem SchurStageActivePivotInvDiagLower13_7.of_reciprocal {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound pivotInvNorm) :
    SchurStageActivePivotInvDiagLower13_7
      stageInvDiagBound pivotInvNorm := by
  intro k hk
  rw [hRecip k hk]

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof:
    product-form pivot data implies the reciprocal pivot certificate used by
    the active Schur-stage wrappers.

    The nonzero pivot-inverse norm and product identity remain explicit,
    because they are concrete nonsingularity/pivot facts for Algorithm 13.3,
    not consequences of the abstract stage predicates alone. -/
theorem SchurStageActivePivotInvReciprocal13_7.of_mul_eq_one {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hPivotInvNorm_ne : ∀ k : ℕ, pivotInvNorm k ≠ 0)
    (hMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ * pivotInvNorm k = 1) :
    SchurStageActivePivotInvReciprocal13_7 stageInvDiagBound pivotInvNorm := by
  intro k hk
  have hne : pivotInvNorm k ≠ 0 := hPivotInvNorm_ne k
  calc
    stageInvDiagBound k ⟨k, hk⟩
        = (stageInvDiagBound k ⟨k, hk⟩ * pivotInvNorm k) *
            (pivotInvNorm k)⁻¹ := by
            field_simp [hne]
    _ = 1 * (pivotInvNorm k)⁻¹ := by rw [hMul k hk]
    _ = (pivotInvNorm k)⁻¹ := by ring

/-- Product-form pivot data on the active stages is enough for the reciprocal
    certificate; the nonzero pivot-inverse norm follows from the product being
    `1`.  This is often the source-facing form of the Algorithm 13.3 pivot
    obligation. -/
theorem SchurStageActivePivotInvReciprocal13_7.of_active_mul_eq_one {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ * pivotInvNorm k = 1) :
    SchurStageActivePivotInvReciprocal13_7 stageInvDiagBound pivotInvNorm := by
  intro k hk
  have hne : pivotInvNorm k ≠ 0 := by
    intro hzero
    have hprod := hMul k hk
    simp [hzero] at hprod
  calc
    stageInvDiagBound k ⟨k, hk⟩
        = (stageInvDiagBound k ⟨k, hk⟩ * pivotInvNorm k) *
            (pivotInvNorm k)⁻¹ := by
            field_simp [hne]
    _ = 1 * (pivotInvNorm k)⁻¹ := by rw [hMul k hk]
    _ = (pivotInvNorm k)⁻¹ := by ring

/-- Active product-form pivot data supplies the weaker one-sided
    diagonal-lower certificate, with nonzero pivot-inverse norms derived from
    the product identity. -/
theorem SchurStageActivePivotInvDiagLower13_7.of_active_mul_eq_one {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hMul : ∀ k : ℕ, ∀ hk : k < m,
      stageInvDiagBound k ⟨k, hk⟩ * pivotInvNorm k = 1) :
    SchurStageActivePivotInvDiagLower13_7
      stageInvDiagBound pivotInvNorm :=
  SchurStageActivePivotInvDiagLower13_7.of_reciprocal
    stageInvDiagBound pivotInvNorm
    (SchurStageActivePivotInvReciprocal13_7.of_active_mul_eq_one
      stageInvDiagBound pivotInvNorm hMul)

/-- A positive direct pivot product bound is equivalent to the one-sided
    diagonal-lower certificate used in the source proof.  This exposes the
    reverse direction of `higham13_theorem13_7_pivot_inverse_bound_of_diag_lower`
    for future concrete pivot estimates. -/
theorem SchurStageActivePivotInvDiagLower13_7.of_pivot_bound {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hPivotPos : ∀ k : ℕ, 0 < pivotInvNorm k)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) :
    SchurStageActivePivotInvDiagLower13_7
      stageInvDiagBound pivotInvNorm := by
  intro k hk
  have hpos : 0 < pivotInvNorm k := hPivotPos k
  have hnonneg_inv : 0 ≤ (pivotInvNorm k)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hpos)
  calc
    stageInvDiagBound k ⟨k, hk⟩
        = (pivotInvNorm k)⁻¹ *
            (pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩) := by
          field_simp [hpos.ne']
    _ ≤ (pivotInvNorm k)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (hPivotBound k hk) hnonneg_inv
    _ = (pivotInvNorm k)⁻¹ := by ring

/-- Source-facing diagonal Schur lower-bound update for the active-stage
    proof of Higham's Theorem 13.7.

    This names the active-stage analogue of the final inequality in equation
    (13.18): after eliminating pivot block `k`, the next diagonal certificate
    dominates the old diagonal certificate minus the pivot-column/pivot-row
    Schur correction. -/
def SchurStageActiveDiagLowerUpdate13_7 {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
    k + 1 ≤ j.val →
      stageInvDiagBound k j -
        stageNorm k j ⟨k, hk⟩ * pivotInvNorm k * stageNorm k ⟨k, hk⟩ j ≤
      stageInvDiagBound (k + 1) j

/-- Higham, 2nd ed., Chapter 13, equation (13.18) proof chain:
    an exact diagonal-certificate update gives the lower-bound inequality used
    by the active Schur-stage dominance induction.

    The equality itself remains an explicit Algorithm 13.3 stage obligation;
    this theorem only performs the source-faithful equality-to-inequality
    conversion. -/
theorem SchurStageActiveDiagLowerUpdate13_7.of_eq {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hEq : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound (k + 1) j =
          stageInvDiagBound k j -
            stageNorm k j ⟨k, hk⟩ * pivotInvNorm k * stageNorm k ⟨k, hk⟩ j) :
    SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm := by
  intro k hk j hj
  rw [hEq k hk j hj]

/-- Higham, 2nd ed., Chapter 13, equation (13.18) proof chain:
    lower-norm/min-action data supplies the active diagonal Schur lower-bound
    update.

    This is the source-shaped route suggested by the proof: the certificate
    `stageInvDiagBound k j` is represented as the minimum of the active
    diagonal block on unit vectors, while the perturbation term is bounded by
    the subordinate-norm product
    `‖A_jk^(k)‖ ‖pivotInv_k‖ ‖A_kj^(k)‖`.  The theorem packages the reverse
    triangle step into the active-stage predicate used by the BDD induction,
    without assuming the updated diagonal block is already invertible. -/
theorem SchurStageActiveDiagLowerUpdate13_7.of_unit_min_actions {m : ℕ}
    {E : Type*} [SeminormedAddCommGroup E]
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (diag perturb schurDiag : ℕ → Fin m → E → E)
    (hDiagMin : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        stageInvDiagBound k j ≤ ‖diag k j x‖)
    (hSchurMin : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        ∃ x : E, ‖x‖ = 1 ∧
          stageInvDiagBound (k + 1) j = ‖schurDiag k j x‖)
    (hPerturb : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        ‖perturb k j x‖ ≤
          stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
            stageNorm k ⟨k, hk⟩ j)
    (hSchur : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        schurDiag k j x = diag k j x - perturb k j x) :
    SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm := by
  intro k hk j hj
  exact higham13_eq13_18_min_lower_bound
    (diag k j) (perturb k j) (schurDiag k j)
    (stageInvDiagBound k j) (stageInvDiagBound (k + 1) j)
        (stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
          stageNorm k ⟨k, hk⟩ j)
    (hDiagMin k hk j hj)
    (hSchurMin k hk j hj)
    (hPerturb k hk j hj)
    (hSchur k hk j hj)

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    continuous-linear lower-norm table for active Schur diagonal updates.

    This is the source lower-norm construction in a generic proper normed real
    vector space.  The certificate at stage `(k,j)` is the attained minimum
    `min_{‖x‖=1} ‖A_jj^(k) x‖`.  The perturbation estimate remains explicit
    and should be supplied by the chosen subordinate block norm. -/
theorem SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_stage_lower_norms
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (stageDiag perturb : ℕ → Fin m → E →L[ℝ] E)
    (hPerturb : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        ‖perturb k j x‖ ≤
          stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
            stageNorm k ⟨k, hk⟩ j)
    (hSchur : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        stageDiag (k + 1) j x = stageDiag k j x - perturb k j x) :
    SchurStageActiveDiagLowerUpdate13_7
      stageNorm
      (fun k j => continuousLinearMapLowerNorm (stageDiag k j) hunit)
      pivotInvNorm := by
  exact
    SchurStageActiveDiagLowerUpdate13_7.of_unit_min_actions
      stageNorm
      (fun k j => continuousLinearMapLowerNorm (stageDiag k j) hunit)
      pivotInvNorm
      (fun k j x => stageDiag k j x)
      (fun k j x => perturb k j x)
      (fun k j x => stageDiag (k + 1) j x)
      (fun k _hk j _hj x hx =>
        continuousLinearMapLowerNorm_le (stageDiag k j) hunit x hx)
      (fun k _hk j _hj =>
        continuousLinearMapLowerNorm_attained (stageDiag (k + 1) j) hunit)
      hPerturb hSchur

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    continuous-linear Schur-composition instance of the lower-norm table.

    This packages the subordinate-norm perturbation estimate when the Schur
    correction has the source form
    `A_jk^(k) (A_kk^(k))⁻¹ A_kj^(k)`.  The block norm is the operator norm of
    the corresponding continuous linear map, so the perturbation estimate is
    discharged by the generic triple-product op-norm inequality. -/
theorem SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_schur_composition
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (stageBlock : ℕ → Fin m → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hSchur : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        stageBlock (k + 1) j j x =
          stageBlock k j j x -
            stageBlock k j ⟨k, hk⟩
              (pivotInv k (stageBlock k ⟨k, hk⟩ j x))) :
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => ‖stageBlock k i j‖)
      (fun k j => continuousLinearMapLowerNorm (stageBlock k j j) hunit)
      (fun k => ‖pivotInv k‖) := by
  let perturb : ℕ → Fin m → E →L[ℝ] E :=
    fun k j =>
      if hk : k < m then
        (stageBlock k j ⟨k, hk⟩).comp
          ((pivotInv k).comp (stageBlock k ⟨k, hk⟩ j))
      else 0
  exact
    SchurStageActiveDiagLowerUpdate13_7.of_continuousLinearMap_stage_lower_norms
      hunit
      (fun k i j => ‖stageBlock k i j‖)
      (fun k => ‖pivotInv k‖)
      (fun k j => stageBlock k j j)
      perturb
      (by
        intro k hk j _hj x hx
        let p : Fin m := ⟨k, hk⟩
        simpa [perturb, hk, p, ContinuousLinearMap.comp_apply] using
          (continuousLinearMap_triple_norm_le_of_unit
            (stageBlock k j p) (pivotInv k) (stageBlock k p j) hx))
      (by
        intro k hk j hj x
        let p : Fin m := ⟨k, hk⟩
        simpa [perturb, hk, p, ContinuousLinearMap.comp_apply] using
          (hSchur k hk j hj x))

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    reciprocal active-pivot table from a two-sided continuous-linear inverse.

    In a generic proper normed real vector space, if the supplied active pivot
    inverse is a two-sided inverse of the active diagonal action, then the
    active lower norm is exactly the reciprocal operator norm of that inverse.
    This is the arbitrary-norm analogue of the Euclidean finite-matrix
    reciprocal table. -/
theorem SchurStageActivePivotInvReciprocal13_7.of_continuousLinearMap_inverse
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (stageDiag : ℕ → Fin m → E →L[ℝ] E)
    (pivotInv : ℕ → E →L[ℝ] E)
    (hLeft : ∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
      pivotInv k (stageDiag k ⟨k, hk⟩ x) = x)
    (hRight : ∀ k : ℕ, ∀ hk : k < m, ∀ y : E,
      stageDiag k ⟨k, hk⟩ (pivotInv k y) = y) :
    SchurStageActivePivotInvReciprocal13_7
      (fun k j => continuousLinearMapLowerNorm (stageDiag k j) hunit)
      (fun k => ‖pivotInv k‖) := by
  intro k hk
  exact
    continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse
      (stageDiag k ⟨k, hk⟩) (pivotInv k) hunit
      (hLeft k hk) (hRight k hk)

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    Euclidean lower-norm table construction for active Schur diagonal updates.

    The diagonal certificate is the actually attained minimum
    `min_{||x||₂=1} ||A_jj^(k) x||₂`, represented by
    `matMulVecLowerNorm2`.  Thus the theorem discharges the
    minimum-attainment part of the Eq.13.18 source route for concrete finite
    Euclidean blocks.  The Schur action identity and subordinate perturbation
    estimate remain explicit analytic obligations. -/
theorem SchurStageActiveDiagLowerUpdate13_7.of_vecNorm2_stage_lower_norm_matrices
    {m r : ℕ} (hr : 0 < r)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (stageDiag perturb : ℕ → Fin m → Fin r → Fin r → ℝ)
    (hPerturb : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : Fin r → ℝ, vecNorm2 x = 1 →
        vecNorm2 (matMulVec r (perturb k j) x) ≤
          stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
            stageNorm k ⟨k, hk⟩ j)
    (hSchur : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : Fin r → ℝ,
        matMulVec r (stageDiag (k + 1) j) x =
          fun i => matMulVec r (stageDiag k j) x i -
            matMulVec r (perturb k j) x i) :
    SchurStageActiveDiagLowerUpdate13_7
      stageNorm
      (fun k j => matMulVecLowerNorm2 hr (stageDiag k j))
      pivotInvNorm := by
  intro k hk j hj
  exact higham13_eq13_18_vecNorm2_min_lower_bound
    (fun x => matMulVec r (stageDiag k j) x)
    (fun x => matMulVec r (perturb k j) x)
    (fun x => matMulVec r (stageDiag (k + 1) j) x)
    (matMulVecLowerNorm2 hr (stageDiag k j))
    (matMulVecLowerNorm2 hr (stageDiag (k + 1) j))
    (stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
      stageNorm k ⟨k, hk⟩ j)
    (fun x hx => matMulVecLowerNorm2_le hr (stageDiag k j) x hx)
    (matMulVecLowerNorm2_attained hr (stageDiag (k + 1) j))
    (hPerturb k hk j hj)
    (hSchur k hk j hj)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    concrete Euclidean lower-norm diagonal update for the true matrix-product
    Schur-stage table.

    This instantiates the lower-norm table construction with the actual
    diagonal blocks `A_jj^(k)`, proves the Schur action identity from the
    Algorithm 13.3 exact update, and proves the perturbation estimate by the
    exact `opNorm2` subordinate triple-product bound.  The active reciprocal
    equality identifying the active lower norm with `||pivotInv_k||₂⁻¹` remains
    a separate nonsingularity/pivot-inverse obligation. -/
theorem higham13_algorithm13_3_vecNorm2_diag_lower_update
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ) :
    SchurStageActiveDiagLowerUpdate13_7
      (fun k i j => opNorm2 (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j s t))
      (fun k j => matMulVecLowerNorm2 hr (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k j j s t))
      (fun k => opNorm2 (fun s t => pivotInv k s t)) := by
  let stage : ℕ → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    higham13_algorithm13_3_schurStageMatrixBlock A pivotInv
  let stageDiag : ℕ → Fin m → Fin r → Fin r → ℝ :=
    fun k j s t => stage k j j s t
  let perturb : ℕ → Fin m → Fin r → Fin r → ℝ :=
    fun k j =>
      if hk : k < m then
        matMul r
          (matMul r (fun s t => stage k j ⟨k, hk⟩ s t)
            (fun s t => pivotInv k s t))
          (fun s t => stage k ⟨k, hk⟩ j s t)
      else
        fun _ _ => 0
  exact
    SchurStageActiveDiagLowerUpdate13_7.of_vecNorm2_stage_lower_norm_matrices
      (m := m) (r := r) hr
      (fun k i j => opNorm2 (fun s t => stage k i j s t))
      (fun k => opNorm2 (fun s t => pivotInv k s t))
      stageDiag perturb
      (by
        intro k hk j _hj x hx
        let p : Fin m := ⟨k, hk⟩
        simpa [perturb, hk, p, stage] using
          (vecNorm2_matMulVec_triple_le_opNorm2_of_unit
            (fun s t => stage k j p s t)
            (fun s t => pivotInv k s t)
            (fun s t => stage k p j s t)
            hx))
      (by
        intro k hk j hj x
        let p : Fin m := ⟨k, hk⟩
        have hUpdate :=
          (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
            k hk j j hj hj
        have hUpdateM :
            stage (k + 1) j j =
              stage k j j - stage k j p * pivotInv k * stage k p j := by
          simpa [stage, higham13_algorithm13_3_schurStageMatrixBlock, p] using
            hUpdate
        ext s
        simp [stageDiag, perturb, hk, p, hUpdateM, matMulVec, matMul,
          Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib])

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and equation (13.18):
    active reciprocal certificate for the Euclidean lower-norm source table.

    If the supplied `pivotInv k` is a right inverse of the active Schur-stage
    pivot block `A_kk^(k)`, then the attained Euclidean lower norm of that
    pivot block is exactly `||pivotInv k||₂⁻¹`.  Together with
    `higham13_algorithm13_3_vecNorm2_diag_lower_update`, this closes the
    active reciprocal-equality part of the concrete 2-norm lower-norm route;
    the source arbitrary-subordinate-norm theorem remains a separate route. -/
theorem higham13_algorithm13_3_vecNorm2_active_pivot_reciprocal_of_right_inverse
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (fun s t =>
          higham13_algorithm13_3_schurStageMatrixBlock
            A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ s t)
        (fun s t => pivotInv k s t)) :
    SchurStageActivePivotInvReciprocal13_7
      (fun k j => matMulVecLowerNorm2 hr (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k j j s t))
      (fun k => opNorm2 (fun s t => pivotInv k s t)) := by
  intro k hk
  simpa using
    (matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse hr
      (fun s t =>
        higham13_algorithm13_3_schurStageMatrixBlock
          A pivotInv k ⟨k, hk⟩ ⟨k, hk⟩ s t)
      (fun s t => pivotInv k s t)
      (hRight k hk))

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    abstract subordinate-norm lower-bound half.

    If `invDiag` is a left inverse for the action of a diagonal block and its
    action is bounded by `normInv`, then every unit vector satisfies
    `normInv⁻¹ <= ‖diag x‖`.  This is the normed-space analogue of rewriting
    a nonsingular block's lower norm as the reciprocal of an inverse norm. -/
theorem higham13_eq13_18_unit_lower_bound_of_inverse_action_bound
    {E : Type*} [SeminormedAddCommGroup E]
    (diag invDiag : E → E) (normInv : ℝ)
    (hNormInvPos : 0 < normInv)
    (hInvBound : ∀ y : E, ‖invDiag y‖ ≤ normInv * ‖y‖)
    (hLeft : ∀ x : E, invDiag (diag x) = x) :
    ∀ x : E, ‖x‖ = 1 → normInv⁻¹ ≤ ‖diag x‖ := by
  intro x hx
  have hInvNonneg : 0 ≤ normInv⁻¹ :=
    inv_nonneg.mpr (le_of_lt hNormInvPos)
  have hone_le : 1 ≤ normInv * ‖diag x‖ := by
    calc
      1 = ‖x‖ := by rw [hx]
      _ = ‖invDiag (diag x)‖ := by rw [hLeft x]
      _ ≤ normInv * ‖diag x‖ := hInvBound (diag x)
  calc
    normInv⁻¹ = normInv⁻¹ * 1 := by ring
    _ ≤ normInv⁻¹ * (normInv * ‖diag x‖) :=
      mul_le_mul_of_nonneg_left hone_le hInvNonneg
    _ = (normInv⁻¹ * normInv) * ‖diag x‖ := by ring
    _ = ‖diag x‖ := by
      rw [inv_mul_cancel₀ hNormInvPos.ne']
      ring

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    active-stage table form of the abstract inverse-action lower-bound half.

    The hypotheses state the source-shaped reciprocal table
    `d(k,j)=normInv(k,j)⁻¹`, a norm bound for the inverse action, and the
    left-inverse identity for each active diagonal block. -/
theorem higham13_eq13_18_active_diag_table_unit_lower_bound_of_inverse_action_bound
    {m : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (diag invDiag : ℕ → Fin m → E → E)
    (normInv : ℕ → Fin m → ℝ)
    (hEq : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → stageInvDiagBound k j = (normInv k j)⁻¹)
    (hNormInvPos : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → 0 < normInv k j)
    (hInvBound : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ y : E,
        ‖invDiag k j y‖ ≤ normInv k j * ‖y‖)
    (hLeft : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, invDiag k j (diag k j x) = x) :
    ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        stageInvDiagBound k j ≤ ‖diag k j x‖ := by
  intro k hk j hj x hx
  rw [hEq k hk j hj]
  exact
    higham13_eq13_18_unit_lower_bound_of_inverse_action_bound
      (diag k j) (invDiag k j) (normInv k j)
      (hNormInvPos k hk j hj) (hInvBound k hk j hj)
      (hLeft k hk j hj) x hx

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    inverse-action bounds supply the active diagonal Schur lower-bound update.

    This composes the source reciprocal/inverse-action lower-bound half with the
    existing reverse-triangle/min-action update.  It still keeps the minimum
    for the updated Schur diagonal block and the perturbation estimate explicit. -/
theorem SchurStageActiveDiagLowerUpdate13_7.of_inverse_action_bounds {m : ℕ}
    {E : Type*} [SeminormedAddCommGroup E]
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (diag invDiag perturb schurDiag : ℕ → Fin m → E → E)
    (normInv : ℕ → Fin m → ℝ)
    (hEq : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → stageInvDiagBound k j = (normInv k j)⁻¹)
    (hNormInvPos : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → 0 < normInv k j)
    (hInvBound : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ y : E,
        ‖invDiag k j y‖ ≤ normInv k j * ‖y‖)
    (hLeft : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, invDiag k j (diag k j x) = x)
    (hSchurMin : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val →
        ∃ x : E, ‖x‖ = 1 ∧
          stageInvDiagBound (k + 1) j = ‖schurDiag k j x‖)
    (hPerturb : ∀ k : ℕ, ∀ hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E, ‖x‖ = 1 →
        ‖perturb k j x‖ ≤
          stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
            stageNorm k ⟨k, hk⟩ j)
    (hSchur : ∀ k : ℕ, ∀ _hk : k < m, ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : E,
        schurDiag k j x = diag k j x - perturb k j x) :
    SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm := by
  exact
    SchurStageActiveDiagLowerUpdate13_7.of_unit_min_actions
      stageNorm stageInvDiagBound pivotInvNorm diag perturb schurDiag
      (higham13_eq13_18_active_diag_table_unit_lower_bound_of_inverse_action_bound
        stageInvDiagBound diag invDiag normInv hEq hNormInvPos hInvBound hLeft)
      hSchurMin hPerturb hSchur

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    for the Euclidean subordinate norm, an actual right inverse of a diagonal
    block gives the unit-vector lower bound
    `||B⁻¹||₂⁻¹ <= ||B x||₂`.

    This is the concrete inverse-data half of the lower-norm table route; it
    does not assert that the lower norm/minimum has already been attained. -/
theorem higham13_eq13_18_unit_lower_bound_of_right_inverse_opNorm2
    {r : ℕ} (hr : 0 < r)
    (B Binv : Fin r → Fin r → ℝ)
    (hRight : IsRightInverse r B Binv) :
    ∀ x : Fin r → ℝ, vecNorm2 x = 1 →
      (opNorm2 Binv)⁻¹ ≤ vecNorm2 (matMulVec r B x) := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  intro x hx
  exact
    opNorm2_inv_recip_le_vecNorm2_matMulVec_of_isRightInverse
      B Binv hRight hx

/-- Higham, 2nd ed., Chapter 13, equation (13.18):
    active-stage table form of the Euclidean lower-bound half.

    If a source diagonal certificate is the reciprocal 2-norm of a certified
    right inverse for each active diagonal block, then it is a lower bound for
    that block's action on every Euclidean unit vector.  The separate
    minimum-attainment/Schur-update step remains the open lower-norm-table
    obligation. -/
theorem higham13_eq13_18_active_diag_table_unit_lower_bound_of_right_inverse_opNorm2
    {m r : ℕ} (hr : 0 < r)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (diag diagInv : ℕ → Fin m → Fin r → Fin r → ℝ)
    (hEq : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val →
        stageInvDiagBound k j = (opNorm2 (diagInv k j))⁻¹)
    (hRight : ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val →
        IsRightInverse r (diag k j) (diagInv k j)) :
    ∀ k : ℕ, k < m → ∀ j : Fin m,
      k + 1 ≤ j.val → ∀ x : Fin r → ℝ, vecNorm2 x = 1 →
        stageInvDiagBound k j ≤ vecNorm2 (matMulVec r (diag k j) x) := by
  intro k hk j hj x hx
  rw [hEq k hk j hj]
  exact
    higham13_eq13_18_unit_lower_bound_of_right_inverse_opNorm2
      hr (diag k j) (diagInv k j) (hRight k hk j hj) x hx

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof:
    the source reciprocal pivot certificate implies the pivot inverse product
    bound used in the Schur-stage dominance and growth arguments.

    This is pure scalar algebra.  It deliberately leaves the construction of
    the concrete pivot inverse and the proof that the diagonal certificate is
    its reciprocal as separate source obligations. -/
theorem higham13_theorem13_7_pivot_inverse_bound_of_reciprocal {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound pivotInvNorm) :
    ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1 := by
  intro k hk
  rw [hRecip k hk]
  exact mul_inv_le_one

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof:
    a one-sided diagonal lower-bound certificate is enough to obtain the pivot
    inverse product bound used in the active Schur-stage induction.

    The actual proof that the concrete Algorithm 13.3 certificate has this
    one-sided relation to the true pivot inverse remains a separate
    nonsingularity/inverse-norm obligation. -/
theorem higham13_theorem13_7_pivot_inverse_bound_of_diag_lower {m : ℕ}
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hDiagLower : SchurStageActivePivotInvDiagLower13_7
      stageInvDiagBound pivotInvNorm) :
    ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1 := by
  intro k hk
  have hmul :
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤
        pivotInvNorm k * (pivotInvNorm k)⁻¹ :=
    mul_le_mul_of_nonneg_left (hDiagLower k hk) (hPivotInvNonneg k)
  exact le_trans hmul mul_inv_le_one

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof:
    local Schur-complement estimates imply the one-step active column
    diagonal-dominance inheritance rule.

    The hypothesis `hDiagUpdate` is the remaining source analytic obligation:
    it is the Schur diagonal-block lower-bound step, i.e. the active-stage
    analogue of the last inequality in equation (13.18). -/
theorem higham13_theorem13_7_active_column_dom_step_of_local_schur_bound {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8 stageNorm pivotInvNorm)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm) :
    SchurStageActiveColumnDomStep13_7 stageNorm stageInvDiagBound := by
  intro k hDomK j hj
  have hk_lt_j : k < j.val := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hj
  have hk : k < m := Nat.lt_trans hk_lt_j j.isLt
  let p : Fin m := ⟨k, hk⟩
  let tail := activeBlockIndices13_8 m (k + 1)
  have hp_not : p ∉ tail := by
    simpa [p, tail] using activeBlockIndices13_8_succ_not_mem (m := m) (k := k) hk
  have hp_ne_j : p ≠ j := by
    intro h
    have : j.val = k := by
      exact (congr_arg Fin.val h).symm
    omega
  have hactive_eq :
      activeBlockIndices13_8 m k = insert p tail := by
    simpa [p, tail] using activeBlockIndices13_8_succ_insert (m := m) (k := k) hk
  have htail_local :
      ∑ i ∈ tail, (if i = j then 0 else stageNorm (k + 1) i j) ≤
        ∑ i ∈ tail,
          (if i = j then 0 else
            stageNorm k i j + stageNorm k i p * pivotInvNorm k * stageNorm k p j) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hij : i = j
    · simp [hij]
    · have hik : k + 1 ≤ i.val := by
        simpa [tail, activeBlockIndices13_8] using hi
      simp [hij]
      exact hLocal k hk i j hik hj
  have htail_expand :
      ∑ i ∈ tail,
          (if i = j then 0 else
            stageNorm k i j + stageNorm k i p * pivotInvNorm k * stageNorm k p j) =
        ∑ i ∈ tail, (if i = j then 0 else stageNorm k i j) +
          (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) *
            pivotInvNorm k * stageNorm k p j := by
    calc
      ∑ i ∈ tail,
          (if i = j then 0 else
            stageNorm k i j + stageNorm k i p * pivotInvNorm k * stageNorm k p j)
          = ∑ i ∈ tail,
              ((if i = j then 0 else stageNorm k i j) +
                (if i = j then 0 else
                  stageNorm k i p * pivotInvNorm k * stageNorm k p j)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              by_cases hij : i = j <;> simp [hij]
      _ = ∑ i ∈ tail, (if i = j then 0 else stageNorm k i j) +
            ∑ i ∈ tail,
              (if i = j then 0 else
                stageNorm k i p * pivotInvNorm k * stageNorm k p j) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ i ∈ tail, (if i = j then 0 else stageNorm k i j) +
          (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) *
            pivotInvNorm k * stageNorm k p j := by
              congr 1
              calc
                ∑ i ∈ tail,
                    (if i = j then 0 else
                      stageNorm k i p * pivotInvNorm k * stageNorm k p j)
                    = ∑ i ∈ tail,
                        (if i = j then 0 else stageNorm k i p) *
                          pivotInvNorm k * stageNorm k p j := by
                        apply Finset.sum_congr rfl
                        intro i _hi
                        by_cases hij : i = j <;> simp [hij]
                _ = (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) *
                      pivotInvNorm k * stageNorm k p j := by
                        rw [Finset.sum_mul, Finset.sum_mul]
  have hdom_j : ∑ i ∈ activeBlockIndices13_8 m k,
        (if i = j then 0 else stageNorm k i j) ≤ stageInvDiagBound k j :=
    hDomK j (Nat.le_of_succ_le hj)
  have hdom_j_split :
      ∑ i ∈ activeBlockIndices13_8 m k,
          (if i = j then 0 else stageNorm k i j) =
        stageNorm k p j + ∑ i ∈ tail, (if i = j then 0 else stageNorm k i j) := by
    rw [hactive_eq, Finset.sum_insert hp_not]
    simp [hp_ne_j]
  have htail_j_le :
      ∑ i ∈ tail, (if i = j then 0 else stageNorm k i j) ≤
        stageInvDiagBound k j - stageNorm k p j := by
    rw [hdom_j_split] at hdom_j
    linarith
  have hdom_p : ∑ i ∈ activeBlockIndices13_8 m k,
        (if i = p then 0 else stageNorm k i p) ≤ stageInvDiagBound k p :=
    hDomK p le_rfl
  have hp_col_split :
      ∑ i ∈ activeBlockIndices13_8 m k,
          (if i = p then 0 else stageNorm k i p) =
        stageNorm k j p + ∑ i ∈ tail, (if i = j then 0 else stageNorm k i p) := by
    rw [hactive_eq, Finset.sum_insert hp_not]
    simp only [if_true, zero_add]
    have htail_insert_j :
        tail = insert j (tail.erase j) := by
      rw [Finset.insert_erase]
      simpa [tail, activeBlockIndices13_8, hj]
    rw [htail_insert_j]
    have hj_not_erase : j ∉ tail.erase j := by simp
    rw [Finset.sum_insert hj_not_erase]
    simp [hp_ne_j.symm]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := by
      intro h
      have : i ∉ tail.erase j := by simp [h]
      exact this hi
    have hip : i ≠ p := by
      intro h
      exact hp_not (by
        have hit : i ∈ tail := Finset.mem_of_mem_erase hi
        simpa [h] using hit)
    simp [hij, hip]
  have htail_p_le :
      ∑ i ∈ tail, (if i = j then 0 else stageNorm k i p) ≤
        stageInvDiagBound k p - stageNorm k j p := by
    rw [hp_col_split] at hdom_p
    linarith
  have htail_p_nonneg :
      0 ≤ ∑ i ∈ tail, (if i = j then 0 else stageNorm k i p) := by
    exact Finset.sum_nonneg (fun i _ => by
      by_cases hij : i = j <;> simp [hij, hStageNonneg k i p])
  have hpj_nonneg : 0 ≤ stageNorm k p j := hStageNonneg k p j
  have hjp_nonneg : 0 ≤ stageNorm k j p := hStageNonneg k j p
  have hcoef_bound :
      (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) * pivotInvNorm k ≤
        1 - stageNorm k j p * pivotInvNorm k := by
    have hmul :
        (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) * pivotInvNorm k ≤
          (stageInvDiagBound k p - stageNorm k j p) * pivotInvNorm k :=
      mul_le_mul_of_nonneg_right htail_p_le (hPivotInvNonneg k)
    have hunit : stageInvDiagBound k p * pivotInvNorm k ≤ 1 := by
      calc
        stageInvDiagBound k p * pivotInvNorm k =
            pivotInvNorm k * stageInvDiagBound k p := by ring
        _ ≤ 1 := by simpa [p] using hPivotInvBound k hk
    have hrewrite :
        (stageInvDiagBound k p - stageNorm k j p) * pivotInvNorm k =
          stageInvDiagBound k p * pivotInvNorm k -
            stageNorm k j p * pivotInvNorm k := by ring
    rw [hrewrite] at hmul
    linarith
  have hprod_le :
      (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) *
          pivotInvNorm k * stageNorm k p j ≤
        stageNorm k p j -
          stageNorm k j p * pivotInvNorm k * stageNorm k p j := by
    calc
      (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) *
          pivotInvNorm k * stageNorm k p j
          ≤ (1 - stageNorm k j p * pivotInvNorm k) * stageNorm k p j :=
            mul_le_mul_of_nonneg_right hcoef_bound hpj_nonneg
      _ = stageNorm k p j -
          stageNorm k j p * pivotInvNorm k * stageNorm k p j := by ring
  calc
    ∑ i ∈ activeBlockIndices13_8 m (k + 1),
        (if i = j then 0 else stageNorm (k + 1) i j)
        = ∑ i ∈ tail, (if i = j then 0 else stageNorm (k + 1) i j) := by rfl
    _ ≤ ∑ i ∈ tail,
          (if i = j then 0 else
            stageNorm k i j + stageNorm k i p * pivotInvNorm k * stageNorm k p j) :=
        htail_local
    _ = ∑ i ∈ tail, (if i = j then 0 else stageNorm k i j) +
          (∑ i ∈ tail, (if i = j then 0 else stageNorm k i p)) *
            pivotInvNorm k * stageNorm k p j := htail_expand
    _ ≤ stageInvDiagBound k j -
          stageNorm k j p * pivotInvNorm k * stageNorm k p j := by
        linarith
    _ ≤ stageInvDiagBound (k + 1) j := hDiagUpdate k hk j hj

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof:
    the active one-step column-dominance inheritance rule follows from the
    exact Schur update relation, the pivot inverse bound, and the diagonal
    Schur lower-bound update.

    This removes the local Schur norm estimate as a direct hypothesis; it is
    proved from the exact active update relation immediately above. -/
theorem higham13_theorem13_7_active_column_dom_step_of_exact_update {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm) :
    SchurStageActiveColumnDomStep13_7 stageNorm stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dom_step_of_local_schur_bound
    stageNorm stageInvDiagBound pivotInvNorm
    (by
      intro k i j
      rw [hStageNorm k i j]
      exact norm_nonneg _)
    (by
      intro k
      rw [hPivotInvNorm k]
      exact norm_nonneg _)
    hPivotInvBound
    (higham13_theorem13_8_active_local_schur_bound_of_exact_update
      stageBlock pivotInv stageNorm pivotInvNorm hStageNorm hPivotInvNorm hUpdate)
    hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof:
    exact Schur update plus the source reciprocal pivot certificate gives the
    one-step active column-dominance inheritance rule.

    Compared with
    `higham13_theorem13_7_active_column_dom_step_of_exact_update`, this wrapper
    derives the pivot product bound from
    `SchurStageActivePivotInvReciprocal13_7`. -/
theorem higham13_theorem13_7_active_column_dom_step_of_exact_update_reciprocal {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound pivotInvNorm)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm) :
    SchurStageActiveColumnDomStep13_7 stageNorm stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dom_step_of_exact_update
    stageBlock pivotInv stageNorm stageInvDiagBound pivotInvNorm hStageNorm
    hPivotInvNorm
    (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
      stageInvDiagBound pivotInvNorm hPivotRecip)
    hUpdate hDiagUpdate

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    active-stage column block diagonal dominance follows from the initial column
    dominance and the exact Schur update relation, provided the diagonal Schur
    lower-bound update and pivot inverse bound are supplied.

    The remaining source obligations are now the concrete Schur-stage
    construction, nonsingularity/pivot inverse data, and the diagonal
    lower-bound update, rather than an assumed local Schur norm estimate. -/
theorem higham13_theorem13_7_active_column_dominance_of_exact_update {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm) :
    SchurStageActiveColumnDom13_7 stageNorm stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dominance_of_steps
    blockNorm invDiagBound hDom stageNorm stageInvDiagBound hInitNorm hInitInv
    (higham13_theorem13_7_active_column_dom_step_of_exact_update
      stageBlock pivotInv stageNorm stageInvDiagBound pivotInvNorm
      hStageNorm hPivotInvNorm hPivotInvBound hUpdate hDiagUpdate)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7:
    active-stage column block diagonal dominance from exact Schur updates and
    the source reciprocal pivot certificate.

    This removes the pre-multiplied pivot inverse product bound from the theorem
    surface; the remaining hard source obligations are the concrete Schur-stage
    construction, the reciprocal pivot certificate itself, the diagonal Schur
    lower-bound update, and nonsingularity/block-LU existence. -/
theorem higham13_theorem13_7_active_column_dominance_of_exact_update_reciprocal {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound pivotInvNorm)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm) :
    SchurStageActiveColumnDom13_7 stageNorm stageInvDiagBound := by
  exact higham13_theorem13_7_active_column_dominance_of_steps
    blockNorm invDiagBound hDom stageNorm stageInvDiagBound hInitNorm hInitInv
    (higham13_theorem13_7_active_column_dom_step_of_exact_update_reciprocal
      stageBlock pivotInv stageNorm stageInvDiagBound pivotInvNorm
      hStageNorm hPivotInvNorm hPivotRecip hUpdate hDiagUpdate)

/-- The active off-pivot column sum used in the Theorem 13.8 proof is bounded
    by the active column-dominance certificate from Theorem 13.7. -/
theorem higham13_theorem13_8_active_tail_pivot_sum_le_of_column_dominance {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDom : SchurStageActiveColumnDom13_7 stageNorm stageInvDiagBound)
    (k : ℕ) (hk : k < m) :
    ∑ i ∈ activeBlockIndices13_8 m (k + 1), stageNorm k i ⟨k, hk⟩ ≤
      stageInvDiagBound k ⟨k, hk⟩ := by
  let p : Fin m := ⟨k, hk⟩
  have hp_not : p ∉ activeBlockIndices13_8 m (k + 1) := by
    simpa [p] using activeBlockIndices13_8_succ_not_mem (m := m) (k := k) hk
  have htail_eq :
      ∑ i ∈ activeBlockIndices13_8 m (k + 1), stageNorm k i p =
        ∑ i ∈ activeBlockIndices13_8 m k,
          (if i = p then 0 else stageNorm k i p) := by
    rw [activeBlockIndices13_8_succ_insert (m := m) (k := k) hk]
    rw [Finset.sum_insert hp_not]
    simp only [if_true, zero_add]
    exact Finset.sum_congr rfl (fun i hi => by
      have hip : i ≠ p := by
        intro hIp
        exact hp_not (by simpa [hIp] using hi)
      simp [hip])
  rw [htail_eq]
  exact hDom k p le_rfl

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8 proof:
    the active-column one-step inequality follows from the local Schur
    block-norm estimate, active column dominance from Theorem 13.7, and the
    pivot inverse bound `‖Aₖₖ⁻¹‖ · gammaₖ ≤ 1`.

    This is still a proof-layer result: it does not construct the matrix
    Schur-stage sequence, but it removes the earlier need to assume the
    active-column sum step directly. -/
theorem higham13_theorem13_8_active_column_step_on_active_of_local_schur_bound {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hDom : SchurStageActiveColumnDom13_7 stageNorm stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8 stageNorm pivotInvNorm) :
    SchurStageActiveColumnStepOnActive13_8 stageNorm := by
  intro k j hj
  have hk_lt_j : k < j.val := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hj
  have hk : k < m := Nat.lt_trans hk_lt_j j.isLt
  let p : Fin m := ⟨k, hk⟩
  let tail := activeBlockIndices13_8 m (k + 1)
  have hp_not : p ∉ tail := by
    simpa [p, tail] using activeBlockIndices13_8_succ_not_mem (m := m) (k := k) hk
  have hsum_local :
      ∑ i ∈ tail, stageNorm (k + 1) i j ≤
        ∑ i ∈ tail,
          (stageNorm k i j + stageNorm k i p * pivotInvNorm k * stageNorm k p j) := by
    apply Finset.sum_le_sum
    intro i hi
    have hik : k + 1 ≤ i.val := by
      simpa [tail, activeBlockIndices13_8] using hi
    exact hLocal k hk i j hik hj
  have hsum_expand :
      ∑ i ∈ tail,
          (stageNorm k i j + stageNorm k i p * pivotInvNorm k * stageNorm k p j) =
        ∑ i ∈ tail, stageNorm k i j +
          (∑ i ∈ tail, stageNorm k i p) * pivotInvNorm k * stageNorm k p j := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_mul, Finset.sum_mul]
  have htail_pivot_le :
      ∑ i ∈ tail, stageNorm k i p ≤ stageInvDiagBound k p := by
    simpa [p, tail] using
      higham13_theorem13_8_active_tail_pivot_sum_le_of_column_dominance
        stageNorm stageInvDiagBound hDom k hk
  have hcoef :
      (∑ i ∈ tail, stageNorm k i p) * pivotInvNorm k ≤ 1 := by
    have hmul :
        (∑ i ∈ tail, stageNorm k i p) * pivotInvNorm k ≤
          stageInvDiagBound k p * pivotInvNorm k :=
      mul_le_mul_of_nonneg_right htail_pivot_le (hPivotInvNonneg k)
    have hunit : stageInvDiagBound k p * pivotInvNorm k ≤ 1 := by
      calc
        stageInvDiagBound k p * pivotInvNorm k =
            pivotInvNorm k * stageInvDiagBound k p := by ring
        _ ≤ 1 := by simpa [p] using hPivotInvBound k hk
    exact le_trans hmul hunit
  have hpj_nonneg : 0 ≤ stageNorm k p j := hStageNonneg k p j
  have hprod :
      (∑ i ∈ tail, stageNorm k i p) * pivotInvNorm k * stageNorm k p j ≤
        stageNorm k p j := by
    calc
      (∑ i ∈ tail, stageNorm k i p) * pivotInvNorm k * stageNorm k p j
          ≤ 1 * stageNorm k p j :=
            mul_le_mul_of_nonneg_right hcoef hpj_nonneg
      _ = stageNorm k p j := by ring
  have hactive_sum :
      ∑ i ∈ activeBlockIndices13_8 m k, stageNorm k i j =
        stageNorm k p j + ∑ i ∈ tail, stageNorm k i j := by
    rw [activeBlockIndices13_8_succ_insert (m := m) (k := k) hk]
    rw [Finset.sum_insert hp_not]
  calc
    ∑ i ∈ activeBlockIndices13_8 m (k + 1), stageNorm (k + 1) i j
        = ∑ i ∈ tail, stageNorm (k + 1) i j := by rfl
    _ ≤ ∑ i ∈ tail,
          (stageNorm k i j + stageNorm k i p * pivotInvNorm k * stageNorm k p j) :=
        hsum_local
    _ = ∑ i ∈ tail, stageNorm k i j +
          (∑ i ∈ tail, stageNorm k i p) * pivotInvNorm k * stageNorm k p j :=
        hsum_expand
    _ ≤ ∑ i ∈ tail, stageNorm k i j + stageNorm k p j :=
        by linarith
    _ = ∑ i ∈ activeBlockIndices13_8 m k, stageNorm k i j := by
        rw [hactive_sum]
        ring

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8 proof, mixed matrix route:
    the active-column one-step inequality for entrywise max norms follows from
    the exact matrix Schur update, active column dominance measured in the
    matrix-`∞` norm, and the pivot product bound
    `||pivotInv_k||∞ * gamma_k <= 1`.

    This is the column-BDD max-entry dependency suggested by the Pro route: the
    pivot column is controlled by row-sum mass, while the pivot row is controlled
    entrywise. -/
theorem higham13_theorem13_8_active_column_step_on_active_of_mixed_column_mass
    {m r : ℕ} (hr : 0 < r)
    (stageBlock : ℕ → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInfDom : SchurStageActiveColumnDom13_7
      (fun k i j => infNorm (stageBlock k i j)) stageInvDiagBound)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv) :
    SchurStageActiveColumnStepOnActive13_8
      (fun k i j => maxEntryNorm hr (stageBlock k i j)) := by
  intro k j hj
  have hk_lt_j : k < j.val := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hj
  have hk : k < m := Nat.lt_trans hk_lt_j j.isLt
  let p : Fin m := ⟨k, hk⟩
  let tail := activeBlockIndices13_8 m (k + 1)
  have hp_not : p ∉ tail := by
    simpa [p, tail] using activeBlockIndices13_8_succ_not_mem (m := m) (k := k) hk
  have hsum_local :
      ∑ i ∈ tail, maxEntryNorm hr (stageBlock (k + 1) i j) ≤
        ∑ i ∈ tail,
          (maxEntryNorm hr (stageBlock k i j) +
            maxEntryNorm hr (stageBlock k i p * pivotInv k * stageBlock k p j)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hik : k + 1 ≤ i.val := by
      simpa [tail, activeBlockIndices13_8] using hi
    have hupdate :
        stageBlock (k + 1) i j =
          stageBlock k i j -
            stageBlock k i p * pivotInv k * stageBlock k p j := by
      simpa [p] using hUpdate k hk i j hik hj
    calc
      maxEntryNorm hr (stageBlock (k + 1) i j)
          = maxEntryNorm hr
              (stageBlock k i j -
                stageBlock k i p * pivotInv k * stageBlock k p j) := by
              rw [hupdate]
      _ ≤ maxEntryNorm hr (stageBlock k i j) +
            maxEntryNorm hr
              (stageBlock k i p * pivotInv k * stageBlock k p j) :=
          maxEntryNorm_sub_le hr (stageBlock k i j)
            (stageBlock k i p * pivotInv k * stageBlock k p j)
  have hsum_expand :
      ∑ i ∈ tail,
          (maxEntryNorm hr (stageBlock k i j) +
            maxEntryNorm hr (stageBlock k i p * pivotInv k * stageBlock k p j)) =
        ∑ i ∈ tail, maxEntryNorm hr (stageBlock k i j) +
          ∑ i ∈ tail,
            maxEntryNorm hr (stageBlock k i p * pivotInv k * stageBlock k p j) := by
    rw [Finset.sum_add_distrib]
  have htail_pivot_le :
      ∑ i ∈ tail, infNorm (stageBlock k i p) ≤ stageInvDiagBound k p := by
    simpa [p, tail] using
      higham13_theorem13_8_active_tail_pivot_sum_le_of_column_dominance
        (fun k i j => infNorm (stageBlock k i j)) stageInvDiagBound hInfDom k hk
  have htriple :
      ∑ i ∈ tail,
          maxEntryNorm hr (stageBlock k i p * pivotInv k * stageBlock k p j) ≤
        maxEntryNorm hr (stageBlock k p j) := by
    exact
      higham13_sum_maxEntryNorm_matrix_mul_pivot_mul_le_of_column_mass
        hr tail (fun i => stageBlock k i p) (pivotInv k) (stageBlock k p j)
        htail_pivot_le (by simpa [p] using hPivotBound k hk)
  have hactive_sum :
      ∑ i ∈ activeBlockIndices13_8 m k, maxEntryNorm hr (stageBlock k i j) =
        maxEntryNorm hr (stageBlock k p j) +
          ∑ i ∈ tail, maxEntryNorm hr (stageBlock k i j) := by
    rw [activeBlockIndices13_8_succ_insert (m := m) (k := k) hk]
    rw [Finset.sum_insert hp_not]
  calc
    ∑ i ∈ activeBlockIndices13_8 m (k + 1),
        maxEntryNorm hr (stageBlock (k + 1) i j)
        = ∑ i ∈ tail, maxEntryNorm hr (stageBlock (k + 1) i j) := by rfl
    _ ≤ ∑ i ∈ tail,
          (maxEntryNorm hr (stageBlock k i j) +
            maxEntryNorm hr (stageBlock k i p * pivotInv k * stageBlock k p j)) :=
        hsum_local
    _ = ∑ i ∈ tail, maxEntryNorm hr (stageBlock k i j) +
          ∑ i ∈ tail,
            maxEntryNorm hr (stageBlock k i p * pivotInv k * stageBlock k p j) :=
        hsum_expand
    _ ≤ ∑ i ∈ tail, maxEntryNorm hr (stageBlock k i j) +
          maxEntryNorm hr (stageBlock k p j) :=
        add_le_add_right htriple _
    _ = ∑ i ∈ activeBlockIndices13_8 m k,
          maxEntryNorm hr (stageBlock k i j) := by
        rw [hactive_sum]
        ring

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8 proof, mixed matrix route:
    the active-column invariant for max-entry stage norms follows from exact
    Algorithm 13.3-style Schur updates, active column dominance in the
    matrix-`∞` norm, and the mixed pivot product bound. -/
theorem higham13_theorem13_8_active_column_bound_on_active_of_mixed_column_mass
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (stageBlock : ℕ → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ i j : Fin m, stageBlock 0 i j = A i j)
    (hInfDom : SchurStageActiveColumnDom13_7
      (fun k i j => infNorm (stageBlock k i j)) stageInvDiagBound)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv) :
    SchurStageActiveColumnBoundOnActive13_8
      (fun k i j => maxEntryNorm hr (stageBlock k i j))
      (fun i j => maxEntryNorm hr (A i j)) := by
  exact
    higham13_theorem13_8_active_column_bound_on_active_of_steps
      (fun k i j => maxEntryNorm hr (stageBlock k i j))
      (fun i j => maxEntryNorm hr (A i j))
      (by
        intro i j
        simpa using congrArg (maxEntryNorm hr) (hInit i j))
      (higham13_theorem13_8_active_column_step_on_active_of_mixed_column_mass
        hr stageBlock pivotInv stageInvDiagBound hInfDom hPivotBound hUpdate)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.8:
    source-strength active-stage max-entry bound from the mixed
    matrix-`∞`/max-entry column-mass route. -/
theorem higham13_theorem13_8_active_stage_block_bound_of_mixed_column_mass
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (stageBlock : ℕ → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hInit : ∀ i j : Fin m, stageBlock 0 i j = A i j)
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagMax : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInfDom : SchurStageActiveColumnDom13_7
      (fun k i j => infNorm (stageBlock k i j)) stageInvDiagBound)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    maxEntryNorm hr (stageBlock k i j) ≤ 2 * blockMaxNorm hm hr A := by
  exact
    higham13_theorem13_8_active_stage_block_bound_on_active
      (fun i j => maxEntryNorm hr (A i j)) invDiagBound
      (higham13_blockDiagDomCol_maxEntry_of_infNorm hr A invDiagBound hDomInf)
      hDiagMax
      (fun k i j => maxEntryNorm hr (stageBlock k i j))
      (by
        intro k i j
        exact maxEntryNorm_nonneg hr (stageBlock k i j))
      (higham13_theorem13_8_active_column_bound_on_active_of_mixed_column_mass
        hr A stageBlock pivotInv stageInvDiagBound hInit hInfDom hPivotBound hUpdate)
      (blockMaxNorm hm hr A)
      (fun i j => block_le_blockMaxNorm hm hr A i j)
      k i j hik hjk

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 and Theorem 13.8:
    active-stage max-entry bound for the concrete matrix-product stage table
    from the mixed matrix-`∞`/max-entry column-mass route. -/
theorem higham13_algorithm13_3_matrix_active_stage_bound_of_mixed_column_mass
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (hDomInf : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound)
    (hDiagMax : ∀ j : Fin m, invDiagBound j ≤ maxEntryNorm hr (A j j))
    (hInfDom : SchurStageActiveColumnDom13_7
      (fun k i j => infNorm
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      stageInvDiagBound)
    (hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      infNorm (pivotInv k) * stageInvDiagBound k ⟨k, hk⟩ ≤ 1) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
      maxEntryNorm hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * blockMaxNorm hm hr A := by
  intro k i j _hk hik hjk
  exact
    higham13_theorem13_8_active_stage_block_bound_of_mixed_column_mass
      hm hr A (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv)
      pivotInv invDiagBound stageInvDiagBound
      (by
        intro i j
        exact higham13_algorithm13_3_schurStageBlock_zero A pivotInv i j)
      hDomInf hDiagMax hInfDom hPivotBound
      (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
      k i j hik hjk

/-- **Theorem 13.8, active-stage max bound from local Schur estimates**.
    This combines the active-column-only induction with the local Schur
    one-step norm estimate and active column dominance.  It is closer to the
    book proof than the earlier wrapper that assumed
    `SchurStageActiveColumnStep13_8` directly; the remaining source obligations
    are now the concrete Schur-stage construction, the local Schur norm bound,
    and the Theorem 13.7 active-dominance proof. -/
theorem higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hActiveDom : SchurStageActiveColumnDom13_7 stageNorm stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8 stageNorm pivotInvNorm)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    stageNorm k i j ≤ 2 * normMax := by
  exact higham13_theorem13_8_active_stage_block_bound_on_active_of_steps
    blockNorm invDiagBound hDom hDiagBound stageNorm hInit
    (higham13_theorem13_8_active_column_step_on_active_of_local_schur_bound
      stageNorm stageInvDiagBound pivotInvNorm hStageNonneg hPivotInvNonneg
      hActiveDom hPivotInvBound hLocal)
    hStageNonneg normMax hMax k i j hik hjk

/-- **Theorem 13.8, active-stage max bound from the exact Schur update**.
    This is the closest current proof-layer wrapper to the book's induction:
    the local Schur estimate is proved from the exact active Schur-complement
    update, and the active column dominance premise is obtained from the
    Theorem 13.7 active-stage induction layer.

    The remaining source obligations are the concrete Schur-stage construction,
    pivot inverse data, and the diagonal Schur lower-bound update. -/
theorem higham13_theorem13_8_active_stage_block_bound_of_exact_update {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    stageNorm k i j ≤ 2 * normMax := by
  have hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j := by
    intro k i j
    rw [hStageNorm k i j]
    exact norm_nonneg _
  have hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k := by
    intro k
    rw [hPivotInvNorm k]
    exact norm_nonneg _
  exact higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound
    blockNorm invDiagBound hDom hDiagBound stageNorm stageInvDiagBound
    pivotInvNorm hInitNorm hStageNonneg hPivotInvNonneg
    (higham13_theorem13_7_active_column_dominance_of_exact_update
      blockNorm invDiagBound hDom stageBlock pivotInv stageNorm stageInvDiagBound
      pivotInvNorm hInitNorm hInitInv hStageNorm hPivotInvNorm hPivotInvBound
      hUpdate hDiagUpdate)
    hPivotInvBound
    (higham13_theorem13_8_active_local_schur_bound_of_exact_update
      stageBlock pivotInv stageNorm pivotInvNorm hStageNorm hPivotInvNorm hUpdate)
    normMax hMax k i j hik hjk

/-- **Theorem 13.8, active-stage max bound from exact Schur updates and the
    source reciprocal pivot certificate**.

    This wrapper replaces the pre-multiplied pivot bound in
    `higham13_theorem13_8_active_stage_block_bound_of_exact_update` by the
    source-shaped reciprocal certificate
    `SchurStageActivePivotInvReciprocal13_7`. -/
theorem higham13_theorem13_8_active_stage_block_bound_of_exact_update_reciprocal {m : ℕ}
    {α : Type*} [SeminormedRing α]
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageBlock : ℕ → Fin m → Fin m → α)
    (pivotInv : ℕ → α)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInitNorm : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hInitInv : ∀ j : Fin m, stageInvDiagBound 0 j = invDiagBound j)
    (hStageNorm : ∀ k : ℕ, ∀ i j : Fin m,
      stageNorm k i j = ‖stageBlock k i j‖)
    (hPivotInvNorm : ∀ k : ℕ, pivotInvNorm k = ‖pivotInv k‖)
    (hPivotRecip : SchurStageActivePivotInvReciprocal13_7
      stageInvDiagBound pivotInvNorm)
    (hUpdate : SchurStageActiveExactUpdate13_8 stageBlock pivotInv)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k : ℕ) (i j : Fin m) (hik : k ≤ i.val) (hjk : k ≤ j.val) :
    stageNorm k i j ≤ 2 * normMax := by
  exact higham13_theorem13_8_active_stage_block_bound_of_exact_update
    blockNorm invDiagBound hDom hDiagBound stageBlock pivotInv stageNorm
    stageInvDiagBound pivotInvNorm hInitNorm hInitInv hStageNorm
    hPivotInvNorm
    (higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
      stageInvDiagBound pivotInvNorm hPivotRecip)
    hUpdate hDiagUpdate normMax hMax k i j hik hjk

/-- **Theorem 13.8, staged max-bound wrapper**: once the Schur-stage
    column-sum invariant from the induction is available, block diagonal
    dominance of the original matrix gives the displayed
    `max ‖Aᵢⱼ^(k)‖ ≤ 2 max ‖Aᵢⱼ‖` bound.  This closes the final scalar
    max-bound step; it does not by itself construct the Schur-stage sequence or
    prove the induction invariant. -/
theorem higham13_theorem13_8_stage_block_bound {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (hDiagBound : ∀ j : Fin m, invDiagBound j ≤ blockNorm j j)
    (stageNorm : Fin m → Fin m → Fin m → ℝ)
    (hStageNonneg : ∀ k i j : Fin m, 0 ≤ stageNorm k i j)
    (hStageColumn : SchurStageColumnBound13_8 stageNorm blockNorm)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax)
    (k i j : Fin m) :
    stageNorm k i j ≤ 2 * normMax := by
  have hsingle : stageNorm k i j ≤ ∑ i' : Fin m, stageNorm k i' j :=
    Finset.single_le_sum (fun i' _ => hStageNonneg k i' j) (Finset.mem_univ i)
  have hstage : ∑ i' : Fin m, stageNorm k i' j ≤ ∑ i' : Fin m, blockNorm i' j :=
    hStageColumn k j
  have hcol : ∑ i' : Fin m, blockNorm i' j ≤ 2 * normMax :=
    col_sum_le_twice_diag blockNorm invDiagBound hDom hDiagBound normMax hMax j
  exact le_trans hsingle (le_trans hstage hcol)

end NumStability
