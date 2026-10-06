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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Section01.OperationModels

/-!
# Source.Higham.Chapter13.Theorem06.AssumptionModel

This module formalizes the source-facing Chapter 13 statements for
`Theorem06.AssumptionModel`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3  Theorem 13.6 scalar aggregation
-- ============================================================

/-- Higham, 2nd ed., Chapter 13, Section 13.3, equation (13.14):
    source-facing unpacking of the Algorithm 13.3 step-2 block-solve model. -/
theorem higham13_eq13_14_from_block_solve_spec {r s : Type*} [Fintype r]
    (u c₄ normLhat21 normA11 normE21 : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 : Matrix r r ℝ)
    (h : BlockSolveFirstOrderSpec u c₄ normLhat21 normA11 normE21
      Lhat21 A21 E21 A11) :
    Lhat21 * A11 = A21 + E21 ∧
      BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21 :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Section 13.3, equation (13.15):
    source-facing unpacking of the diagonal-block solve model used in block
    back substitution. -/
theorem higham13_eq13_15_from_diagonal_block_solve_spec {r p : Type*} [Fintype r]
    (u c₅ normUii normDeltaUii : ℝ)
    (Uii DeltaUii : Matrix r r ℝ) (Xhat D : Matrix r p ℝ)
    (h : DiagonalBlockSolveFirstOrderSpec u c₅ normUii normDeltaUii
      Uii DeltaUii Xhat D) :
    (Uii + DeltaUii) * Xhat = D ∧
      DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii :=
  ⟨h.equation, h.norm_bound⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 setup: the local Implementation 1 path exposes exactly the
    block-solve residual model (13.14) and the diagonal-block solve model
    (13.15).  This wrapper is a source-path package, not the omitted proof that
    GEPP/substitution instantiate those assumptions. -/
theorem higham13_algorithm13_3_implementation1_eq13_14_15_from_spec
    {r s p : Type*} [Fintype r]
    (u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ)
    (h : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D) :
    (Lhat21 * A11 = A21 + E21 ∧
        BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21) ∧
      ((Uii + DeltaUii) * Xhat = D ∧
        DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii) :=
  ⟨higham13_eq13_14_from_block_solve_spec
      u c₄ normLhat21 normA11 normE21 Lhat21 A21 E21 A11 h.step2,
    higham13_eq13_15_from_diagonal_block_solve_spec
      u c₅ normUii normDeltaUii Uii DeltaUii Xhat D h.diagonal_solve⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 2:
    source-facing unpacking of the explicit-inverse computed path. -/
theorem higham13_algorithm13_3_implementation2_explicit_inverse_equations
    {r s p : Type*} [Fintype r]
    (A11invHat UiiInvHat : Matrix r r ℝ)
    (Lhat21 A21 : Matrix s r ℝ) (Xhat D : Matrix r p ℝ)
    (h : Algorithm13_3Implementation2ExplicitInverseSpec
      A11invHat UiiInvHat Lhat21 A21 Xhat D) :
    Lhat21 = A21 * A11invHat ∧ Xhat = UiiInvHat * D :=
  ⟨h.step2_as_matmul, h.diagonal_solve_as_matmul⟩

/-- **Theorem 13.6 scalar aggregation** (Demmel--Higham--Schreiber, eq. 13.16).
    Block LU factorization and solve: ‖ΔAᵢ‖ ≤ dₙ · u · (‖A‖ + ‖L̂‖ · ‖Û‖). -/
theorem block_lu_solve_backward_error
    (normΔA_fact normΔA_solve : ℝ)
    (normA normL normU u d_fact d_solve : ℝ)
    (hu : 0 ≤ u) (_hd_f : 0 ≤ d_fact) (_hd_s : 0 ≤ d_solve)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hFact : normΔA_fact ≤ d_fact * u * (normA + normL * normU))
    (hSolve : normΔA_solve ≤ d_solve * u * (normA + normL * normU)) :
    max normΔA_fact normΔA_solve ≤
      max d_fact d_solve * u * (normA + normL * normU) := by
  have hsum : 0 ≤ normA + normL * normU := by linarith [mul_nonneg hL hU]
  have husum : 0 ≤ u * (normA + normL * normU) := mul_nonneg hu hsum
  apply max_le
  · calc normΔA_fact ≤ d_fact * u * (normA + normL * normU) := hFact
      _ ≤ max d_fact d_solve * u * (normA + normL * normU) := by
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left d_fact d_solve) husum]
  · calc normΔA_solve ≤ d_solve * u * (normA + normL * normU) := hSolve
      _ ≤ max d_fact d_solve * u * (normA + normL * normU) := by
          nlinarith [mul_le_mul_of_nonneg_right (le_max_right d_fact d_solve) husum]

/-- Higham, 2nd ed., Chapter 13, Section 13.3, Theorem 13.6/equation
    (13.16), exact conditional scalar wrapper.

    If the implementation-specific factorization and solve estimates have
    already been supplied with constants bounded by a common `d_n`, then both
    displayed Eq.13.16 inequalities, and their max aggregation, hold with
    `d_n`.  This is a conditional algebraic bridge; it does not prove the
    omitted Demmel--Higham--Schreiber implementation analysis. -/
theorem higham13_theorem13_6_eq13_16_from_factor_solve_estimates
    (normΔA_fact normΔA_solve : ℝ)
    (normA normL normU u d_fact d_solve dn : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hFact : normΔA_fact ≤ d_fact * u * (normA + normL * normU))
    (hSolve : normΔA_solve ≤ d_solve * u * (normA + normL * normU)) :
    normΔA_fact ≤ dn * u * (normA + normL * normU) ∧
      normΔA_solve ≤ dn * u * (normA + normL * normU) ∧
      max normΔA_fact normΔA_solve ≤
        dn * u * (normA + normL * normU) := by
  have hsum : 0 ≤ normA + normL * normU := by
    linarith [mul_nonneg hL hU]
  have hscale : 0 ≤ u * (normA + normL * normU) :=
    mul_nonneg hu hsum
  have hFactLeading :
      d_fact * u * (normA + normL * normU) ≤
        dn * u * (normA + normL * normU) := by
    calc
      d_fact * u * (normA + normL * normU)
          = d_fact * (u * (normA + normL * normU)) := by ring
      _ ≤ dn * (u * (normA + normL * normU)) :=
          mul_le_mul_of_nonneg_right hd_fact hscale
      _ = dn * u * (normA + normL * normU) := by ring
  have hSolveLeading :
      d_solve * u * (normA + normL * normU) ≤
        dn * u * (normA + normL * normU) := by
    calc
      d_solve * u * (normA + normL * normU)
          = d_solve * (u * (normA + normL * normU)) := by ring
      _ ≤ dn * (u * (normA + normL * normU)) :=
          mul_le_mul_of_nonneg_right hd_solve hscale
      _ = dn * u * (normA + normL * normU) := by ring
  have hFactDn :
      normΔA_fact ≤ dn * u * (normA + normL * normU) :=
    le_trans hFact hFactLeading
  have hSolveDn :
      normΔA_solve ≤ dn * u * (normA + normL * normU) :=
    le_trans hSolve hSolveLeading
  exact ⟨hFactDn, hSolveDn, max_le hFactDn hSolveDn⟩

/-- **Theorem 13.6 scalar aggregation with `+ O(u^2)` terms**.

    This is the first-order version of `block_lu_solve_backward_error`: if the
    factorization and solve perturbations each satisfy the source-shaped
    first-order bound with explicit second-order witnesses, then their maximum
    satisfies the same bound with the larger constant.  It remains a scalar
    aggregation adapter, not the omitted implementation-facing proof of
    Theorem 13.6. -/
theorem block_lu_solve_backward_error_firstOrder
    (normΔA_fact normΔA_solve : ℝ)
    (normA normL normU u d_fact d_solve : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hFact : FirstOrderLe u (d_fact * u * (normA + normL * normU)) normΔA_fact)
    (hSolve : FirstOrderLe u (d_solve * u * (normA + normL * normU)) normΔA_solve) :
    FirstOrderLe u
      (max d_fact d_solve * u * (normA + normL * normU))
      (max normΔA_fact normΔA_solve) := by
  refine (FirstOrderLe.max hFact hSolve).mono_leading ?_
  have hsum : 0 ≤ normA + normL * normU := by linarith [mul_nonneg hL hU]
  have husum : 0 ≤ u * (normA + normL * normU) := mul_nonneg hu hsum
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_left d_fact d_solve) husum]
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_right d_fact d_solve) husum]

/-- Higham, 2nd ed., Chapter 13, Section 13.3, Theorem 13.6/equation
    (13.16), conditional first-order wrapper.

    If the cited Demmel--Higham--Schreiber implementation analysis has already
    supplied the factorization and solve estimates with constants bounded by a
    common `d_n`, then the two displayed (13.16) inequalities, and their max
    aggregation, hold with that same `d_n`.

    This theorem deliberately keeps those implementation-specific estimates as
    hypotheses; it is a source-facing conditional bridge, not the omitted proof
    of Theorem 13.6 for Algorithm 13.3 Implementation 1. -/
theorem higham13_theorem13_6_eq13_16_firstOrder_from_factor_solve_estimates
    (normΔA_fact normΔA_solve : ℝ)
    (normA normL normU u d_fact d_solve dn : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hFact : FirstOrderLe u (d_fact * u * (normA + normL * normU))
      normΔA_fact)
    (hSolve : FirstOrderLe u (d_solve * u * (normA + normL * normU))
      normΔA_solve) :
    FirstOrderLe u (dn * u * (normA + normL * normU)) normΔA_fact ∧
      FirstOrderLe u (dn * u * (normA + normL * normU)) normΔA_solve ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        (max normΔA_fact normΔA_solve) := by
  have hsum : 0 ≤ normA + normL * normU := by
    linarith [mul_nonneg hL hU]
  have hscale : 0 ≤ u * (normA + normL * normU) :=
    mul_nonneg hu hsum
  have hFactLeading :
      d_fact * u * (normA + normL * normU) ≤
        dn * u * (normA + normL * normU) := by
    calc
      d_fact * u * (normA + normL * normU)
          = d_fact * (u * (normA + normL * normU)) := by ring
      _ ≤ dn * (u * (normA + normL * normU)) :=
          mul_le_mul_of_nonneg_right hd_fact hscale
      _ = dn * u * (normA + normL * normU) := by ring
  have hSolveLeading :
      d_solve * u * (normA + normL * normU) ≤
        dn * u * (normA + normL * normU) := by
    calc
      d_solve * u * (normA + normL * normU)
          = d_solve * (u * (normA + normL * normU)) := by ring
      _ ≤ dn * (u * (normA + normL * normU)) :=
          mul_le_mul_of_nonneg_right hd_solve hscale
      _ = dn * u * (normA + normL * normU) := by ring
  have hFactDn := hFact.mono_leading hFactLeading
  have hSolveDn := hSolve.mono_leading hSolveLeading
  exact ⟨hFactDn, hSolveDn, FirstOrderLe.max_same hFactDn hSolveDn⟩

/-- Conditional proof-source predicate for Higham, 2nd ed., Chapter 13,
    Theorem 13.6 / equation (13.16).

    The book cites Demmel--Higham--Schreiber [326] for the implementation
    analysis behind these two first-order estimates.  This predicate names that
    still-open proof obligation explicitly: it records the factorization and
    solve perturbation estimates that the cited analysis must eventually
    provide for Algorithm 13.3 Implementation 1. -/
structure DemmelHighamSchreiber13_6Estimates
    (u d_fact d_solve normA normL normU normDeltaA_fact normDeltaA_solve : ℝ) :
    Prop where
  factorization :
    FirstOrderLe u (d_fact * u * (normA + normL * normU)) normDeltaA_fact
  solve :
    FirstOrderLe u (d_solve * u * (normA + normL * normU)) normDeltaA_solve

/-- Proof-source boundary for Demmel--Higham--Schreiber [326], Theorem 2.1.

    The recovered Pro audit identified the current hard boundary more sharply
    than the earlier generic `DemmelHighamSchreiber13_6Estimates` predicate:
    a source-faithful formal proof must represent recursive Algorithm 13.3
    execution, the rounded Schur update, block-row right-hand-side formation,
    the local forward/diagonal block solves, block back substitution, local
    solve success, and the max-entry product laws used to aggregate the first
    order estimates.  These fields are intentionally abstract `Prop`s so this
    structure records the proof obligations without inventing unproved
    numerical kernels or hiding them inside the final estimate predicate. -/
structure DemmelHighamSchreiber13_6SourcePath
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop) :
    Prop where
  recursive_execution : recursiveExecution
  schur_update : schurUpdate
  block_row_rhs : blockRowRHS
  forward_substitution : forwardSubstitution
  block_back_substitution : blockBackSubstitution
  local_solve_success : localSolveSuccess
  max_entry_product_laws : maxEntryProductLaws

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 source-path instantiation
    from Higham Algorithm 13.3 Implementation 1's local model.

    The local spec already exposes the two source facts available in Higham's
    text: the step-2 block solve residual (13.14) and the diagonal-block solve
    residual (13.15), each with its first-order scalar bound.  This theorem
    feeds exactly those facts into the corresponding DHS source-path slots.
    Recursive execution, the rounded Schur update, and max-entry product laws
    remain explicit hypotheses, so this does not prove the cited DHS estimates. -/
theorem demmelHighamSchreiber13_6_source_path_from_implementation1_local_spec
    {r s p : Type*} [Fintype r]
    (u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D) :
    DemmelHighamSchreiber13_6SourcePath recursiveExecution schurUpdate
      (Lhat21 * A11 = A21 + E21)
      (BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21)
      ((Uii + DeltaUii) * Xhat = D)
      (DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)
      maxEntryProductLaws := by
  rcases
    higham13_algorithm13_3_implementation1_eq13_14_15_from_spec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D hLocal with
    ⟨hBlock, hDiag⟩
  exact
    ⟨hRecursiveExecution, hSchurUpdate, hBlock.1, hBlock.2, hDiag.1,
      hDiag.2, hMaxEntryProductLaws⟩

/-- Factorization half of the Demmel--Higham--Schreiber [326] source boundary
    used by Higham, Chapter 13, Theorem 13.6.

    The recovered Pro audit recommends keeping the factorization estimate
    separate from the block-solve estimate.  This predicate records the
    recursive execution, rounded Schur-update, and max-entry product-law
    obligations that justify the factorization `FirstOrderLe` estimate; it is
    still a proof-source boundary, not the local reconstruction of [326]. -/
structure DemmelHighamSchreiber13_6FactorizationResult
    (u d_fact normA normL normU normDeltaA_fact : ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop) : Prop where
  recursive_execution : recursiveExecution
  schur_update : schurUpdate
  max_entry_product_laws : maxEntryProductLaws
  factorization :
    FirstOrderLe u (d_fact * u * (normA + normL * normU)) normDeltaA_fact

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 scalar comparison for the
    partitioned factorization leading term.

    Once the source-side factorization coefficients for the `‖A‖` and
    `‖L̂‖‖Û‖` terms are each bounded by the advertised DHS constant `d_fact`,
    the partitioned first-order leading term is bounded by the common
    `d_fact * u * (‖A‖ + ‖L̂‖‖Û‖)` expression.  This closes one of the scalar
    comparison obligations that was previously passed as a raw hypothesis. -/
theorem demmelHighamSchreiber13_6_partitioned_leading_term_le_of_coeff_bounds
    (u δ θ d_fact normA normL normU : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hδ : δ ≤ d_fact) (hθ : θ ≤ d_fact) :
    u * (δ * normA + θ * normL * normU) ≤
      d_fact * u * (normA + normL * normU) := by
  have hLU : 0 ≤ normL * normU := mul_nonneg hL hU
  have hδA : δ * normA ≤ d_fact * normA :=
    mul_le_mul_of_nonneg_right hδ hA
  have hθLU : θ * (normL * normU) ≤ d_fact * (normL * normU) :=
    mul_le_mul_of_nonneg_right hθ hLU
  have hsum :
      δ * normA + θ * normL * normU ≤
        d_fact * (normA + normL * normU) := by
    calc
      δ * normA + θ * normL * normU
          = δ * normA + θ * (normL * normU) := by ring
      _ ≤ d_fact * normA + d_fact * (normL * normU) :=
          add_le_add hδA hθLU
      _ = d_fact * (normA + normL * normU) := by ring
  calc
    u * (δ * normA + θ * normL * normU)
        ≤ u * (d_fact * (normA + normL * normU)) :=
          mul_le_mul_of_nonneg_left hsum hu
    _ = d_fact * u * (normA + normL * normU) := by ring

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 factorization route:
    package a checked partitioned-LU first-order layer into the audited DHS
    factorization-result boundary.

    This is the factorization-side companion to
    `demmelHighamSchreiber13_6_solve_result_from_perturbation_layers`.  It does
    not prove the recursive implementation kernels by itself: recursive
    execution, the rounded Schur update, and the max-entry product laws remain
    explicit source-path hypotheses, and the scalar comparison from the
    partitioned leading term to the advertised DHS constant is explicit. -/
theorem demmelHighamSchreiber13_6_factorization_result_from_partitioned_layer
    {n : Type*} [Fintype n]
    (A DeltaA Lhat Uhat : Matrix n n ℝ)
    (u δ θ d_fact normA normL normU normDeltaA_fact : ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA Lhat Uhat)
    (hLeading :
      u * (δ * normA + θ * normL * normU) ≤
        d_fact * u * (normA + normL * normU)) :
    (Lhat * Uhat = A + DeltaA) ∧
      DemmelHighamSchreiber13_6FactorizationResult
        u d_fact normA normL normU normDeltaA_fact
        recursiveExecution schurUpdate maxEntryProductLaws := by
  exact
    ⟨hSpec.equation,
      ⟨hRecursiveExecution, hSchurUpdate, hMaxEntryProductLaws,
        hSpec.norm_bound.mono_leading hLeading⟩⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 factorization route with the
    scalar leading-term comparison derived from coefficient bounds.

    This is the source-facing companion to
    `demmelHighamSchreiber13_6_factorization_result_from_partitioned_layer`.
    It removes the raw `hLeading` premise when the available source analysis
    provides separate coefficient inequalities `δ ≤ d_fact` and `θ ≤ d_fact`.
    The recursive execution, rounded Schur update, and max-entry product-law
    facts remain explicit implementation obligations. -/
theorem demmelHighamSchreiber13_6_factorization_result_from_partitioned_layer_of_coeff_bounds
    {n : Type*} [Fintype n]
    (A DeltaA Lhat Uhat : Matrix n n ℝ)
    (u δ θ d_fact normA normL normU normDeltaA_fact : ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hδ : δ ≤ d_fact) (hθ : θ ≤ d_fact)
    (hSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA Lhat Uhat) :
    (Lhat * Uhat = A + DeltaA) ∧
      DemmelHighamSchreiber13_6FactorizationResult
        u d_fact normA normL normU normDeltaA_fact
        recursiveExecution schurUpdate maxEntryProductLaws := by
  exact
    demmelHighamSchreiber13_6_factorization_result_from_partitioned_layer
      A DeltaA Lhat Uhat u δ θ d_fact normA normL normU normDeltaA_fact
      recursiveExecution schurUpdate maxEntryProductLaws
      hRecursiveExecution hSchurUpdate hMaxEntryProductLaws hSpec
      (demmelHighamSchreiber13_6_partitioned_leading_term_le_of_coeff_bounds
        u δ θ d_fact normA normL normU hu hA hL hU hδ hθ)

/-- Solve half of the Demmel--Higham--Schreiber [326] source boundary used by
    Higham, Chapter 13, Theorem 13.6.

    This keeps the block-row right-hand-side formation, local forward/diagonal
    solves, block back substitution, solve-success, and max-entry product-law
    obligations visible before they are combined with the factorization half
    into the full DHS Theorem 2.1 result object. -/
structure DemmelHighamSchreiber13_6SolveResult
    (u d_solve normA normL normU normDeltaA_solve : ℝ)
    (blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws : Prop) : Prop where
  block_row_rhs : blockRowRHS
  forward_substitution : forwardSubstitution
  block_back_substitution : blockBackSubstitution
  local_solve_success : localSolveSuccess
  max_entry_product_laws : maxEntryProductLaws
  solve :
    FirstOrderLe u (d_solve * u * (normA + normL * normU)) normDeltaA_solve

/-- Selected-scope DHS forward-substitution branch for Theorem 13.6.

    The strict recovered Pro audit separates the solve proof into a forward
    substitution branch and a block-back-substitution branch before they are
    recombined into the global perturbation identity.  This structure records
    the higher-level forward branch once its exact perturbed equation and
    first-order transported perturbation budget have been proved from a chosen
    triangular-solve execution model. -/
structure DHSBlockForwardSubstitutionFirstOrderSpec {n p : Type*} [Fintype n]
    (u cForward normA normL normU normDeltaLU : ℝ)
    (Lhat DeltaL : Matrix n n ℝ) (Yhat B : Matrix n p ℝ) : Prop where
  equation : (Lhat + DeltaL) * Yhat = B
  norm_bound :
    FirstOrderLe u (cForward * u * (normA + normL * normU)) normDeltaLU

/-- Selected-scope DHS block-back-substitution branch for Theorem 13.6.

    The norm field is the left-transported perturbation budget used by the
    global solve perturbation identity, namely the scalar bound later consumed
    for the `Lhat * DeltaU` term.  A full operational proof should construct
    this spec from the fixed block-row evaluation order, the local
    equation (13.15), and the BLAS/product rounding model. -/
structure DHSBlockBackSubstitutionFirstOrderSpec {n p : Type*} [Fintype n]
    (u cBack normA normL normU normLDeltaU : ℝ)
    (Uhat DeltaU : Matrix n n ℝ) (Xhat Yhat : Matrix n p ℝ) : Prop where
  equation : (Uhat + DeltaU) * Xhat = Yhat
  norm_bound :
    FirstOrderLe u (cBack * u * (normA + normL * normU)) normLDeltaU

/-- Row-analysis boundary for the DHS block-back-substitution proof.

    DHS obtains each row equation by combining the rounded block-row
    right-hand-side formation with the local diagonal solve (13.15), then
    assembles the rows into one perturbation `DeltaU`.  This structure records
    exactly the output needed from that row arithmetic: every assembled row
    equation, a uniform entry bound for `DeltaU`, and its first-order scalar
    budget.  It does not assume the desired global `Lhat * DeltaU` estimate. -/
structure DHSBlockBackSubstitutionRowsFirstOrderSpec {n : ℕ} {p : Type*}
    (u cRows normU rowPerturbBound : ℝ)
    (Uhat DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (Xhat Yhat : Matrix (Fin n) p ℝ) : Prop where
  equation : ∀ i : Fin n, ∀ k : p,
    ∑ j : Fin n, (Uhat i j + DeltaU i j) * Xhat j k = Yhat i k
  entry_bound : ∀ i j : Fin n, |DeltaU i j| ≤ rowPerturbBound
  norm_bound : FirstOrderLe u (cRows * u * normU) rowPerturbBound

/-- Simultaneously assembled strict-upper perturbations for every uniform
    block-back-substitution row.

    Each row has its concrete RHS-formation equation, diagonal-and-lower
    support is zero, and one finite first-order envelope bounds all scalar
    entries.  The diagonal Eq.13.15 perturbations are deliberately kept
    separate for the next composition layer. -/
structure DHSBlockBackSubstitutionUpperRowsFirstOrderSpec
    {m r : ℕ}
    (u cUpper normU upperPerturbBound : ℝ)
    (U DeltaUpper : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ) : Prop where
  support : ∀ i j : Fin m, ¬i.val < j.val → DeltaUpper i j = 0
  rhs_formation : ∀ i : Fin m,
    Dhat i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          (U i j + DeltaUpper i j) * X j =
      Y i
  entry_bound : ∀ i j : Fin m, ∀ s t : Fin r,
    |DeltaUpper i j s t| ≤ upperPerturbBound
  norm_bound : FirstOrderLe u (cUpper * u * normU) upperPerturbBound

/-- Simultaneously assembled source-correct RHS-formation perturbations for
    every uniform block-back-substitution row.

    In contrast to the strict-upper boundary, `DeltaSuffix` may occupy the
    diagonal block because the rounded row subtraction can perturb that
    coefficient.  It remains zero strictly below the diagonal.  The separate
    local Eq.13.15 perturbations are added only in the next composition layer. -/
structure DHSBlockBackSubstitutionSuffixRowsFirstOrderSpec
    {m r : ℕ}
    (u cSuffix normU suffixPerturbBound : ℝ)
    (U DeltaSuffix : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ) : Prop where
  support : ∀ i j : Fin m, j.val < i.val → DeltaSuffix i j = 0
  rhs_formation : ∀ i : Fin m,
    Dhat i +
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          U i j * X j) +
        (∑ j : Fin m, DeltaSuffix i j * X j) = Y i
  entry_bound : ∀ i j : Fin m, ∀ s t : Fin r,
    |DeltaSuffix i j s t| ≤ suffixPerturbBound
  norm_bound :
    FirstOrderLe u (cSuffix * u * normU) suffixPerturbBound

/-- Source-facing fixed-block-row boundary for DHS block back substitution.

    For each uniform block row, `rhs_formation` is the exact relation obtained
    after the rounded products and subtractions have formed `Dhat i` from the
    already computed later solution blocks.  `diagonal_solve` supplies the
    corresponding local equation (13.15), indexed over every diagonal block.
    Keeping those two facts separate makes their subsequent algebraic
    combination auditable.  The entrywise and first-order fields are the
    common perturbation budget delivered by the row arithmetic analysis. -/
structure DHSBlockBackSubstitutionFixedBlockRowsFirstOrderSpec
    {m r : ℕ} {p : Type*}
    (hr : 0 < r)
    (u c₅ cRows normU rowPerturbBound : ℝ)
    (normUii : Fin m → ℝ)
    (Uhat DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Xhat Yhat Dhat : Fin m → Matrix (Fin r) p ℝ) : Prop where
  upper_support : ∀ i j : Fin m, j.val < i.val →
    Uhat i j = 0 ∧ DeltaU i j = 0
  rhs_formation : ∀ i : Fin m,
    Dhat i +
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          (Uhat i j + DeltaU i j) * Xhat j =
      Yhat i
  diagonal_solve : ∀ i : Fin m,
    DiagonalBlockSolveFirstOrderSpec u c₅ (normUii i)
      (maxEntryNorm hr (DeltaU i i))
      (Uhat i i) (DeltaU i i) (Xhat i) (Dhat i)
  entry_bound : ∀ i j : Fin m, ∀ s t : Fin r,
    |DeltaU i j s t| ≤ rowPerturbBound
  norm_bound : FirstOrderLe u (cRows * u * normU) rowPerturbBound

/-- Choose the individually proved strict-upper row witnesses simultaneously
    and aggregate their first-order budgets into one finite envelope. -/
theorem dhs_block_back_upper_rows_spec_from_row_witnesses
    {m r : ℕ}
    (hm : 0 < m)
    (u cUpper normU : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hRows : ∀ i : Fin m,
      ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
          (rowPerturbBound : ℝ),
        Dhat i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              (U i j + DeltaRow j) * X j = Y i ∧
        (∀ j : Fin m, ¬i.val < j.val → DeltaRow j = 0) ∧
        (∀ j : Fin m, ∀ s t : Fin r,
          |DeltaRow j s t| ≤ rowPerturbBound) ∧
        FirstOrderLe u (cUpper * u * normU) rowPerturbBound) :
    ∃ (DeltaUpper : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
        (upperPerturbBound : ℝ),
      DHSBlockBackSubstitutionUpperRowsFirstOrderSpec
        u cUpper normU upperPerturbBound U DeltaUpper X Y Dhat := by
  classical
  choose DeltaRow rowPerturbBound hRow using hRows
  let DeltaUpper : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    fun i j => DeltaRow i j
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  let upperPerturbBound := Finset.univ.sup' hne rowPerturbBound
  refine ⟨DeltaUpper, upperPerturbBound, ?_, ?_, ?_, ?_⟩
  · intro i j hj
    simpa [DeltaUpper] using (hRow i).2.1 j hj
  · intro i
    simpa [DeltaUpper] using (hRow i).1
  · intro i j s t
    calc
      |DeltaUpper i j s t| ≤ rowPerturbBound i := by
        simpa [DeltaUpper] using (hRow i).2.2.1 j s t
      _ ≤ upperPerturbBound := by
        exact Finset.le_sup' rowPerturbBound (Finset.mem_univ i)
  · exact FirstOrderLe.finset_univ_sup' hne rowPerturbBound
      (fun i => (hRow i).2.2.2)

/-- Merge the simultaneously assembled strict-upper perturbations with every
    diagonal Eq.13.15 perturbation.

    The diagonal max-entry norms are enclosed by their own finite supremum.
    Adding that envelope to the upper-row envelope gives the common entrywise
    budget and coefficient `cUpper + c₅` required by the existing fixed-row
    DHS composition theorem. -/
theorem dhs_block_back_fixed_rows_spec_from_upper_rows_and_eq13_15
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (u c₅ cUpper normU upperPerturbBound : ℝ)
    (normUii : Fin m → ℝ)
    (U DeltaUpper : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hc₅ : 0 ≤ c₅)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hUpper : DHSBlockBackSubstitutionUpperRowsFirstOrderSpec
      u cUpper normU upperPerturbBound U DeltaUpper X Y Dhat)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i) (Dhat i)) :
    ∃ (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      DHSBlockBackSubstitutionFixedBlockRowsFirstOrderSpec
        hr u c₅ (cUpper + c₅) normU rowPerturbBound normUii
        U DeltaU X Y Dhat := by
  classical
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  let diagPerturbBound :=
    Finset.univ.sup' hne (fun i => maxEntryNorm hr (DeltaDiag i))
  have hDiagFirstOrder : ∀ i : Fin m,
      FirstOrderLe u (c₅ * u * normU) (maxEntryNorm hr (DeltaDiag i)) := by
    intro i
    apply (hDiagonal i).norm_bound.mono_leading
    exact mul_le_mul_of_nonneg_left (hNormUii i) (mul_nonneg hc₅ hu)
  have hDiagBound : FirstOrderLe u (c₅ * u * normU) diagPerturbBound :=
    FirstOrderLe.finset_univ_sup' hne
      (fun i => maxEntryNorm hr (DeltaDiag i)) hDiagFirstOrder
  have hUpperNonneg : 0 ≤ upperPerturbBound := by
    let i0 : Fin m := ⟨0, hm⟩
    let s0 : Fin r := ⟨0, hr⟩
    exact le_trans (abs_nonneg (DeltaUpper i0 i0 s0 s0))
      (hUpper.entry_bound i0 i0 s0 s0)
  have hDiagNonneg : 0 ≤ diagPerturbBound := by
    let i0 : Fin m := ⟨0, hm⟩
    exact le_trans (maxEntryNorm_nonneg hr (DeltaDiag i0))
      (Finset.le_sup' (fun i => maxEntryNorm hr (DeltaDiag i))
        (Finset.mem_univ i0))
  let DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ := fun i j =>
    if j = i then DeltaDiag i else DeltaUpper i j
  refine ⟨DeltaU, upperPerturbBound + diagPerturbBound,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hji
    have hneji : j ≠ i := by omega
    exact
      ⟨hUUpper i j hji,
        by simp [DeltaU, hneji, hUpper.support i j (by omega)]⟩
  · intro i
    calc
      Dhat i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              (U i j + DeltaU i j) * X j =
          Dhat i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              (U i j + DeltaUpper i j) * X j := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i.val < j.val := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
        have hneji : j ≠ i := by omega
        simp [DeltaU, hneji]
      _ = Y i := hUpper.rhs_formation i
  · intro i
    simpa [DeltaU] using hDiagonal i
  · intro i j s t
    by_cases hji : j = i
    · subst j
      simp only [DeltaU, if_pos]
      calc
        |DeltaDiag i s t| ≤ maxEntryNorm hr (DeltaDiag i) :=
          entry_le_maxEntryNorm hr (DeltaDiag i) s t
        _ ≤ diagPerturbBound :=
          Finset.le_sup' (fun k => maxEntryNorm hr (DeltaDiag k))
            (Finset.mem_univ i)
        _ ≤ upperPerturbBound + diagPerturbBound := by linarith
    · simp only [DeltaU, if_neg hji]
      calc
        |DeltaUpper i j s t| ≤ upperPerturbBound :=
          hUpper.entry_bound i j s t
        _ ≤ upperPerturbBound + diagPerturbBound := by linarith
  · have hCombined := FirstOrderLe.add hUpper.norm_bound hDiagBound le_rfl
    apply hCombined.mono_leading
    exact le_of_eq (by ring)

/-- Source-level result boundary for Demmel--Higham--Schreiber [326],
    Theorem 2.1, equations (2.5)--(2.6), as used by Higham Theorem 13.6.

    This structure is stronger and more auditable than supplying
    `DemmelHighamSchreiber13_6Estimates` alone: it carries the explicit
    execution/proof-source path needed to justify the factorization and solve
    first-order estimates.  A future closure of Theorem 13.6 should prove this
    result from the cited algorithmic model, not assume the estimates directly. -/
structure DemmelHighamSchreiber13_6Theorem2_1Result
    (u d_fact d_solve normA normL normU normDeltaA_fact normDeltaA_solve : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop) :
    Prop where
  source_path :
    DemmelHighamSchreiber13_6SourcePath recursiveExecution schurUpdate
      blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws
  estimates :
    DemmelHighamSchreiber13_6Estimates u d_fact d_solve normA normL normU
      normDeltaA_fact normDeltaA_solve

/-- Build the audited DHS Theorem 2.1 result object from the named estimate
    package and the concrete Algorithm 13.3 Implementation 1 local path.

    Compared with a result object whose source-path fields are arbitrary
    propositions, this version instantiates the block-row/forward-solve and
    block-back/local-solve slots with the actual Eq.13.14 and Eq.13.15
    equation/bound facts supplied by `Algorithm13_3Implementation1LocalSpec`.
    The estimate package is still an explicit hypothesis: this is a source-path
    tightening step, not the omitted DHS implementation analysis. -/
theorem demmelHighamSchreiber13_6_theorem2_1_result_from_estimates_and_implementation1_local_spec
    {r s p : Type*} [Fintype r]
    (u d_fact d_solve normA normL normU normDeltaA_fact normDeltaA_solve : ℝ)
    (c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D)
    (hEst : DemmelHighamSchreiber13_6Estimates
      u d_fact d_solve normA normL normU
      normDeltaA_fact normDeltaA_solve) :
    DemmelHighamSchreiber13_6Theorem2_1Result
      u d_fact d_solve normA normL normU
      normDeltaA_fact normDeltaA_solve
      recursiveExecution schurUpdate
      (Lhat21 * A11 = A21 + E21)
      (BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21)
      ((Uii + DeltaUii) * Xhat = D)
      (DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)
      maxEntryProductLaws := by
  exact
    ⟨demmelHighamSchreiber13_6_source_path_from_implementation1_local_spec
        u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
        Lhat21 A21 E21 A11 Uii DeltaUii Xhat D
        recursiveExecution schurUpdate maxEntryProductLaws
        hRecursiveExecution hSchurUpdate hMaxEntryProductLaws hLocal,
      hEst⟩

/-- Combine the factorization and solve halves of the audited DHS source
    boundary into the full DHS Theorem 2.1 result object used by the existing
    Higham Theorem 13.6 wrappers. -/
theorem demmelHighamSchreiber13_6_theorem2_1_result_from_factorization_solve_results
    (u d_fact d_solve normA normL normU normDeltaA_fact normDeltaA_solve : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (hFact : DemmelHighamSchreiber13_6FactorizationResult
      u d_fact normA normL normU normDeltaA_fact
      recursiveExecution schurUpdate maxEntryProductLaws)
    (hSolve : DemmelHighamSchreiber13_6SolveResult
      u d_solve normA normL normU normDeltaA_solve
      blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws) :
    DemmelHighamSchreiber13_6Theorem2_1Result
      u d_fact d_solve normA normL normU
      normDeltaA_fact normDeltaA_solve
      recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws := by
  exact
    ⟨⟨hFact.recursive_execution, hFact.schur_update, hSolve.block_row_rhs,
        hSolve.forward_substitution, hSolve.block_back_substitution,
        hSolve.local_solve_success, hFact.max_entry_product_laws⟩,
      ⟨hFact.factorization, hSolve.solve⟩⟩

/-- A proved projection from the audited DHS Theorem 2.1 boundary to the older
    estimate predicate used by the scalar Eq.13.16 aggregation wrappers. -/
theorem demmelHighamSchreiber13_6_estimates_from_theorem2_1_result
    (u d_fact d_solve normA normL normU normDeltaA_fact normDeltaA_solve : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (h :
      DemmelHighamSchreiber13_6Theorem2_1Result
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve
        recursiveExecution schurUpdate blockRowRHS forwardSubstitution
        blockBackSubstitution localSolveSuccess maxEntryProductLaws) :
    DemmelHighamSchreiber13_6Estimates u d_fact d_solve normA normL normU
      normDeltaA_fact normDeltaA_solve :=
  h.estimates

/-- Combine the factorization and solve halves directly into the older estimate
    predicate.  This projection is useful for older conditional wrappers while
    preserving the finer source-boundary decomposition in new callers. -/
theorem demmelHighamSchreiber13_6_estimates_from_factorization_solve_results
    (u d_fact d_solve normA normL normU normDeltaA_fact normDeltaA_solve : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (hFact : DemmelHighamSchreiber13_6FactorizationResult
      u d_fact normA normL normU normDeltaA_fact
      recursiveExecution schurUpdate maxEntryProductLaws)
    (hSolve : DemmelHighamSchreiber13_6SolveResult
      u d_solve normA normL normU normDeltaA_solve
      blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws) :
    DemmelHighamSchreiber13_6Estimates u d_fact d_solve normA normL normU
      normDeltaA_fact normDeltaA_solve :=
  ⟨hFact.factorization, hSolve.solve⟩

/-- Higham, 2nd ed., Chapter 13, Theorem 13.6 / equation (13.16), routed
    through the audited DHS Theorem 2.1 source boundary.

    Compared with
    `higham13_theorem13_6_eq13_16_firstOrder_from_DHS_estimates`, this theorem
    asks callers for the stricter DHS result object that records the
    proof-source obligations recovered from the Pro audit.  It is still a
    conditional bridge until that DHS result object is proved locally. -/
theorem higham13_theorem13_6_eq13_16_firstOrder_from_DHS_theorem2_1_result
    (normDeltaA_fact normDeltaA_solve : ℝ)
    (normA normL normU u d_fact d_solve dn : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hDHS :
      DemmelHighamSchreiber13_6Theorem2_1Result
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve
        recursiveExecution schurUpdate blockRowRHS forwardSubstitution
        blockBackSubstitution localSolveSuccess maxEntryProductLaws) :
    FirstOrderLe u (dn * u * (normA + normL * normU)) normDeltaA_fact ∧
      FirstOrderLe u (dn * u * (normA + normL * normU)) normDeltaA_solve ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        (max normDeltaA_fact normDeltaA_solve) := by
  exact
    higham13_theorem13_6_eq13_16_firstOrder_from_factor_solve_estimates
      normDeltaA_fact normDeltaA_solve normA normL normU u
      d_fact d_solve dn hu hA hL hU hd_fact hd_solve
      hDHS.estimates.factorization hDHS.estimates.solve

/-- Higham, 2nd ed., Chapter 13, Theorem 13.6 / equation (13.16), routed
    through the separated factorization and solve halves of the audited DHS
    source boundary. -/
theorem higham13_theorem13_6_eq13_16_firstOrder_from_DHS_factorization_solve_results
    (normDeltaA_fact normDeltaA_solve : ℝ)
    (normA normL normU u d_fact d_solve dn : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hFact : DemmelHighamSchreiber13_6FactorizationResult
      u d_fact normA normL normU normDeltaA_fact
      recursiveExecution schurUpdate maxEntryProductLaws)
    (hSolve : DemmelHighamSchreiber13_6SolveResult
      u d_solve normA normL normU normDeltaA_solve
      blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws) :
    FirstOrderLe u (dn * u * (normA + normL * normU)) normDeltaA_fact ∧
      FirstOrderLe u (dn * u * (normA + normL * normU)) normDeltaA_solve ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        (max normDeltaA_fact normDeltaA_solve) := by
  exact
    higham13_theorem13_6_eq13_16_firstOrder_from_DHS_theorem2_1_result
      normDeltaA_fact normDeltaA_solve normA normL normU u
      d_fact d_solve dn recursiveExecution schurUpdate blockRowRHS
      forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws hu hA hL hU hd_fact hd_solve
      (demmelHighamSchreiber13_6_theorem2_1_result_from_factorization_solve_results
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve recursiveExecution schurUpdate
        blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
        maxEntryProductLaws hFact hSolve)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 / equation (13.16), routed through the audited DHS Theorem 2.1
    source boundary.

    The local specification exposes equations (13.14) and (13.15).  The DHS
    result object records the additional recursive execution, Schur-update,
    triangular-solve, block-back-substitution, successful-solve, and max-entry
    product-law obligations that still have to be proved from the cited source. -/
theorem higham13_theorem13_6_implementation1_from_DHS_theorem2_1_result
    {r s p : Type*} [Fintype r]
    (u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ)
    (normDeltaA_fact normDeltaA_solve : ℝ)
    (normA normL normU d_fact d_solve dn : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D)
    (hDHS :
      DemmelHighamSchreiber13_6Theorem2_1Result
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve
        recursiveExecution schurUpdate blockRowRHS forwardSubstitution
        blockBackSubstitution localSolveSuccess maxEntryProductLaws) :
    ((Lhat21 * A11 = A21 + E21 ∧
        BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21) ∧
      ((Uii + DeltaUii) * Xhat = D ∧
        DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)) ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        normDeltaA_fact ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        normDeltaA_solve ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        (max normDeltaA_fact normDeltaA_solve) := by
  exact
    ⟨higham13_algorithm13_3_implementation1_eq13_14_15_from_spec
        u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
        Lhat21 A21 E21 A11 Uii DeltaUii Xhat D hLocal,
      higham13_theorem13_6_eq13_16_firstOrder_from_DHS_theorem2_1_result
        normDeltaA_fact normDeltaA_solve normA normL normU u
        d_fact d_solve dn recursiveExecution schurUpdate blockRowRHS
        forwardSubstitution blockBackSubstitution localSolveSuccess
        maxEntryProductLaws hu hA hL hU hd_fact hd_solve hDHS⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 / equation (13.16), routed through the audited DHS estimate
    package and the concrete local Eq.13.14/Eq.13.15 source path.

    This is the implementation-facing companion to
    `demmelHighamSchreiber13_6_theorem2_1_result_from_estimates_and_implementation1_local_spec`.
    It prevents the DHS source-path slots from being arbitrary at the final
    wrapper: the block-row and diagonal-block local facts are exactly those
    unpacked from `Algorithm13_3Implementation1LocalSpec`.  The cited DHS
    first-order estimates themselves remain explicit hypotheses. -/
theorem higham13_theorem13_6_implementation1_from_DHS_estimates_and_implementation1_local_spec
    {r s p : Type*} [Fintype r]
    (u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ)
    (normDeltaA_fact normDeltaA_solve : ℝ)
    (normA normL normU d_fact d_solve dn : ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D)
    (hEst : DemmelHighamSchreiber13_6Estimates
      u d_fact d_solve normA normL normU
      normDeltaA_fact normDeltaA_solve) :
    ((Lhat21 * A11 = A21 + E21 ∧
        BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21) ∧
      ((Uii + DeltaUii) * Xhat = D ∧
        DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)) ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        normDeltaA_fact ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        normDeltaA_solve ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        (max normDeltaA_fact normDeltaA_solve) := by
  exact
    higham13_theorem13_6_implementation1_from_DHS_theorem2_1_result
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D
      normDeltaA_fact normDeltaA_solve normA normL normU
      d_fact d_solve dn recursiveExecution schurUpdate
      (Lhat21 * A11 = A21 + E21)
      (BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21)
      ((Uii + DeltaUii) * Xhat = D)
      (DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)
      maxEntryProductLaws hu hA hL hU hd_fact hd_solve hLocal
      (demmelHighamSchreiber13_6_theorem2_1_result_from_estimates_and_implementation1_local_spec
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve c₄ c₅ normLhat21 normA11
        normE21 normUii normDeltaUii Lhat21 A21 E21 A11 Uii
        DeltaUii Xhat D recursiveExecution schurUpdate maxEntryProductLaws
        hRecursiveExecution hSchurUpdate hMaxEntryProductLaws hLocal hEst)

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 / equation (13.16), routed through the separated
    factorization and solve halves of the audited DHS source boundary. -/
theorem higham13_theorem13_6_implementation1_from_DHS_factorization_solve_results
    {r s p : Type*} [Fintype r]
    (u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ)
    (normDeltaA_fact normDeltaA_solve : ℝ)
    (normA normL normU d_fact d_solve dn : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D)
    (hFact : DemmelHighamSchreiber13_6FactorizationResult
      u d_fact normA normL normU normDeltaA_fact
      recursiveExecution schurUpdate maxEntryProductLaws)
    (hSolve : DemmelHighamSchreiber13_6SolveResult
      u d_solve normA normL normU normDeltaA_solve
      blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws) :
    ((Lhat21 * A11 = A21 + E21 ∧
        BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21) ∧
      ((Uii + DeltaUii) * Xhat = D ∧
        DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)) ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        normDeltaA_fact ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        normDeltaA_solve ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        (max normDeltaA_fact normDeltaA_solve) := by
  exact
    higham13_theorem13_6_implementation1_from_DHS_theorem2_1_result
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii Xhat D
      normDeltaA_fact normDeltaA_solve normA normL normU
      d_fact d_solve dn recursiveExecution schurUpdate blockRowRHS
      forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws hu hA hL hU hd_fact hd_solve hLocal
      (demmelHighamSchreiber13_6_theorem2_1_result_from_factorization_solve_results
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve recursiveExecution schurUpdate
        blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
        maxEntryProductLaws hFact hSolve)

end NumStability
