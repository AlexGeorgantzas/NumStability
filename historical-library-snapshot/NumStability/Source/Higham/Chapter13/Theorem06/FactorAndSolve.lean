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
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Algorithms.LinearSystems.LU.BlockLU.ResidualLifting
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SolveError
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter13.Section01.OperationModels
import NumStability.Source.Higham.Chapter13.Theorem06.AssumptionModel

/-!
# Source.Higham.Chapter13.Theorem06.FactorAndSolve

This module formalizes the source-facing Chapter 13 statements for
`Theorem06.FactorAndSolve`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Demmel--Higham--Schreiber [326], Theorem 2.1 solve route:
    exact LU-solve perturbation identity.

    If the factorization residual is `Lhat * Uhat = A + E`, the forward solve
    supplies `(Lhat + DeltaL) * Yhat = B`, and block back substitution supplies
    `(Uhat + DeltaU) * Xhat = Yhat`, then the final solve is exact for the
    perturbed coefficient matrix
    `A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU)`.  This is the
    algebraic composition step named by the recovered DHS/Pro answer; it is not
    by itself the full first-order solve estimate. -/
theorem dhs_lu_solve_perturbation_identity
    {n p : Type*} [Fintype n]
    (A E Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (Xhat B Yhat : Matrix n p ℝ)
    (hFact : Lhat * Uhat = A + E)
    (hForward : (Lhat + DeltaL) * Yhat = B)
    (hBack : (Uhat + DeltaU) * Xhat = Yhat) :
    (A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU)) * Xhat =
      B := by
  have hProduct :
      A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU) =
        (Lhat + DeltaL) * (Uhat + DeltaU) := by
    calc
      A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU)
          = (A + E) + (DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU) := by
            abel
      _ = Lhat * Uhat +
            (DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU) := by
            rw [← hFact]
      _ = (Lhat + DeltaL) * (Uhat + DeltaU) := by
            rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
            abel
  calc
    (A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU)) * Xhat
        = ((Lhat + DeltaL) * (Uhat + DeltaU)) * Xhat := by rw [hProduct]
    _ = (Lhat + DeltaL) * ((Uhat + DeltaU) * Xhat) := by
        rw [Matrix.mul_assoc]
    _ = (Lhat + DeltaL) * Yhat := by rw [hBack]
    _ = B := hForward

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 solve route:
    scalar first-order aggregation for the exact LU-solve perturbation identity.

    The exact perturbation in `dhs_lu_solve_perturbation_identity` contains the
    factorization residual `E`, the forward-solve term `DeltaL * Uhat`, the
    back-substitution term `Lhat * DeltaU`, and the cross term
    `DeltaL * DeltaU`.  If the first three satisfy source-shaped first-order
    bounds and the cross term is explicitly second order, then the total solve
    perturbation satisfies the common first-order bound. -/
theorem dhs_lu_solve_perturbation_firstOrder
    (normDeltaSolve normE normDeltaLU normLDeltaU normDeltaLDeltaU
      normA normL normU u cFact cForward cBack cSolve : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc : cFact + cForward + cBack ≤ cSolve)
    (hE : FirstOrderLe u (cFact * u * (normA + normL * normU)) normE)
    (hDeltaLU : FirstOrderLe u
      (cForward * u * (normA + normL * normU)) normDeltaLU)
    (hLDeltaU : FirstOrderLe u
      (cBack * u * (normA + normL * normU)) normLDeltaU)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaSolve ≤ normE + normDeltaLU + normLDeltaU + normDeltaLDeltaU) :
    FirstOrderLe u (cSolve * u * (normA + normL * normU)) normDeltaSolve := by
  have h12 : FirstOrderLe u
      (cFact * u * (normA + normL * normU) +
        cForward * u * (normA + normL * normU))
      (normE + normDeltaLU) :=
    FirstOrderLe.add hE hDeltaLU le_rfl
  have h123 : FirstOrderLe u
      ((cFact * u * (normA + normL * normU) +
          cForward * u * (normA + normL * normU)) +
        cBack * u * (normA + normL * normU))
      (normE + normDeltaLU + normLDeltaU) :=
    FirstOrderLe.add h12 hLDeltaU (by linarith)
  have hAll : FirstOrderLe u
      (((cFact * u * (normA + normL * normU) +
          cForward * u * (normA + normL * normU)) +
        cBack * u * (normA + normL * normU)) + 0)
      normDeltaSolve :=
    FirstOrderLe.add h123 hDeltaLDeltaU (by linarith)
  refine hAll.mono_leading ?_
  have hsum : 0 ≤ normA + normL * normU := by
    linarith [mul_nonneg hL hU]
  have hscale : 0 ≤ u * (normA + normL * normU) :=
    mul_nonneg hu hsum
  calc
    ((cFact * u * (normA + normL * normU) +
          cForward * u * (normA + normL * normU)) +
        cBack * u * (normA + normL * normU)) + 0
        = (cFact + cForward + cBack) * (u * (normA + normL * normU)) := by
          ring
    _ ≤ cSolve * (u * (normA + normL * normU)) :=
        mul_le_mul_of_nonneg_right hc hscale
    _ = cSolve * u * (normA + normL * normU) := by ring

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 forward-substitution branch,
    selected-scope spec constructor.

    The full operational theorem should derive this spec from a fixed forward
    substitution execution and rounding model.  This constructor is the
    reusable boundary used by the higher-level DHS solve packaging once that
    equation and first-order perturbation budget are available. -/
theorem dhs_block_forward_substitution_firstOrder
    {n p : Type*} [Fintype n]
    (u cForward normA normL normU normDeltaLU : ℝ)
    (Lhat DeltaL : Matrix n n ℝ) (Yhat B : Matrix n p ℝ)
    (hEquation : (Lhat + DeltaL) * Yhat = B)
    (hBound :
      FirstOrderLe u (cForward * u * (normA + normL * normU)) normDeltaLU) :
    DHSBlockForwardSubstitutionFirstOrderSpec
      u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B :=
  ⟨hEquation, hBound⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 forward branch for the
    conventional flattened forward-substitution algorithm and one right-hand
    side.

    The Chapter 8 componentwise backward-error theorem supplies one common
    coefficient perturbation `DeltaL` for this single column.  Its exact
    perturbed solve equation and the max-entry product estimate for
    `DeltaL * Uhat` give the selected DHS forward spec with coefficient `n^2`.
    The DHS solve theorem is naturally a one-right-hand-side statement; no
    stronger common-perturbation claim for simultaneous right-hand sides is
    made here. -/
theorem
    dhs_block_forward_substitution_firstOrder_from_conventional_forwardSub_single_rhs
    {n : ℕ}
    (fp : FPModel) (hn : 0 < n) (normA : ℝ)
    (Lhat Uhat : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hA : 0 ≤ normA)
    (hdiag : ∀ i : Fin n, Lhat i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → Lhat i j = 0)
    (hγ : gammaValid fp n) :
    ∃ DeltaL : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |Lhat i j|) ∧
        DHSBlockForwardSubstitutionFirstOrderSpec
          fp.u ((n : ℝ) ^ 2)
          normA (maxEntryNorm hn Lhat) (maxEntryNorm hn Uhat)
          (maxEntryNorm hn (DeltaL * Uhat))
          Lhat DeltaL
          (fun i (_j : Fin 1) => fl_forwardSub fp n Lhat b i)
          (fun i (_j : Fin 1) => b i) := by
  rcases forwardSub_backward_error fp n Lhat b hdiag hlower hγ with
    ⟨DeltaLRaw, hDeltaL, hEquation⟩
  let DeltaL : Matrix (Fin n) (Fin n) ℝ := DeltaLRaw
  refine ⟨DeltaL, ?_, dhs_block_forward_substitution_firstOrder
    fp.u ((n : ℝ) ^ 2)
    normA (maxEntryNorm hn Lhat) (maxEntryNorm hn Uhat)
    (maxEntryNorm hn (DeltaL * Uhat))
    Lhat DeltaL
    (fun i (_j : Fin 1) => fl_forwardSub fp n Lhat b i)
    (fun i (_j : Fin 1) => b i) ?_ ?_⟩
  · intro i j
    simpa [DeltaL] using hDeltaL i j
  · ext i j
    simpa [DeltaL, Matrix.mul_apply] using hEquation i
  · have hnormL : 0 ≤ maxEntryNorm hn Lhat := maxEntryNorm_nonneg hn Lhat
    have hnormU : 0 ≤ maxEntryNorm hn Uhat := maxEntryNorm_nonneg hn Uhat
    have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hγ
    have hDeltaNorm :
        maxEntryNorm hn DeltaL ≤ gamma fp n * maxEntryNorm hn Lhat := by
      apply maxEntryNorm_le_of_entry_le_bound
      intro i j
      calc
        |DeltaL i j| ≤ gamma fp n * |Lhat i j| := by
          simpa [DeltaL] using hDeltaL i j
        _ ≤ gamma fp n * maxEntryNorm hn Lhat :=
          mul_le_mul_of_nonneg_left (entry_le_maxEntryNorm hn Lhat i j) hgamma
    have hProduct :
        maxEntryNorm hn (DeltaL * Uhat) ≤
          gamma fp n * (n : ℝ) * maxEntryNorm hn Lhat *
            maxEntryNorm hn Uhat := by
      calc
        maxEntryNorm hn (DeltaL * Uhat) ≤
            (n : ℝ) * maxEntryNorm hn DeltaL * maxEntryNorm hn Uhat :=
          maxEntryNorm_matrix_mul_le_dim hn DeltaL Uhat
        _ ≤ (n : ℝ) * (gamma fp n * maxEntryNorm hn Lhat) *
              maxEntryNorm hn Uhat := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDeltaNorm (Nat.cast_nonneg n)) hnormU
        _ = gamma fp n * (n : ℝ) * maxEntryNorm hn Lhat *
              maxEntryNorm hn Uhat := by ring
    have hFirst : FirstOrderLe fp.u
        (((n : ℝ) ^ 2) * fp.u * maxEntryNorm hn Lhat *
          maxEntryNorm hn Uhat)
        (maxEntryNorm hn (DeltaL * Uhat)) :=
      FirstOrderLe.of_gamma_dim_mul fp n hγ hnormL hnormU hProduct
    refine hFirst.mono_leading ?_
    have hscale :
        maxEntryNorm hn Lhat * maxEntryNorm hn Uhat ≤
          normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat := by
      linarith
    have hfactor : 0 ≤ ((n : ℝ) ^ 2) * fp.u :=
      mul_nonneg (sq_nonneg (n : ℝ)) fp.u_nonneg
    calc
      ((n : ℝ) ^ 2) * fp.u * maxEntryNorm hn Lhat * maxEntryNorm hn Uhat =
          (((n : ℝ) ^ 2) * fp.u) *
            (maxEntryNorm hn Lhat * maxEntryNorm hn Uhat) := by ring
      _ ≤ (((n : ℝ) ^ 2) * fp.u) *
            (normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat) :=
          mul_le_mul_of_nonneg_left hscale hfactor
      _ = ((n : ℝ) ^ 2) * fp.u *
            (normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat) := by ring

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 forward-side residual scale:
    scalar comparison from local Eq.13.14 coefficients.

    The recovered strict DHS audit separates the local block-solve residual
    from the global forward-substitution branch.  This lemma discharges the
    scalar leading-term comparison when the source analysis supplies a
    coefficient bound `c₄ <= cForward` and a norm comparison from the local
    residual product `‖Lhat21‖‖A11‖` into the global DHS scale
    `‖A‖ + ‖Lhat‖‖Uhat‖`. -/
theorem dhs_block_forward_residual_leading_term_le_of_coeff_bounds
    (u c₄ cForward normA normL normU normLhat21 normA11 : ℝ)
    (hu : 0 ≤ u) (hc₄_nonneg : 0 ≤ c₄)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc₄_le : c₄ ≤ cForward)
    (hLocalScale : normLhat21 * normA11 ≤ normA + normL * normU) :
    c₄ * u * normLhat21 * normA11 ≤
      cForward * u * (normA + normL * normU) := by
  have hsum : 0 ≤ normA + normL * normU := by
    linarith [mul_nonneg hL hU]
  have hc₄u : 0 ≤ c₄ * u := mul_nonneg hc₄_nonneg hu
  have hscale : 0 ≤ u * (normA + normL * normU) :=
    mul_nonneg hu hsum
  calc
    c₄ * u * normLhat21 * normA11
        = (c₄ * u) * (normLhat21 * normA11) := by ring
    _ ≤ (c₄ * u) * (normA + normL * normU) :=
        mul_le_mul_of_nonneg_left hLocalScale hc₄u
    _ = c₄ * (u * (normA + normL * normU)) := by ring
    _ ≤ cForward * (u * (normA + normL * normU)) :=
        mul_le_mul_of_nonneg_right hc₄_le hscale
    _ = cForward * u * (normA + normL * normU) := by ring

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 forward-side residual scale
    from Higham's local block solve specification (equation 13.14).

    Equation (13.14) gives a residual equation
    `Lhat21 * A11 = A21 + E21` and a local first-order bound for `E21`.
    It is not, by itself, the full DHS global forward-substitution perturbation
    equation `(Lhat + DeltaL) * Yhat = B`.  This adapter therefore transports
    only the residual equation and scalar budget to the global DHS
    forward-branch leading scale, keeping the operational forward-substitution
    equation and any product/value laws as separate obligations. -/
theorem dhs_block_forward_residual_firstOrder_from_block_solve_spec
    {r s : Type*} [Fintype r]
    (u c₄ cForward normA normL normU normLhat21 normA11 normE21 : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 : Matrix r r ℝ)
    (hLeading :
      c₄ * u * normLhat21 * normA11 ≤
        cForward * u * (normA + normL * normU))
    (hSpec :
      BlockSolveFirstOrderSpec u c₄ normLhat21 normA11 normE21
        Lhat21 A21 E21 A11) :
    (Lhat21 * A11 = A21 + E21) ∧
      FirstOrderLe u (cForward * u * (normA + normL * normU)) normE21 :=
  ⟨hSpec.equation, hSpec.norm_bound.mono_leading hLeading⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 forward-side residual scale
    from Higham's local block solve specification, with the scalar comparison
    derived from source-shaped coefficient and norm comparisons. -/
theorem dhs_block_forward_residual_firstOrder_from_block_solve_spec_of_coeff_bounds
    {r s : Type*} [Fintype r]
    (u c₄ cForward normA normL normU normLhat21 normA11 normE21 : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 : Matrix r r ℝ)
    (hu : 0 ≤ u) (hc₄_nonneg : 0 ≤ c₄)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc₄_le : c₄ ≤ cForward)
    (hLocalScale : normLhat21 * normA11 ≤ normA + normL * normU)
    (hSpec :
      BlockSolveFirstOrderSpec u c₄ normLhat21 normA11 normE21
        Lhat21 A21 E21 A11) :
    (Lhat21 * A11 = A21 + E21) ∧
      FirstOrderLe u (cForward * u * (normA + normL * normU)) normE21 :=
  dhs_block_forward_residual_firstOrder_from_block_solve_spec
    u c₄ cForward normA normL normU normLhat21 normA11 normE21
    Lhat21 A21 E21 A11
    (dhs_block_forward_residual_leading_term_le_of_coeff_bounds
      u c₄ cForward normA normL normU normLhat21 normA11
      hu hc₄_nonneg hA hL hU hc₄_le hLocalScale)
    hSpec

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 block-back-substitution
    branch, selected-scope spec constructor.

    This is the named branch requested by the recovered strict DHS audit.  It
    does not replace the missing row-by-row implementation proof; instead it
    records the exact perturbed back-substitution equation and the transported
    first-order budget that the final solve perturbation theorem consumes. -/
theorem dhs_block_back_substitution_firstOrder
    {n p : Type*} [Fintype n]
    (u cBack normA normL normU normLDeltaU : ℝ)
    (Uhat DeltaU : Matrix n n ℝ) (Xhat Yhat : Matrix n p ℝ)
    (hEquation : (Uhat + DeltaU) * Xhat = Yhat)
    (hBound :
      FirstOrderLe u (cBack * u * (normA + normL * normU)) normLDeltaU) :
    DHSBlockBackSubstitutionFirstOrderSpec
      u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat :=
  ⟨hEquation, hBound⟩

/-- Assemble the DHS row-analysis boundary into the selected global
    block-back-substitution branch.

    The row equations give `(Uhat + DeltaU) * Xhat = Yhat`.  The uniform entry
    budget bounds `‖DeltaU‖max`; one max-entry product estimate then transports
    it to the `‖Lhat * DeltaU‖max` quantity consumed by the solve perturbation.
    The displayed comparison `(n : ℝ) * cRows <= cBack` accounts for that
    product's dimension factor. -/
theorem
    dhs_block_back_substitution_firstOrder_from_rows_spec_of_coeff_bounds
    {n : ℕ} {p : Type*}
    (hn : 0 < n)
    (u cRows cBack normA normL normU rowPerturbBound : ℝ)
    (Lhat Uhat DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (Xhat Yhat : Matrix (Fin n) p ℝ)
    (hu : 0 ≤ u) (hcRows : 0 ≤ cRows)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hLhat : maxEntryNorm hn Lhat ≤ normL)
    (hc : (n : ℝ) * cRows ≤ cBack)
    (hRows : DHSBlockBackSubstitutionRowsFirstOrderSpec
      u cRows normU rowPerturbBound Uhat DeltaU Xhat Yhat) :
    DHSBlockBackSubstitutionFirstOrderSpec
      u cBack normA normL normU (maxEntryNorm hn (Lhat * DeltaU))
      Uhat DeltaU Xhat Yhat := by
  have hDeltaNorm : maxEntryNorm hn DeltaU ≤ rowPerturbBound :=
    maxEntryNorm_le_of_entry_le_bound hn DeltaU rowPerturbBound hRows.entry_bound
  have hProduct :
      maxEntryNorm hn (Lhat * DeltaU) ≤
        rowPerturbBound * ((n : ℝ) * normL) := by
    calc
      maxEntryNorm hn (Lhat * DeltaU) ≤
          (n : ℝ) * maxEntryNorm hn Lhat * maxEntryNorm hn DeltaU :=
        maxEntryNorm_matrix_mul_le_dim hn Lhat DeltaU
      _ ≤ (n : ℝ) * maxEntryNorm hn Lhat * rowPerturbBound :=
        mul_le_mul_of_nonneg_left hDeltaNorm
          (mul_nonneg (Nat.cast_nonneg n) (maxEntryNorm_nonneg hn Lhat))
      _ ≤ (n : ℝ) * normL * rowPerturbBound := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLhat (Nat.cast_nonneg n))
          (le_trans (maxEntryNorm_nonneg hn DeltaU) hDeltaNorm)
      _ = rowPerturbBound * ((n : ℝ) * normL) := by ring
  have hScale : normL * normU ≤ normA + normL * normU := by linarith
  have hCoeffNonneg : 0 ≤ (n : ℝ) * cRows :=
    mul_nonneg (Nat.cast_nonneg n) hcRows
  have hcBack : 0 ≤ cBack := le_trans hCoeffNonneg hc
  have hLeading :
      (cRows * u * normU) * ((n : ℝ) * normL) ≤
        cBack * u * (normA + normL * normU) := by
    have hbase : 0 ≤ u * (normL * normU) :=
      mul_nonneg hu (mul_nonneg hL hU)
    calc
      (cRows * u * normU) * ((n : ℝ) * normL) =
          ((n : ℝ) * cRows) * (u * (normL * normU)) := by ring
      _ ≤ cBack * (u * (normL * normU)) :=
        mul_le_mul_of_nonneg_right hc hbase
      _ = (cBack * u) * (normL * normU) := by ring
      _ ≤ (cBack * u) * (normA + normL * normU) :=
        mul_le_mul_of_nonneg_left hScale (mul_nonneg hcBack hu)
      _ = cBack * u * (normA + normL * normU) := by ring
  refine ⟨?_, ?_⟩
  · ext i k
    simpa [Matrix.mul_apply] using hRows.equation i k
  · exact
      (hRows.norm_bound.bound_mul_nonneg_right
        (mul_nonneg (Nat.cast_nonneg n) hL) hProduct).mono_leading hLeading

/-- Combine every fixed block-row right-hand-side relation with its local
    equation (13.15), then flatten the uniform block system into the global DHS
    row certificate.

    This theorem closes the exact algebra and representation layer between the
    source's two rowwise ingredients.  Constructing the fixed-row spec from the
    rounded block products/subtractions and the concrete local solver remains
    the numerical-analysis obligation. -/
theorem
    dhs_block_back_substitution_rows_spec_from_fixed_block_rows_and_eq13_15
    {m r : ℕ} {p : Type*}
    (hr : 0 < r)
    (u c₅ cRows normU rowPerturbBound : ℝ)
    (normUii : Fin m → ℝ)
    (Uhat DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Xhat Yhat Dhat : Fin m → Matrix (Fin r) p ℝ)
    (h : DHSBlockBackSubstitutionFixedBlockRowsFirstOrderSpec
      hr u c₅ cRows normU rowPerturbBound normUii
      Uhat DeltaU Xhat Yhat Dhat) :
    DHSBlockBackSubstitutionRowsFirstOrderSpec
      u cRows normU rowPerturbBound
      (blockMatrixFlatFin Uhat) (blockMatrixFlatFin DeltaU)
      (blockMatrixRowsFlatFin Xhat) (blockMatrixRowsFlatFin Yhat) := by
  have hBlockEquation : ∀ i : Fin m,
      (∑ j : Fin m, (Uhat i j + DeltaU i j) * Xhat j) = Yhat i := by
    intro i
    let f : Fin m → Matrix (Fin r) p ℝ :=
      fun j => (Uhat i j + DeltaU i j) * Xhat j
    have hbelow :
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬i.val ≤ j.val), f j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j.val < i.val := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hj
      rcases h.upper_support i j hji with ⟨hU, hDelta⟩
      simp only [f]
      rw [hU, hDelta]
      simp
    have htailset :
        Finset.univ.filter (fun j : Fin m => i.val ≤ j.val) \ {i} =
          Finset.univ.filter (fun j : Fin m => i.val < j.val) := by
      ext j
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      omega
    have hge :
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val), f j) =
          Dhat i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val), f j := by
      calc
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val), f j) =
            f i +
              ∑ j ∈ (Finset.univ.filter
                (fun j : Fin m => i.val ≤ j.val)) \ {i}, f j := by
          exact Finset.sum_eq_add_sum_diff_singleton i f (by simp)
        _ = f i +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val), f j := by
          rw [htailset]
        _ = Dhat i +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val), f j := by
          have hdiag : f i = Dhat i := by
            simpa [f] using (h.diagonal_solve i).equation
          rw [hdiag]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin m => i.val ≤ j.val)]
    rw [hbelow, add_zero, hge]
    exact h.rhs_formation i
  refine ⟨?_, ?_, h.norm_bound⟩
  · intro is k
    let q := finProdFinEquiv.symm is
    have his : finProdFinEquiv q = is := finProdFinEquiv.apply_symm_apply is
    calc
      (∑ jt : Fin (m * r),
          (blockMatrixFlatFin Uhat is jt + blockMatrixFlatFin DeltaU is jt) *
            blockMatrixRowsFlatFin Xhat jt k) =
          ∑ jt : Fin (m * r),
            (blockMatrixFlatFin Uhat (finProdFinEquiv q) jt +
                blockMatrixFlatFin DeltaU (finProdFinEquiv q) jt) *
              blockMatrixRowsFlatFin Xhat jt k := by rw [his]
      _ = ∑ j : Fin m,
            ((Uhat q.1 j + DeltaU q.1 j) * Xhat j) q.2 k :=
        blockMatrixFlatFin_add_mul_blockMatrixRowsFlatFin_apply
          Uhat DeltaU Xhat q.1 q.2 k
      _ = Yhat q.1 q.2 k := by
        have hrow := congrFun (congrFun (hBlockEquation q.1) q.2) k
        simpa only [Matrix.sum_apply] using hrow
      _ = blockMatrixRowsFlatFin Yhat is k := by
        simp [blockMatrixRowsFlatFin, q]
  · intro is jt
    simpa [blockMatrixFlatFin] using
      h.entry_bound (finProdFinEquiv.symm is).1
        (finProdFinEquiv.symm jt).1 (finProdFinEquiv.symm is).2
        (finProdFinEquiv.symm jt).2

/-- Source-shaped fixed block rows and every local equation (13.15) imply the
    selected global DHS back-substitution branch.

    The first theorem above performs row algebra and block flattening; the
    existing row assembler supplies the max-entry product transport through
    `Lhat`.  Thus the only remaining premise at this layer is the checked
    fixed-row arithmetic certificate itself, plus explicit scalar coefficient
    comparisons. -/
theorem
    dhs_block_back_substitution_firstOrder_from_fixed_block_rows_and_eq13_15_of_coeff_bounds
    {m r : ℕ} {p : Type*}
    (hm : 0 < m) (hr : 0 < r)
    (u c₅ cRows cBack normA normL normU rowPerturbBound : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat Uhat DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Xhat Yhat Dhat : Fin m → Matrix (Fin r) p ℝ)
    (hu : 0 ≤ u) (hcRows : 0 ≤ cRows)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : ((m * r : ℕ) : ℝ) * cRows ≤ cBack)
    (hRows : DHSBlockBackSubstitutionFixedBlockRowsFirstOrderSpec
      hr u c₅ cRows normU rowPerturbBound normUii
      Uhat DeltaU Xhat Yhat Dhat) :
    DHSBlockBackSubstitutionFirstOrderSpec
      u cBack normA normL normU
      (maxEntryNorm (Nat.mul_pos hm hr)
        (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
      (blockMatrixFlatFin Uhat) (blockMatrixFlatFin DeltaU)
      (blockMatrixRowsFlatFin Xhat) (blockMatrixRowsFlatFin Yhat) :=
  dhs_block_back_substitution_firstOrder_from_rows_spec_of_coeff_bounds
    (Nat.mul_pos hm hr) u cRows cBack normA normL normU rowPerturbBound
    (blockMatrixFlatFin Lhat) (blockMatrixFlatFin Uhat)
    (blockMatrixFlatFin DeltaU) (blockMatrixRowsFlatFin Xhat)
    (blockMatrixRowsFlatFin Yhat) hu hcRows hA hL hU hLhat hc
    (dhs_block_back_substitution_rows_spec_from_fixed_block_rows_and_eq13_15
      hr u c₅ cRows normU rowPerturbBound normUii
      Uhat DeltaU Xhat Yhat Dhat hRows)

/-- Simultaneous strict-upper row witnesses and all local Eq.13.15 solves imply
    the selected global DHS block-back-substitution branch.

    This wrapper performs finite witness selection, upper/diagonal budget
    aggregation, fixed-row composition, block flattening, and the final
    `Lhat * DeltaU` max-entry transport. -/
theorem dhs_block_back_substitution_firstOrder_from_upper_row_witnesses_and_eq13_15
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (u c₅ cUpper cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hc₅ : 0 ≤ c₅) (hcUpper : 0 ≤ cUpper)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) * (cUpper + c₅)) ≤ cBack)
    (hRows : ∀ i : Fin m,
      ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
          (rowPerturbBound : ℝ),
        Dhat i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              (U i j + DeltaRow j) * X j = Y i ∧
        (∀ j : Fin m, ¬i.val < j.val → DeltaRow j = 0) ∧
        (∀ j : Fin m, ∀ s t : Fin r,
          |DeltaRow j s t| ≤ rowPerturbBound) ∧
        FirstOrderLe u (cUpper * u * normU) rowPerturbBound)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i) (Dhat i)) :
    ∃ DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  obtain ⟨DeltaUpper, upperPerturbBound, hUpper⟩ :=
    dhs_block_back_upper_rows_spec_from_row_witnesses
      hm u cUpper normU U X Y Dhat hRows
  obtain ⟨DeltaU, rowPerturbBound, hFixed⟩ :=
    dhs_block_back_fixed_rows_spec_from_upper_rows_and_eq13_15
      hm hr u c₅ cUpper normU upperPerturbBound normUii
      U DeltaUpper DeltaDiag X Y Dhat hu hc₅ hUUpper hNormUii
      hUpper hDiagonal
  refine ⟨DeltaU, ?_⟩
  exact
    dhs_block_back_substitution_firstOrder_from_fixed_block_rows_and_eq13_15_of_coeff_bounds
      hm hr u c₅ (cUpper + c₅) cBack normA normL normU rowPerturbBound
      normUii Lhat U DeltaU X Y Dhat hu (add_nonneg hcUpper hc₅)
      hA hL hU hLhat hc hFixed

/-- Choose the individually proved full-suffix row witnesses simultaneously
    and aggregate their first-order budgets into one finite envelope. -/
theorem dhs_block_back_suffix_rows_spec_from_row_witnesses
    {m r : ℕ}
    (hm : 0 < m)
    (u cSuffix normU : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hRows : ∀ i : Fin m,
      ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
          (rowPerturbBound : ℝ),
        Dhat i +
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U i j * X j) +
            (∑ j : Fin m, DeltaRow j * X j) = Y i ∧
        (∀ j : Fin m, j.val < i.val → DeltaRow j = 0) ∧
        (∀ j : Fin m, ∀ s t : Fin r,
          |DeltaRow j s t| ≤ rowPerturbBound) ∧
        FirstOrderLe u (cSuffix * u * normU) rowPerturbBound) :
    ∃ (DeltaSuffix : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
        (suffixPerturbBound : ℝ),
      DHSBlockBackSubstitutionSuffixRowsFirstOrderSpec
        u cSuffix normU suffixPerturbBound U DeltaSuffix X Y Dhat := by
  classical
  choose DeltaRow rowPerturbBound hRow using hRows
  let DeltaSuffix : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
    fun i j => DeltaRow i j
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  let suffixPerturbBound := Finset.univ.sup' hne rowPerturbBound
  refine ⟨DeltaSuffix, suffixPerturbBound, ?_, ?_, ?_, ?_⟩
  · intro i j hji
    simpa [DeltaSuffix] using (hRow i).2.1 j hji
  · intro i
    simpa [DeltaSuffix] using (hRow i).1
  · intro i j s t
    calc
      |DeltaSuffix i j s t| ≤ rowPerturbBound i := by
        simpa [DeltaSuffix] using (hRow i).2.2.1 j s t
      _ ≤ suffixPerturbBound :=
        Finset.le_sup' rowPerturbBound (Finset.mem_univ i)
  · exact FirstOrderLe.finset_univ_sup' hne rowPerturbBound
      (fun i => (hRow i).2.2.2)

/-- Add every local Eq.13.15 perturbation to the simultaneously assembled
    RHS-formation suffix perturbations.

    The combined diagonal block is `DeltaSuffix i i + DeltaDiag i`, and its
    right-hand side is correspondingly
    `Dhat i + DeltaSuffix i i * X i`.  Thus the RHS-formation diagonal
    perturbation is neither discarded nor counted twice.  Finite envelopes
    give the single coefficient `cSuffix + c₅` used by the existing fixed-row
    and flattening layers. -/
theorem dhs_block_back_fixed_rows_spec_from_suffix_rows_and_eq13_15
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (u c₅ cSuffix normU suffixPerturbBound : ℝ)
    (normUii : Fin m → ℝ)
    (U DeltaSuffix : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hc₅ : 0 ≤ c₅)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hSuffix : DHSBlockBackSubstitutionSuffixRowsFirstOrderSpec
      u cSuffix normU suffixPerturbBound U DeltaSuffix X Y Dhat)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i) (Dhat i)) :
    ∃ (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ)
        (DhatCombined : Fin m → Matrix (Fin r) (Fin 1) ℝ),
      DHSBlockBackSubstitutionFixedBlockRowsFirstOrderSpec
        hr u (cSuffix + c₅) (cSuffix + c₅) normU rowPerturbBound
        (fun _i => normU) U DeltaU X Y DhatCombined := by
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
  have hCombinedBound : FirstOrderLe u
      ((cSuffix + c₅) * u * normU)
      (suffixPerturbBound + diagPerturbBound) := by
    have hAdd := FirstOrderLe.add hSuffix.norm_bound hDiagBound le_rfl
    apply hAdd.mono_leading
    exact le_of_eq (by ring)
  have hSuffixNonneg : 0 ≤ suffixPerturbBound := by
    let i0 : Fin m := ⟨0, hm⟩
    let s0 : Fin r := ⟨0, hr⟩
    exact le_trans (abs_nonneg (DeltaSuffix i0 i0 s0 s0))
      (hSuffix.entry_bound i0 i0 s0 s0)
  have hDiagNonneg : 0 ≤ diagPerturbBound := by
    let i0 : Fin m := ⟨0, hm⟩
    exact le_trans (maxEntryNorm_nonneg hr (DeltaDiag i0))
      (Finset.le_sup' (fun i => maxEntryNorm hr (DeltaDiag i))
        (Finset.mem_univ i0))
  let DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ := fun i j =>
    DeltaSuffix i j + if j = i then DeltaDiag i else 0
  let DhatCombined : Fin m → Matrix (Fin r) (Fin 1) ℝ := fun i =>
    Dhat i + DeltaSuffix i i * X i
  refine ⟨DeltaU, suffixPerturbBound + diagPerturbBound,
    DhatCombined, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hji
    have hneji : j ≠ i := by omega
    refine ⟨hUUpper i j hji, ?_⟩
    simp [DeltaU, hneji, hSuffix.support i j hji]
  · intro i
    let g : Fin m → Matrix (Fin r) (Fin 1) ℝ :=
      fun j => DeltaSuffix i j * X j
    have hbelow :
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬i.val ≤ j.val),
          g j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j.val < i.val := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hj
      simp [g, hSuffix.support i j hji]
    have htailset :
        Finset.univ.filter (fun j : Fin m => i.val ≤ j.val) \ {i} =
          Finset.univ.filter (fun j : Fin m => i.val < j.val) := by
      ext j
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      omega
    have hge :
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val),
          g j) =
          DeltaSuffix i i * X i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              DeltaSuffix i j * X j := by
      calc
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val ≤ j.val),
            g j) =
            g i +
              ∑ j ∈ (Finset.univ.filter
                (fun j : Fin m => i.val ≤ j.val)) \ {i}, g j := by
          exact Finset.sum_eq_add_sum_diff_singleton i g (by simp)
        _ = g i +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                g j := by
          rw [htailset]
        _ = DeltaSuffix i i * X i +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                DeltaSuffix i j * X j := by rfl
    have hDeltaDecomp :
        (∑ j : Fin m, DeltaSuffix i j * X j) =
          DeltaSuffix i i * X i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              DeltaSuffix i j * X j := by
      change (∑ j : Fin m, g j) = _
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin m => i.val ≤ j.val)]
      rw [hbelow, add_zero, hge]
    have hTailExpand :
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          (U i j + DeltaU i j) * X j) =
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            U i j * X j) +
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            DeltaSuffix i j * X j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hij : i.val < j.val := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hneji : j ≠ i := by omega
      simp only [DeltaU, if_neg hneji, add_zero, Matrix.add_mul]
    rw [hTailExpand]
    simp only [DhatCombined]
    calc
      Dhat i + DeltaSuffix i i * X i +
            ((∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                U i j * X j) +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                DeltaSuffix i j * X j) =
          Dhat i +
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U i j * X j) +
            (DeltaSuffix i i * X i +
              ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
                DeltaSuffix i j * X j) := by abel
      _ = Dhat i +
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U i j * X j) +
            (∑ j : Fin m, DeltaSuffix i j * X j) := by
        rw [hDeltaDecomp]
      _ = Y i := hSuffix.rhs_formation i
  · intro i
    have hDeltaAtDiag : DeltaU i i = DeltaSuffix i i + DeltaDiag i := by
      simp [DeltaU]
    refine ⟨?_, ?_⟩
    · rw [hDeltaAtDiag]
      calc
        (U i i + (DeltaSuffix i i + DeltaDiag i)) * X i =
            (U i i + DeltaDiag i) * X i + DeltaSuffix i i * X i := by
          rw [show U i i + (DeltaSuffix i i + DeltaDiag i) =
              (U i i + DeltaDiag i) + DeltaSuffix i i by abel]
          rw [Matrix.add_mul]
        _ = Dhat i + DeltaSuffix i i * X i := by
          rw [(hDiagonal i).equation]
        _ = DhatCombined i := by rfl
    · apply hCombinedBound.mono_value
      calc
        maxEntryNorm hr (DeltaU i i) =
            maxEntryNorm hr (DeltaSuffix i i + DeltaDiag i) := by
          rw [hDeltaAtDiag]
        _ ≤ maxEntryNorm hr (DeltaSuffix i i) +
            maxEntryNorm hr (DeltaDiag i) :=
          maxEntryNorm_add_le hr (DeltaSuffix i i) (DeltaDiag i)
        _ ≤ suffixPerturbBound + diagPerturbBound :=
          add_le_add
            (maxEntryNorm_le_of_entry_le_bound hr (DeltaSuffix i i)
              suffixPerturbBound (hSuffix.entry_bound i i))
            (Finset.le_sup' (fun k => maxEntryNorm hr (DeltaDiag k))
              (Finset.mem_univ i))
  · intro i j s t
    by_cases hji : j = i
    · subst j
      simp only [DeltaU, if_pos]
      calc
        |DeltaSuffix i i s t + DeltaDiag i s t| ≤
            |DeltaSuffix i i s t| + |DeltaDiag i s t| := abs_add_le _ _
        _ ≤ suffixPerturbBound + maxEntryNorm hr (DeltaDiag i) :=
          add_le_add (hSuffix.entry_bound i i s t)
            (entry_le_maxEntryNorm hr (DeltaDiag i) s t)
        _ ≤ suffixPerturbBound + diagPerturbBound :=
          add_le_add le_rfl
            (Finset.le_sup' (fun k => maxEntryNorm hr (DeltaDiag k))
              (Finset.mem_univ i))
    · simp only [DeltaU, if_neg hji, add_zero]
      calc
        |DeltaSuffix i j s t| ≤ suffixPerturbBound :=
          hSuffix.entry_bound i j s t
        _ ≤ suffixPerturbBound + diagPerturbBound := by linarith
  · exact hCombinedBound

/-- Simultaneous full-suffix RHS-formation row witnesses and all local
    Eq.13.15 solves imply the selected global DHS back-substitution branch.

    This is the source-correct counterpart of the earlier strict-upper
    wrapper: finite witness selection, diagonal composition, fixed-row
    algebra, block flattening, and `Lhat * DeltaU` transport are all performed
    without excluding the RHS-formation perturbation at `j = i`. -/
theorem dhs_block_back_substitution_firstOrder_from_suffix_row_witnesses_and_eq13_15
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (u c₅ cSuffix cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hc₅ : 0 ≤ c₅) (hcSuffix : 0 ≤ cSuffix)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) * (cSuffix + c₅)) ≤ cBack)
    (hRows : ∀ i : Fin m,
      ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
          (rowPerturbBound : ℝ),
        Dhat i +
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U i j * X j) +
            (∑ j : Fin m, DeltaRow j * X j) = Y i ∧
        (∀ j : Fin m, j.val < i.val → DeltaRow j = 0) ∧
        (∀ j : Fin m, ∀ s t : Fin r,
          |DeltaRow j s t| ≤ rowPerturbBound) ∧
        FirstOrderLe u (cSuffix * u * normU) rowPerturbBound)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i) (Dhat i)) :
    ∃ DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  obtain ⟨DeltaSuffix, suffixPerturbBound, hSuffix⟩ :=
    dhs_block_back_suffix_rows_spec_from_row_witnesses
      hm u cSuffix normU U X Y Dhat hRows
  obtain ⟨DeltaU, rowPerturbBound, DhatCombined, hFixed⟩ :=
    dhs_block_back_fixed_rows_spec_from_suffix_rows_and_eq13_15
      hm hr u c₅ cSuffix normU suffixPerturbBound normUii
      U DeltaSuffix DeltaDiag X Y Dhat hu hc₅ hUUpper hNormUii
      hSuffix hDiagonal
  refine ⟨DeltaU, ?_⟩
  exact
    dhs_block_back_substitution_firstOrder_from_fixed_block_rows_and_eq13_15_of_coeff_bounds
      hm hr u (cSuffix + c₅) (cSuffix + c₅) cBack
      normA normL normU rowPerturbBound (fun _i => normU)
      Lhat U DeltaU X Y DhatCombined hu (add_nonneg hcSuffix hc₅)
      hA hL hU hLhat hc hFixed

/-- Source-correct suffix witnesses with Eq.13.15 produce both the flattened
    row certificate and the transported global back-substitution spec.

    Retaining the row certificate exposes the entrywise perturbation bound
    needed to prove that the forward/back cross product is `O(u^2)`; the
    earlier wrapper deliberately projected this information away. -/
theorem
    dhs_block_back_substitution_rows_and_firstOrder_from_suffix_row_witnesses_and_eq13_15
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (u c₅ cSuffix cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y Dhat : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hc₅ : 0 ≤ c₅) (hcSuffix : 0 ≤ cSuffix)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) * (cSuffix + c₅)) ≤ cBack)
    (hRowWitnesses : ∀ i : Fin m,
      ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
          (rowPerturbBound : ℝ),
        Dhat i +
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U i j * X j) +
            (∑ j : Fin m, DeltaRow j * X j) = Y i ∧
        (∀ j : Fin m, j.val < i.val → DeltaRow j = 0) ∧
        (∀ j : Fin m, ∀ s t : Fin r,
          |DeltaRow j s t| ≤ rowPerturbBound) ∧
        FirstOrderLe u (cSuffix * u * normU) rowPerturbBound)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i) (Dhat i)) :
    ∃ (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      DHSBlockBackSubstitutionRowsFirstOrderSpec
        u (cSuffix + c₅) normU rowPerturbBound
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) ∧
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  obtain ⟨DeltaSuffix, suffixPerturbBound, hSuffix⟩ :=
    dhs_block_back_suffix_rows_spec_from_row_witnesses
      hm u cSuffix normU U X Y Dhat hRowWitnesses
  obtain ⟨DeltaU, rowPerturbBound, DhatCombined, hFixed⟩ :=
    dhs_block_back_fixed_rows_spec_from_suffix_rows_and_eq13_15
      hm hr u c₅ cSuffix normU suffixPerturbBound normUii
      U DeltaSuffix DeltaDiag X Y Dhat hu hc₅ hUUpper hNormUii
      hSuffix hDiagonal
  have hRows : DHSBlockBackSubstitutionRowsFirstOrderSpec
      u (cSuffix + c₅) normU rowPerturbBound
      (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
      (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) :=
    dhs_block_back_substitution_rows_spec_from_fixed_block_rows_and_eq13_15
      hr u (cSuffix + c₅) (cSuffix + c₅) normU rowPerturbBound
      (fun _i => normU) U DeltaU X Y DhatCombined hFixed
  refine ⟨DeltaU, rowPerturbBound, hRows, ?_⟩
  exact
    dhs_block_back_substitution_firstOrder_from_rows_spec_of_coeff_bounds
      (Nat.mul_pos hm hr) u (cSuffix + c₅) cBack
      normA normL normU rowPerturbBound
      (blockMatrixFlatFin Lhat) (blockMatrixFlatFin U)
      (blockMatrixFlatFin DeltaU) (blockMatrixRowsFlatFin X)
      (blockMatrixRowsFlatFin Y) hu (add_nonneg hcSuffix hc₅)
      hA hL hU hLhat hc hRows

/-- DHS two-block back-substitution RHS perturbation from the Chapter 13
    product and subtraction models.

    For one right-hand side, the product residual `DeltaC` and subtraction
    residual `Fsub` combine as `DeltaC - Fsub`.  The max-norm residual-lifting
    lemma turns that vector into an off-diagonal coefficient perturbation
    `DeltaU12`, giving the source equation
    `Dhat + (U12 + DeltaU12) X2 = Y1`.  The explicit residual-scale premise is
    the remaining numerical comparison needed to bound this coefficient
    perturbation; no exact row equation is assumed. -/
theorem dhs_two_block_back_rhs_perturbation_from_matmul_subtraction_specs
    {r : ℕ}
    (hr : 0 < r)
    (u cMul normU12 normX2 normY1 normChat eta : ℝ)
    (U12 : Matrix (Fin r) (Fin r) ℝ)
    (X2 Chat DeltaC Y1 Fsub Dhat : Matrix (Fin r) (Fin 1) ℝ)
    (heta : 0 ≤ eta)
    (hMul : MatMulFirstOrderSpec u cMul normU12 normX2
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      U12 X2 Chat DeltaC)
    (hSub : SubtractionFirstOrderSpec u normY1 normChat
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y1 Chat Fsub Dhat)
    (hResidualScale :
      maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
          maxEntryNormRect hr (Nat.succ_pos 0) Fsub ≤
        eta * infNormVec (fun t : Fin r => X2 t 0)) :
    ∃ DeltaU12 : Matrix (Fin r) (Fin r) ℝ,
      Dhat + (U12 + DeltaU12) * X2 = Y1 ∧
      maxEntryNormRect hr hr DeltaU12 ≤ eta := by
  let residual : Fin r → ℝ := fun s => DeltaC s 0 - Fsub s 0
  have hResidualNorm : infNormVec residual ≤
      eta * infNormVec (fun t : Fin r => X2 t 0) := by
    apply infNormVec_le_of_abs_le
    · intro s
      calc
        |residual s| ≤ |DeltaC s 0| + |Fsub s 0| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_sub_le (DeltaC s 0) 0 (Fsub s 0)
        _ ≤ maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
            maxEntryNormRect hr (Nat.succ_pos 0) Fsub :=
          add_le_add
            (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) DeltaC s 0)
            (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) Fsub s 0)
        _ ≤ eta * infNormVec (fun t : Fin r => X2 t 0) := hResidualScale
    · exact mul_nonneg heta (infNormVec_nonneg _)
  obtain ⟨DeltaU12, hDeltaMul, hDeltaNorm⟩ :=
    higham13_maxNorm_vecResidual_lift hr hr
      (fun t : Fin r => X2 t 0) residual eta heta hResidualNorm
  have hDeltaMatrix : DeltaU12 * X2 = DeltaC - Fsub := by
    ext s k
    fin_cases k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, residual] using
      congrFun hDeltaMul s
  refine ⟨DeltaU12, ?_, hDeltaNorm⟩
  rw [hSub.equation, Matrix.add_mul, hMul.equation, hDeltaMatrix]
  abel

/-- DHS two-block back-substitution RHS perturbation with its first-order
    coefficient bound derived from the product and subtraction budgets.

    The source-style magnitude comparison bounds the subtraction inputs by the
    common upper-factor scale times `‖X₂‖∞`.  Together with containment of the
    off-diagonal block norm in that common scale, this removes the preceding
    theorem's raw residual-scale premise.  Division by the nonzero solution
    norm realizes the residual as a coefficient perturbation and cancels the
    solution norm from the first-order leading term. -/
theorem dhs_two_block_back_rhs_perturbation_firstOrder_from_matmul_subtraction_specs_of_rhs_scale
    {r : ℕ}
    (hr : 0 < r)
    (u cMul cSub normU12 normU normY1 normChat : ℝ)
    (U12 : Matrix (Fin r) (Fin r) ℝ)
    (X2 Chat DeltaC Y1 Fsub Dhat : Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hcMul : 0 ≤ cMul)
    (hU12U : normU12 ≤ normU)
    (hX2 : infNormVec (fun t : Fin r => X2 t 0) ≠ 0)
    (hRhsScale :
      normY1 + normChat ≤
        cSub * normU * infNormVec (fun t : Fin r => X2 t 0))
    (hMul : MatMulFirstOrderSpec u cMul normU12
      (infNormVec (fun t : Fin r => X2 t 0))
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      U12 X2 Chat DeltaC)
    (hSub : SubtractionFirstOrderSpec u normY1 normChat
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y1 Chat Fsub Dhat) :
    ∃ DeltaU12 : Matrix (Fin r) (Fin r) ℝ,
      Dhat + (U12 + DeltaU12) * X2 = Y1 ∧
      FirstOrderLe u ((cMul + cSub) * u * normU)
        (maxEntryNormRect hr hr DeltaU12) := by
  let xnorm := infNormVec (fun t : Fin r => X2 t 0)
  let deltaNorm := maxEntryNormRect hr (Nat.succ_pos 0) DeltaC
  let fNorm := maxEntryNormRect hr (Nat.succ_pos 0) Fsub
  have hxpos : 0 < xnorm :=
    lt_of_le_of_ne (infNormVec_nonneg _) (Ne.symm hX2)
  have hMulU : FirstOrderLe u
      (cMul * u * normU * xnorm) deltaNorm := by
    apply hMul.norm_bound.mono_leading
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hU12U (mul_nonneg hcMul hu)
    · exact infNormVec_nonneg _
  have hFsub : FirstOrderLe u
      (cSub * u * normU * xnorm) fNorm := by
    apply FirstOrderLe.of_le
    calc
      fNorm ≤ u * (normY1 + normChat) := hSub.norm_bound
      _ ≤ u * (cSub * normU * xnorm) :=
        mul_le_mul_of_nonneg_left hRhsScale hu
      _ = cSub * u * normU * xnorm := by ring
  have hResidual : FirstOrderLe u
      ((cMul + cSub) * u * normU * xnorm) (deltaNorm + fNorm) := by
    have hAdd := FirstOrderLe.add hMulU hFsub le_rfl
    apply hAdd.mono_leading
    exact le_of_eq (by ring)
  have heta : 0 ≤ (deltaNorm + fNorm) / xnorm :=
    div_nonneg
      (add_nonneg
        (maxEntryNormRect_nonneg hr (Nat.succ_pos 0) DeltaC)
        (maxEntryNormRect_nonneg hr (Nat.succ_pos 0) Fsub))
      (le_of_lt hxpos)
  have hResidualScale :
      deltaNorm + fNorm ≤ ((deltaNorm + fNorm) / xnorm) * xnorm := by
    apply le_of_eq
    field_simp [ne_of_gt hxpos]
  obtain ⟨DeltaU12, hEquation, hDeltaNorm⟩ :=
    dhs_two_block_back_rhs_perturbation_from_matmul_subtraction_specs
      hr u cMul normU12 xnorm normY1 normChat
      ((deltaNorm + fNorm) / xnorm) U12 X2 Chat DeltaC Y1 Fsub Dhat
      heta hMul hSub hResidualScale
  have hxinv_nonneg : 0 ≤ xnorm⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
  have hScaled : FirstOrderLe u
      (((cMul + cSub) * u * normU * xnorm) * xnorm⁻¹)
      ((deltaNorm + fNorm) * xnorm⁻¹) :=
    hResidual.bound_mul_nonneg_right hxinv_nonneg le_rfl
  have hLeading :
      ((cMul + cSub) * u * normU * xnorm) * xnorm⁻¹ =
        (cMul + cSub) * u * normU := by
    field_simp [ne_of_gt hxpos]
  have hEtaFirstOrder : FirstOrderLe u
      ((cMul + cSub) * u * normU) ((deltaNorm + fNorm) / xnorm) := by
    simpa [div_eq_mul_inv] using
      hScaled.mono_leading (le_of_eq hLeading)
  exact ⟨DeltaU12, hEquation, hEtaFirstOrder.mono_value hDeltaNorm⟩

/-- Concrete two-block DHS back-substitution row formed by the repository's
    conventional rounded matrix product and entrywise subtraction.

    This instantiates both abstract operation specs in the preceding theorem.
    Under the source-style RHS magnitude comparison, the returned coefficient
    perturbation satisfies the exact equation for the actual computed
    right-hand side and has leading coefficient `r² + cRhs`. -/
theorem dhs_two_block_back_rhs_perturbation_firstOrder_from_conventional_operations
    {r : ℕ}
    (fp : FPModel) (hr : 0 < r)
    (cRhs normU : ℝ)
    (U12 : Matrix (Fin r) (Fin r) ℝ)
    (X2 Y1 : Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp r)
    (hU12U : maxEntryNormRect hr hr U12 ≤ normU)
    (hX2 : infNormVec (fun t : Fin r => X2 t 0) ≠ 0)
    (hRhsScale :
      maxEntryNormRect hr (Nat.succ_pos 0) Y1 +
          maxEntryNormRect hr (Nat.succ_pos 0)
            (fl_matMul fp r r 1 U12 X2) ≤
        cRhs * normU * infNormVec (fun t : Fin r => X2 t 0)) :
    ∃ DeltaU12 : Matrix (Fin r) (Fin r) ℝ,
      higham13_fl_matrixSub fp Y1 (fl_matMul fp r r 1 U12 X2) +
          (U12 + DeltaU12) * X2 = Y1 ∧
      FirstOrderLe fp.u (((r : ℝ) ^ 2 + cRhs) * fp.u * normU)
        (maxEntryNormRect hr hr DeltaU12) := by
  let Chat : Matrix (Fin r) (Fin 1) ℝ := fl_matMul fp r r 1 U12 X2
  let DeltaC : Matrix (Fin r) (Fin 1) ℝ := fun i j =>
    Chat i j - ∑ k : Fin r, U12 i k * X2 k j
  let Fsub := higham13_fl_matrixSubError fp Y1 Chat
  let Dhat := higham13_fl_matrixSub fp Y1 Chat
  have hMul : MatMulFirstOrderSpec fp.u ((r : ℝ) ^ 2)
      (maxEntryNormRect hr hr U12)
      (infNormVec (fun t : Fin r => X2 t 0))
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      U12 X2 Chat DeltaC := by
    simpa only [Chat, DeltaC,
      maxEntryNormRect_single_col_eq_infNormVec hr X2] using
      higham13_conventional_matmul_spec_c1_maxEntry
        fp hr hr (Nat.succ_pos 0) U12 X2 hγ
  have hSub : SubtractionFirstOrderSpec fp.u
      (maxEntryNormRect hr (Nat.succ_pos 0) Y1)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y1 Chat Fsub Dhat := by
    exact higham13_conventional_subtraction_spec_maxEntry
      fp hr (Nat.succ_pos 0) Y1 Chat
  simpa [Chat, Dhat] using
    dhs_two_block_back_rhs_perturbation_firstOrder_from_matmul_subtraction_specs_of_rhs_scale
      hr fp.u ((r : ℝ) ^ 2) cRhs
      (maxEntryNormRect hr hr U12) normU
      (maxEntryNormRect hr (Nat.succ_pos 0) Y1)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      U12 X2 Chat DeltaC Y1 Fsub Dhat fp.u_nonneg (sq_nonneg (r : ℝ))
      hU12U hX2 (by simpa [Chat] using hRhsScale) hMul hSub

/-- Construct the coefficient perturbations for an arbitrary fixed upper
    block-back-substitution row from an aggregate tail-product spec and the
    following rounded subtraction.

    The support-preserving residual lift distributes `DeltaC - Fsub` only over
    strict upper blocks, while the flattened-tail product identity recovers
    the source sum of block products. -/
theorem dhs_block_back_upper_row_perturbation_from_matmul_subtraction_specs
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (u cMul normUTail normXTail normY normChat eta : ℝ)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Chat DeltaC Y Fsub Dhat : Matrix (Fin r) (Fin 1) ℝ)
    (heta : 0 ≤ eta)
    (hMul : MatMulFirstOrderSpec u cMul normUTail normXTail
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      (dhsBlockBackUpperTailRowFlat i U)
      (dhsBlockBackUpperTailColumn i X) Chat DeltaC)
    (hSub : SubtractionFirstOrderSpec u normY normChat
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y Chat Fsub Dhat)
    (hResidualScale :
      maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
          maxEntryNormRect hr (Nat.succ_pos 0) Fsub ≤
        eta * infNormVec (dhsBlockBackUpperTailVector i X)) :
    ∃ Delta : Fin m → Matrix (Fin r) (Fin r) ℝ,
      Dhat +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            (U j + Delta j) * X j = Y ∧
      (∀ j : Fin m, ¬i.val < j.val → Delta j = 0) ∧
      ∀ j : Fin m, ∀ s t : Fin r, |Delta j s t| ≤ eta := by
  let residual : Fin r → ℝ := fun s => DeltaC s 0 - Fsub s 0
  have hResidualNorm : infNormVec residual ≤
      eta * infNormVec (dhsBlockBackUpperTailVector i X) := by
    apply infNormVec_le_of_abs_le
    · intro s
      calc
        |residual s| ≤ |DeltaC s 0| + |Fsub s 0| := by
          simpa [residual, sub_eq_add_neg, abs_neg] using
            abs_sub_le (DeltaC s 0) 0 (Fsub s 0)
        _ ≤ maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
            maxEntryNormRect hr (Nat.succ_pos 0) Fsub :=
          add_le_add
            (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) DeltaC s 0)
            (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) Fsub s 0)
        _ ≤ eta * infNormVec (dhsBlockBackUpperTailVector i X) :=
          hResidualScale
    · exact mul_nonneg heta (infNormVec_nonneg _)
  obtain ⟨Delta, hDeltaFull, hInactive, hEntry⟩ :=
    higham13_maxNorm_upperBlockRowResidual_lift
      hm hr i X residual eta heta hResidualNorm
  have hDeltaTail :
      (∑ j : Fin m, Delta j * X j) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          Delta j * X j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _hjmem
    by_cases hj : i.val < j.val
    · simp [hj]
    · rw [hInactive j hj]
      simp [hj]
  have hDeltaResidual :
      (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          Delta j * X j) = DeltaC - Fsub := by
    rw [← hDeltaTail, hDeltaFull]
    ext s k
    fin_cases k
    rfl
  have hProduct :
      dhsBlockBackUpperTailRowFlat i U *
          dhsBlockBackUpperTailColumn i X =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          U j * X j := by
    ext s k
    fin_cases k
    exact dhsBlockBackUpperTailRowFlat_mul_apply i U X s
  have hMulEquation :
      Chat =
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          U j * X j) + DeltaC := by
    simpa [hProduct] using hMul.equation
  refine ⟨Delta, ?_, hInactive, hEntry⟩
  calc
    Dhat +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            (U j + Delta j) * X j =
        Dhat +
          ((∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U j * X j) +
            ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              Delta j * X j) := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hjmem
      rw [Matrix.add_mul]
    _ = Dhat +
          ((∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
              U j * X j) + (DeltaC - Fsub)) := by
      rw [hDeltaResidual]
    _ = Y := by
      rw [hSub.equation, hMulEquation]
      abel

/-- First-order arbitrary-row companion to
    `dhs_block_back_upper_row_perturbation_from_matmul_subtraction_specs`.

    A source-style bound on the subtraction inputs and containment of the
    strict upper-tail norm in the global upper-factor scale remove the raw
    error-scale premise.  The returned row perturbation has strict upper
    support and a common entrywise first-order budget. -/
theorem dhs_block_back_upper_row_perturbation_firstOrder_from_matmul_subtraction_specs_of_rhs_scale
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (u cMul cSub normUTail normU normY normChat : ℝ)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Chat DeltaC Y Fsub Dhat : Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hcMul : 0 ≤ cMul)
    (hUTailU : normUTail ≤ normU)
    (hXTail : infNormVec (dhsBlockBackUpperTailVector i X) ≠ 0)
    (hRhsScale :
      normY + normChat ≤
        cSub * normU * infNormVec (dhsBlockBackUpperTailVector i X))
    (hMul : MatMulFirstOrderSpec u cMul normUTail
      (infNormVec (dhsBlockBackUpperTailVector i X))
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      (dhsBlockBackUpperTailRowFlat i U)
      (dhsBlockBackUpperTailColumn i X) Chat DeltaC)
    (hSub : SubtractionFirstOrderSpec u normY normChat
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y Chat Fsub Dhat) :
    ∃ (Delta : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      Dhat +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            (U j + Delta j) * X j = Y ∧
      (∀ j : Fin m, ¬i.val < j.val → Delta j = 0) ∧
      (∀ j : Fin m, ∀ s t : Fin r,
        |Delta j s t| ≤ rowPerturbBound) ∧
      FirstOrderLe u ((cMul + cSub) * u * normU) rowPerturbBound := by
  let xnorm := infNormVec (dhsBlockBackUpperTailVector i X)
  let deltaNorm := maxEntryNormRect hr (Nat.succ_pos 0) DeltaC
  let fNorm := maxEntryNormRect hr (Nat.succ_pos 0) Fsub
  have hxpos : 0 < xnorm :=
    lt_of_le_of_ne (infNormVec_nonneg _) (Ne.symm hXTail)
  have hMulU : FirstOrderLe u
      (cMul * u * normU * xnorm) deltaNorm := by
    apply hMul.norm_bound.mono_leading
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hUTailU (mul_nonneg hcMul hu)
    · exact infNormVec_nonneg _
  have hFsub : FirstOrderLe u
      (cSub * u * normU * xnorm) fNorm := by
    apply FirstOrderLe.of_le
    calc
      fNorm ≤ u * (normY + normChat) := hSub.norm_bound
      _ ≤ u * (cSub * normU * xnorm) :=
        mul_le_mul_of_nonneg_left hRhsScale hu
      _ = cSub * u * normU * xnorm := by ring
  have hResidual : FirstOrderLe u
      ((cMul + cSub) * u * normU * xnorm) (deltaNorm + fNorm) := by
    have hAdd := FirstOrderLe.add hMulU hFsub le_rfl
    apply hAdd.mono_leading
    exact le_of_eq (by ring)
  have heta : 0 ≤ (deltaNorm + fNorm) / xnorm :=
    div_nonneg
      (add_nonneg
        (maxEntryNormRect_nonneg hr (Nat.succ_pos 0) DeltaC)
        (maxEntryNormRect_nonneg hr (Nat.succ_pos 0) Fsub))
      (le_of_lt hxpos)
  have hResidualScale :
      deltaNorm + fNorm ≤ ((deltaNorm + fNorm) / xnorm) * xnorm := by
    apply le_of_eq
    field_simp [ne_of_gt hxpos]
  obtain ⟨Delta, hEquation, hInactive, hEntry⟩ :=
    dhs_block_back_upper_row_perturbation_from_matmul_subtraction_specs
      hm hr i u cMul normUTail xnorm normY normChat
      ((deltaNorm + fNorm) / xnorm) U X Chat DeltaC Y Fsub Dhat
      heta hMul hSub hResidualScale
  have hxinv_nonneg : 0 ≤ xnorm⁻¹ := inv_nonneg.mpr (le_of_lt hxpos)
  have hScaled : FirstOrderLe u
      (((cMul + cSub) * u * normU * xnorm) * xnorm⁻¹)
      ((deltaNorm + fNorm) * xnorm⁻¹) :=
    hResidual.bound_mul_nonneg_right hxinv_nonneg le_rfl
  have hLeading :
      ((cMul + cSub) * u * normU * xnorm) * xnorm⁻¹ =
        (cMul + cSub) * u * normU := by
    field_simp [ne_of_gt hxpos]
  have hEtaFirstOrder : FirstOrderLe u
      ((cMul + cSub) * u * normU) ((deltaNorm + fNorm) / xnorm) := by
    simpa [div_eq_mul_inv] using
      hScaled.mono_leading (le_of_eq hLeading)
  exact ⟨Delta, (deltaNorm + fNorm) / xnorm,
    hEquation, hInactive, hEntry, hEtaFirstOrder⟩

/-- Executable arbitrary upper block-row construction using the repository's
    conventional rounded product and subtraction.

    The matrix multiplication is performed on the flattened strict upper
    coefficient row and masked stacked tail.  Its inner dimension is `m*r`, so
    the concrete conventional leading coefficient is `(m*r)^2`; the
    subtraction-input comparison contributes `cRhs`. -/
theorem dhs_block_back_upper_row_perturbation_firstOrder_from_conventional_operations
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (cRhs normU : ℝ)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Y : Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp (m * r))
    (hUTailU :
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i U) ≤ normU)
    (hXTail : infNormVec (dhsBlockBackUpperTailVector i X) ≠ 0)
    (hRhsScale :
      maxEntryNormRect hr (Nat.succ_pos 0) Y +
          maxEntryNormRect hr (Nat.succ_pos 0)
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i U)
              (dhsBlockBackUpperTailColumn i X)) ≤
        cRhs * normU * infNormVec (dhsBlockBackUpperTailVector i X)) :
    ∃ (Delta : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      higham13_fl_matrixSub fp Y
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i U)
              (dhsBlockBackUpperTailColumn i X)) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            (U j + Delta j) * X j = Y ∧
      (∀ j : Fin m, ¬i.val < j.val → Delta j = 0) ∧
      (∀ j : Fin m, ∀ s t : Fin r,
        |Delta j s t| ≤ rowPerturbBound) ∧
      FirstOrderLe fp.u
        ((((m * r : ℕ) : ℝ) ^ 2 + cRhs) * fp.u * normU)
        rowPerturbBound := by
  let A := dhsBlockBackUpperTailRowFlat i U
  let B := dhsBlockBackUpperTailColumn i X
  let Chat : Matrix (Fin r) (Fin 1) ℝ := fl_matMul fp r (m * r) 1 A B
  let DeltaC : Matrix (Fin r) (Fin 1) ℝ := fun s k =>
    Chat s k - ∑ jt : Fin (m * r), A s jt * B jt k
  let Fsub := higham13_fl_matrixSubError fp Y Chat
  let Dhat := higham13_fl_matrixSub fp Y Chat
  have hBnorm : maxEntryNormRect (Nat.mul_pos hm hr) (Nat.succ_pos 0) B =
      infNormVec (dhsBlockBackUpperTailVector i X) := by
    rw [maxEntryNormRect_single_col_eq_infNormVec]
    rfl
  have hMul : MatMulFirstOrderSpec fp.u (((m * r : ℕ) : ℝ) ^ 2)
      (maxEntryNormRect hr (Nat.mul_pos hm hr) A)
      (infNormVec (dhsBlockBackUpperTailVector i X))
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      A B Chat DeltaC := by
    simpa only [Chat, DeltaC, hBnorm] using
      higham13_conventional_matmul_spec_c1_maxEntry
        fp hr (Nat.mul_pos hm hr) (Nat.succ_pos 0) A B hγ
  have hSub : SubtractionFirstOrderSpec fp.u
      (maxEntryNormRect hr (Nat.succ_pos 0) Y)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y Chat Fsub Dhat := by
    exact higham13_conventional_subtraction_spec_maxEntry
      fp hr (Nat.succ_pos 0) Y Chat
  simpa [A, B, Chat, Dhat] using
    dhs_block_back_upper_row_perturbation_firstOrder_from_matmul_subtraction_specs_of_rhs_scale
      hm hr i fp.u (((m * r : ℕ) : ℝ) ^ 2) cRhs
      (maxEntryNormRect hr (Nat.mul_pos hm hr) A) normU
      (maxEntryNormRect hr (Nat.succ_pos 0) Y)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      U X Chat DeltaC Y Fsub Dhat fp.u_nonneg
      (sq_nonneg (((m * r : ℕ) : ℝ))) hUTailU hXTail
      (by simpa [A, B, Chat] using hRhsScale) hMul hSub

/-- Construct a source-correct coefficient perturbation for one arbitrary
    block-back-substitution row from an aggregate tail-product spec and the
    following rounded subtraction.

    The residual is lifted against the full upper suffix, not just the strict
    tail.  Consequently the returned perturbation may occupy the diagonal
    block, as required by the DHS row analysis, but it vanishes strictly below
    the current row. -/
theorem dhs_block_back_upper_suffix_row_perturbation_from_specs
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (u cMul normUTail normXTail normY normChat eta : ℝ)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Chat DeltaC Y Fsub Dhat : Matrix (Fin r) (Fin 1) ℝ)
    (heta : 0 ≤ eta)
    (hMul : MatMulFirstOrderSpec u cMul normUTail normXTail
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      (dhsBlockBackUpperTailRowFlat i U)
      (dhsBlockBackUpperTailColumn i X) Chat DeltaC)
    (hSub : SubtractionFirstOrderSpec u normY normChat
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y Chat Fsub Dhat)
    (hResidualScale :
      maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
          maxEntryNormRect hr (Nat.succ_pos 0) Fsub ≤
        eta * infNormVec (dhsBlockBackUpperSuffixVector i X)) :
    ∃ Delta : Fin m → Matrix (Fin r) (Fin r) ℝ,
      Dhat +
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            U j * X j) +
          (∑ j : Fin m, Delta j * X j) = Y ∧
      (∀ j : Fin m, j.val < i.val → Delta j = 0) ∧
      ∀ j : Fin m, ∀ s t : Fin r, |Delta j s t| ≤ eta := by
  let residual : Fin r → ℝ := fun s => DeltaC s 0 - Fsub s 0
  have hResidualNorm : infNormVec residual ≤
      eta * infNormVec (dhsBlockBackUpperSuffixVector i X) := by
    apply infNormVec_le_of_abs_le
    · intro s
      calc
        |residual s| ≤ |DeltaC s 0| + |Fsub s 0| := by
          simpa [residual, sub_eq_add_neg, abs_neg] using
            abs_sub_le (DeltaC s 0) 0 (Fsub s 0)
        _ ≤ maxEntryNormRect hr (Nat.succ_pos 0) DeltaC +
            maxEntryNormRect hr (Nat.succ_pos 0) Fsub :=
          add_le_add
            (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) DeltaC s 0)
            (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) Fsub s 0)
        _ ≤ eta * infNormVec (dhsBlockBackUpperSuffixVector i X) :=
          hResidualScale
    · exact mul_nonneg heta (infNormVec_nonneg _)
  obtain ⟨Delta, hDeltaFull, hInactive, hEntry⟩ :=
    higham13_maxNorm_upperBlockSuffixResidual_lift
      hm hr i X residual eta heta hResidualNorm
  have hDeltaResidual :
      (∑ j : Fin m, Delta j * X j) = DeltaC - Fsub := by
    rw [hDeltaFull]
    ext s k
    fin_cases k
    rfl
  have hProduct :
      dhsBlockBackUpperTailRowFlat i U *
          dhsBlockBackUpperTailColumn i X =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          U j * X j := by
    ext s k
    fin_cases k
    exact dhsBlockBackUpperTailRowFlat_mul_apply i U X s
  have hMulEquation :
      Chat =
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          U j * X j) + DeltaC := by
    simpa [hProduct] using hMul.equation
  refine ⟨Delta, ?_, hInactive, hEntry⟩
  rw [hDeltaResidual, hSub.equation, hMulEquation]
  abel

/-- First-order source-correct arbitrary-row companion to
    `dhs_block_back_upper_suffix_row_perturbation_from_specs`.

    The tail-product error first grows from the strict-tail scale to the full
    suffix scale.  The rounded subtraction is already compared against that
    suffix.  Dividing their combined residual by its nonzero suffix norm gives
    one common coefficient-entry budget supported on `j ≥ i`. -/
theorem dhs_block_back_upper_suffix_row_perturbation_firstOrder_from_specs
    {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (u cMul cSub normUTail normU normY normChat : ℝ)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Chat DeltaC Y Fsub Dhat : Matrix (Fin r) (Fin 1) ℝ)
    (hu : 0 ≤ u) (hcMul : 0 ≤ cMul) (hNormU : 0 ≤ normU)
    (hUTailU : normUTail ≤ normU)
    (hXSuffix : infNormVec (dhsBlockBackUpperSuffixVector i X) ≠ 0)
    (hRhsScale :
      normY + normChat ≤
        cSub * normU * infNormVec (dhsBlockBackUpperSuffixVector i X))
    (hMul : MatMulFirstOrderSpec u cMul normUTail
      (infNormVec (dhsBlockBackUpperTailVector i X))
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      (dhsBlockBackUpperTailRowFlat i U)
      (dhsBlockBackUpperTailColumn i X) Chat DeltaC)
    (hSub : SubtractionFirstOrderSpec u normY normChat
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y Chat Fsub Dhat) :
    ∃ (Delta : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      Dhat +
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            U j * X j) +
          (∑ j : Fin m, Delta j * X j) = Y ∧
      (∀ j : Fin m, j.val < i.val → Delta j = 0) ∧
      (∀ j : Fin m, ∀ s t : Fin r,
        |Delta j s t| ≤ rowPerturbBound) ∧
      FirstOrderLe u ((cMul + cSub) * u * normU) rowPerturbBound := by
  let tailNorm := infNormVec (dhsBlockBackUpperTailVector i X)
  let suffixNorm := infNormVec (dhsBlockBackUpperSuffixVector i X)
  let deltaNorm := maxEntryNormRect hr (Nat.succ_pos 0) DeltaC
  let fNorm := maxEntryNormRect hr (Nat.succ_pos 0) Fsub
  have hSuffixPos : 0 < suffixNorm :=
    lt_of_le_of_ne (infNormVec_nonneg _) (Ne.symm hXSuffix)
  have hTailSuffix : tailNorm ≤ suffixNorm :=
    dhsBlockBackUpperTail_infNormVec_le_suffix i X
  have hMulU : FirstOrderLe u
      (cMul * u * normU * suffixNorm) deltaNorm := by
    apply hMul.norm_bound.mono_leading
    calc
      cMul * u * normUTail * tailNorm ≤
          cMul * u * normU * tailNorm :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hUTailU (mul_nonneg hcMul hu))
          (infNormVec_nonneg _)
      _ ≤ cMul * u * normU * suffixNorm :=
        mul_le_mul_of_nonneg_left hTailSuffix
          (mul_nonneg (mul_nonneg hcMul hu) hNormU)
  have hFsub : FirstOrderLe u
      (cSub * u * normU * suffixNorm) fNorm := by
    apply FirstOrderLe.of_le
    calc
      fNorm ≤ u * (normY + normChat) := hSub.norm_bound
      _ ≤ u * (cSub * normU * suffixNorm) :=
        mul_le_mul_of_nonneg_left hRhsScale hu
      _ = cSub * u * normU * suffixNorm := by ring
  have hResidual : FirstOrderLe u
      ((cMul + cSub) * u * normU * suffixNorm)
      (deltaNorm + fNorm) := by
    have hAdd := FirstOrderLe.add hMulU hFsub le_rfl
    apply hAdd.mono_leading
    exact le_of_eq (by ring)
  have heta : 0 ≤ (deltaNorm + fNorm) / suffixNorm :=
    div_nonneg
      (add_nonneg
        (maxEntryNormRect_nonneg hr (Nat.succ_pos 0) DeltaC)
        (maxEntryNormRect_nonneg hr (Nat.succ_pos 0) Fsub))
      (le_of_lt hSuffixPos)
  have hResidualScale :
      deltaNorm + fNorm ≤
        ((deltaNorm + fNorm) / suffixNorm) * suffixNorm := by
    apply le_of_eq
    field_simp [ne_of_gt hSuffixPos]
  obtain ⟨Delta, hEquation, hInactive, hEntry⟩ :=
    dhs_block_back_upper_suffix_row_perturbation_from_specs
      hm hr i u cMul normUTail tailNorm normY normChat
      ((deltaNorm + fNorm) / suffixNorm)
      U X Chat DeltaC Y Fsub Dhat heta hMul hSub hResidualScale
  have hSuffixInvNonneg : 0 ≤ suffixNorm⁻¹ :=
    inv_nonneg.mpr (le_of_lt hSuffixPos)
  have hScaled : FirstOrderLe u
      (((cMul + cSub) * u * normU * suffixNorm) * suffixNorm⁻¹)
      ((deltaNorm + fNorm) * suffixNorm⁻¹) :=
    hResidual.bound_mul_nonneg_right hSuffixInvNonneg le_rfl
  have hLeading :
      ((cMul + cSub) * u * normU * suffixNorm) * suffixNorm⁻¹ =
        (cMul + cSub) * u * normU := by
    field_simp [ne_of_gt hSuffixPos]
  have hEtaFirstOrder : FirstOrderLe u
      ((cMul + cSub) * u * normU)
      ((deltaNorm + fNorm) / suffixNorm) := by
    simpa [div_eq_mul_inv] using
      hScaled.mono_leading (le_of_eq hLeading)
  exact ⟨Delta, (deltaNorm + fNorm) / suffixNorm,
    hEquation, hInactive, hEntry, hEtaFirstOrder⟩

/-- Executable source-correct upper-suffix row construction using conventional
    rounded matrix multiplication followed by conventional subtraction.

    The product is evaluated only on the strict upper tail, while the residual
    perturbation is supported on the full suffix.  Its concrete product
    coefficient is `(m*r)^2`; the source RHS comparison contributes `cRhs`. -/
theorem dhs_block_back_upper_suffix_row_perturbation_firstOrder_from_conventional_operations
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (cRhs normU : ℝ)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Y : Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp (m * r))
    (hUTailU :
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i U) ≤ normU)
    (hXSuffix : infNormVec (dhsBlockBackUpperSuffixVector i X) ≠ 0)
    (hRhsScale :
      maxEntryNormRect hr (Nat.succ_pos 0) Y +
          maxEntryNormRect hr (Nat.succ_pos 0)
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i U)
              (dhsBlockBackUpperTailColumn i X)) ≤
        cRhs * normU * infNormVec (dhsBlockBackUpperSuffixVector i X)) :
    ∃ (Delta : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      higham13_fl_matrixSub fp Y
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i U)
              (dhsBlockBackUpperTailColumn i X)) +
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            U j * X j) +
          (∑ j : Fin m, Delta j * X j) = Y ∧
      (∀ j : Fin m, j.val < i.val → Delta j = 0) ∧
      (∀ j : Fin m, ∀ s t : Fin r,
        |Delta j s t| ≤ rowPerturbBound) ∧
      FirstOrderLe fp.u
        ((((m * r : ℕ) : ℝ) ^ 2 + cRhs) * fp.u * normU)
        rowPerturbBound := by
  let A := dhsBlockBackUpperTailRowFlat i U
  let B := dhsBlockBackUpperTailColumn i X
  let Chat : Matrix (Fin r) (Fin 1) ℝ := fl_matMul fp r (m * r) 1 A B
  let DeltaC : Matrix (Fin r) (Fin 1) ℝ := fun s k =>
    Chat s k - ∑ jt : Fin (m * r), A s jt * B jt k
  let Fsub := higham13_fl_matrixSubError fp Y Chat
  let Dhat := higham13_fl_matrixSub fp Y Chat
  have hBnorm : maxEntryNormRect (Nat.mul_pos hm hr) (Nat.succ_pos 0) B =
      infNormVec (dhsBlockBackUpperTailVector i X) := by
    rw [maxEntryNormRect_single_col_eq_infNormVec]
    rfl
  have hMul : MatMulFirstOrderSpec fp.u (((m * r : ℕ) : ℝ) ^ 2)
      (maxEntryNormRect hr (Nat.mul_pos hm hr) A)
      (infNormVec (dhsBlockBackUpperTailVector i X))
      (maxEntryNormRect hr (Nat.succ_pos 0) DeltaC)
      A B Chat DeltaC := by
    simpa only [Chat, DeltaC, hBnorm] using
      higham13_conventional_matmul_spec_c1_maxEntry
        fp hr (Nat.mul_pos hm hr) (Nat.succ_pos 0) A B hγ
  have hSub : SubtractionFirstOrderSpec fp.u
      (maxEntryNormRect hr (Nat.succ_pos 0) Y)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      (maxEntryNormRect hr (Nat.succ_pos 0) Fsub)
      Y Chat Fsub Dhat := by
    exact higham13_conventional_subtraction_spec_maxEntry
      fp hr (Nat.succ_pos 0) Y Chat
  have hNormU : 0 ≤ normU :=
    le_trans (maxEntryNormRect_nonneg hr (Nat.mul_pos hm hr) A) hUTailU
  simpa [A, B, Chat, Dhat] using
    dhs_block_back_upper_suffix_row_perturbation_firstOrder_from_specs
      hm hr i fp.u (((m * r : ℕ) : ℝ) ^ 2) cRhs
      (maxEntryNormRect hr (Nat.mul_pos hm hr) A) normU
      (maxEntryNormRect hr (Nat.succ_pos 0) Y)
      (maxEntryNormRect hr (Nat.succ_pos 0) Chat)
      U X Chat DeltaC Y Fsub Dhat fp.u_nonneg
      (sq_nonneg (((m * r : ℕ) : ℝ))) hNormU hUTailU hXSuffix
      (by simpa [A, B, Chat] using hRhsScale) hMul hSub

/-- The actual conventional rounded strict-upper product for one fixed block
    back-substitution row. -/
noncomputable def dhsBlockBackConventionalUpperProduct {m r : ℕ}
    (fp : FPModel) (i : Fin m)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    Matrix (Fin r) (Fin 1) ℝ :=
  fl_matMul fp r (m * r) 1
    (dhsBlockBackUpperTailRowFlat i (U i))
    (dhsBlockBackUpperTailColumn i X)

/-- The actual conventional rounded RHS obtained by subtracting the strict
    upper product from the current block of the forward-solve output. -/
noncomputable def dhsBlockBackConventionalRHS {m r : ℕ}
    (fp : FPModel) (i : Fin m)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    Matrix (Fin r) (Fin 1) ℝ :=
  higham13_fl_matrixSub fp (Y i)
    (dhsBlockBackConventionalUpperProduct fp i U X)

/-- The actual conventional block-back-substitution solution, constructed in
    descending block-row order.

    At block row `i`, only already-computed strict-upper blocks are exposed to
    the rounded block product.  The current diagonal block is then solved by
    the repository's conventional `fl_backSub`.  The decreasing measure
    `m - i.val` makes the source's recursive execution order explicit. -/
noncomputable def dhsBlockBackConventionalSolution {m r : ℕ}
    (fp : FPModel)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (i : Fin m) : Matrix (Fin r) (Fin 1) ℝ :=
  fun a _ =>
    fl_backSub fp r (U i i)
      (fun b : Fin r =>
        dhsBlockBackConventionalRHS fp i U
          (fun j : Fin m =>
            if i.val < j.val then
              dhsBlockBackConventionalSolution fp U Y j
            else 0)
          Y b 0) a
termination_by m - i.val
decreasing_by omega

/-- The descending conventional block solution satisfies the exact per-row
    execution relation consumed by the Eq.13.15 local-solve analysis.

    The proof identifies the recursively visible tail with the corresponding
    masked tail of the completed solution.  Thus no independent execution
    hypothesis is needed when the solution is
    `dhsBlockBackConventionalSolution fp U Y`. -/
theorem dhsBlockBackConventionalSolution_execution {m r : ℕ}
    (fp : FPModel)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (i : Fin m) (a : Fin r) :
    dhsBlockBackConventionalSolution fp U Y i a 0 =
      fl_backSub fp r (U i i)
        (fun b : Fin r => dhsBlockBackConventionalRHS fp i U
          (dhsBlockBackConventionalSolution fp U Y) Y b 0) a := by
  rw [dhsBlockBackConventionalSolution]
  apply congrArg (fun rhs : Fin r → ℝ => fl_backSub fp r (U i i) rhs a)
  funext b
  have hTail :
      dhsBlockBackUpperTailColumn i
          (fun j : Fin m =>
            if i.val < j.val then
              dhsBlockBackConventionalSolution fp U Y j
            else 0) =
        dhsBlockBackUpperTailColumn i
          (dhsBlockBackConventionalSolution fp U Y) := by
    ext jt k
    simp only [dhsBlockBackUpperTailColumn]
    change
      (if i.val < (finProdFinEquiv.symm jt).1.val then
          (if i.val < (finProdFinEquiv.symm jt).1.val then
            dhsBlockBackConventionalSolution fp U Y
              (finProdFinEquiv.symm jt).1
          else 0) (finProdFinEquiv.symm jt).2 0
        else 0) =
        (if i.val < (finProdFinEquiv.symm jt).1.val then
          dhsBlockBackConventionalSolution fp U Y
            (finProdFinEquiv.symm jt).1 (finProdFinEquiv.symm jt).2 0
        else 0)
    by_cases hq : i.val < (finProdFinEquiv.symm jt).1.val
    · have hq' : i.val < jt.val / r := by simpa using hq
      simp [hq']
    · have hq' : ¬i.val < jt.val / r := by simpa using hq
      simp [hq']
  unfold dhsBlockBackConventionalRHS dhsBlockBackConventionalUpperProduct
  rw [hTail]

/-- A zero full upper suffix forces both the conventional row RHS and the
    original forward-solve block to be zero once the local Eq.13.15 equation
    is imposed.

    The conventional strict-tail product is exactly zero by its checked
    matrix-product error bound.  Eq.13.15 then makes the rounded subtraction
    zero.  Finally `gammaValid fp (m*r)` gives `u < 1`, so the relative
    subtraction model `fl(Y-0) = Y*(1+delta)` has a nonzero factor and forces
    `Y = 0`.  No subtract-by-zero exactness law is needed. -/
theorem dhs_block_back_conventional_rhs_eq_zero_of_upper_suffix_zero_and_eq13_15
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (c₅ normUii normDeltaUii : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp (m * r))
    (hSuffixZero : infNormVec (dhsBlockBackUpperSuffixVector i X) = 0)
    (hDiagonal :
      DiagonalBlockSolveFirstOrderSpec fp.u c₅ normUii normDeltaUii
        (U i i) DeltaDiag (X i)
        (dhsBlockBackConventionalRHS fp i U X Y)) :
    dhsBlockBackConventionalRHS fp i U X Y = 0 ∧ Y i = 0 := by
  have hSuffixVectorZero : dhsBlockBackUpperSuffixVector i X = 0 := by
    funext jt
    apply abs_eq_zero.mp
    apply le_antisymm
    · simpa [hSuffixZero] using
        abs_le_infNormVec (dhsBlockBackUpperSuffixVector i X) jt
    · exact abs_nonneg (dhsBlockBackUpperSuffixVector i X jt)
  have hTailNormZero :
      infNormVec (dhsBlockBackUpperTailVector i X) = 0 := by
    apply le_antisymm
    · calc
        infNormVec (dhsBlockBackUpperTailVector i X) ≤
            infNormVec (dhsBlockBackUpperSuffixVector i X) :=
          dhsBlockBackUpperTail_infNormVec_le_suffix i X
        _ = 0 := hSuffixZero
    · exact infNormVec_nonneg _
  have hTailVectorZero : dhsBlockBackUpperTailVector i X = 0 := by
    funext jt
    apply abs_eq_zero.mp
    apply le_antisymm
    · simpa [hTailNormZero] using
        abs_le_infNormVec (dhsBlockBackUpperTailVector i X) jt
    · exact abs_nonneg (dhsBlockBackUpperTailVector i X jt)
  have hXiZero : X i = 0 := by
    ext s k
    fin_cases k
    have hzero := congrFun hSuffixVectorZero (finProdFinEquiv (i, s))
    simpa using hzero
  have hDhatZero : dhsBlockBackConventionalRHS fp i U X Y = 0 := by
    have hEq := hDiagonal.equation
    rw [hXiZero] at hEq
    simpa using hEq.symm
  have hTailColumnZero : dhsBlockBackUpperTailColumn i X = 0 := by
    ext jt k
    fin_cases k
    exact congrFun hTailVectorZero jt
  have hChatZero : dhsBlockBackConventionalUpperProduct fp i U X = 0 := by
    rw [dhsBlockBackConventionalUpperProduct, hTailColumnZero]
    ext s k
    have herr := matMul_error_bound fp r (m * r) 1
      (dhsBlockBackUpperTailRowFlat i (U i)) 0 hγ s k
    apply abs_eq_zero.mp
    apply le_antisymm
    · simpa using herr
    · exact abs_nonneg
        (fl_matMul fp r (m * r) 1
          (dhsBlockBackUpperTailRowFlat i (U i)) 0 s k)
  have hu_lt_one : fp.u < 1 := by
    have hγ1 : gammaValid fp 1 :=
      gammaValid_mono fp (Nat.succ_le_iff.mpr (Nat.mul_pos hm hr)) hγ
    unfold gammaValid at hγ1
    simpa using hγ1
  have hYZero : Y i = 0 := by
    ext s k
    fin_cases k
    obtain ⟨delta, hdelta, hsub⟩ := fp.model_sub (Y i s 0) 0
    have hflzero : fp.fl_sub (Y i s 0) 0 = 0 := by
      have hd := congrFun (congrFun hDhatZero s) 0
      simpa [dhsBlockBackConventionalRHS, higham13_fl_matrixSub,
        hChatZero] using hd
    have hfactor : 1 + delta ≠ 0 := by
      have hdeltaLower : -1 < delta := by
        have hnegabs : -|delta| ≤ delta := neg_abs_le delta
        linarith
      linarith
    have hprod : Y i s 0 * (1 + delta) = 0 := by
      calc
        Y i s 0 * (1 + delta) =
            (Y i s 0 - 0) * (1 + delta) := by ring
        _ = fp.fl_sub (Y i s 0) 0 := hsub.symm
        _ = 0 := hflzero
    exact (mul_eq_zero.mp hprod).resolve_right hfactor
  exact ⟨hDhatZero, hYZero⟩

/-- Construct one source-correct conventional full-suffix row witness.

    A nonzero suffix uses the executable suffix perturbation theorem and its
    RHS-magnitude comparison.  In the zero-suffix case the preceding theorem
    derives the exact zero row from `gammaValid` and Eq.13.15, so the witness
    uses zero coefficient perturbation without any extra operational premise. -/
theorem dhs_block_back_upper_suffix_row_witness_from_conventional
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (cRhs normU c₅ normUii normDeltaUii : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp (m * r))
    (hcRhs : 0 ≤ cRhs) (hNormU : 0 ≤ normU)
    (hUTailU :
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hRhsScale : infNormVec (dhsBlockBackUpperSuffixVector i X) ≠ 0 →
      maxEntryNormRect hr (Nat.succ_pos 0) (Y i) +
          maxEntryNormRect hr (Nat.succ_pos 0)
            (dhsBlockBackConventionalUpperProduct fp i U X) ≤
        cRhs * normU * infNormVec (dhsBlockBackUpperSuffixVector i X))
    (hDiagonal :
      DiagonalBlockSolveFirstOrderSpec fp.u c₅ normUii normDeltaUii
        (U i i) DeltaDiag (X i)
        (dhsBlockBackConventionalRHS fp i U X Y)) :
    ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      dhsBlockBackConventionalRHS fp i U X Y +
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            U i j * X j) +
          (∑ j : Fin m, DeltaRow j * X j) = Y i ∧
      (∀ j : Fin m, j.val < i.val → DeltaRow j = 0) ∧
      (∀ j : Fin m, ∀ s t : Fin r,
        |DeltaRow j s t| ≤ rowPerturbBound) ∧
      FirstOrderLe fp.u
        ((((m * r : ℕ) : ℝ) ^ 2 + cRhs) * fp.u * normU)
        rowPerturbBound := by
  by_cases hXSuffix : infNormVec (dhsBlockBackUpperSuffixVector i X) = 0
  · obtain ⟨hDhatZero, hYZero⟩ :=
      dhs_block_back_conventional_rhs_eq_zero_of_upper_suffix_zero_and_eq13_15
        fp hm hr i c₅ normUii normDeltaUii U DeltaDiag X Y hγ hXSuffix
        hDiagonal
    have hTailNormZero :
        infNormVec (dhsBlockBackUpperTailVector i X) = 0 := by
      apply le_antisymm
      · calc
          infNormVec (dhsBlockBackUpperTailVector i X) ≤
              infNormVec (dhsBlockBackUpperSuffixVector i X) :=
            dhsBlockBackUpperTail_infNormVec_le_suffix i X
          _ = 0 := hXSuffix
      · exact infNormVec_nonneg _
    have hTailVectorZero : dhsBlockBackUpperTailVector i X = 0 := by
      funext jt
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa [hTailNormZero] using
          abs_le_infNormVec (dhsBlockBackUpperTailVector i X) jt
      · exact abs_nonneg (dhsBlockBackUpperTailVector i X jt)
    have hXZero : ∀ j : Fin m, i.val < j.val → X j = 0 := by
      intro j hij
      ext s k
      fin_cases k
      have hzero := congrFun hTailVectorZero (finProdFinEquiv (j, s))
      simpa [dhsBlockBackUpperTailVector_apply, hij] using hzero
    refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
    · rw [hDhatZero, hYZero]
      simp only [zero_add]
      have hTailSum :
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            U i j * X j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hij : i.val < j.val := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
        rw [hXZero j hij]
        simp
      rw [hTailSum]
      simp
    · simp
    · simp
    · apply FirstOrderLe.of_le
      exact mul_nonneg
        (mul_nonneg (add_nonneg (sq_nonneg (((m * r : ℕ) : ℝ))) hcRhs)
          fp.u_nonneg) hNormU
  · simpa [dhsBlockBackConventionalUpperProduct,
      dhsBlockBackConventionalRHS] using
      dhs_block_back_upper_suffix_row_perturbation_firstOrder_from_conventional_operations
        fp hm hr i cRhs normU (U i) X (Y i) hγ hUTailU hXSuffix
        (by simpa [dhsBlockBackConventionalUpperProduct] using
          hRhsScale hXSuffix)

/-- Construct one conventional strict-upper row witness without dividing by a
    zero tail norm.

    A nonzero tail uses the concrete rounded row theorem and its source
    RHS-magnitude comparison.  A zero tail uses the algorithm's explicit exact
    no-tail RHS relation and the zero coefficient perturbation. -/
theorem dhs_block_back_upper_row_witness_from_conventional_or_zero_tail
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (cRhs normU : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp (m * r))
    (hcRhs : 0 ≤ cRhs) (hNormU : 0 ≤ normU)
    (hUTailU :
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hRhsScale : infNormVec (dhsBlockBackUpperTailVector i X) ≠ 0 →
      maxEntryNormRect hr (Nat.succ_pos 0) (Y i) +
          maxEntryNormRect hr (Nat.succ_pos 0)
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i (U i))
              (dhsBlockBackUpperTailColumn i X)) ≤
        cRhs * normU * infNormVec (dhsBlockBackUpperTailVector i X))
    (hZeroTail : infNormVec (dhsBlockBackUpperTailVector i X) = 0 →
      higham13_fl_matrixSub fp (Y i)
          (fl_matMul fp r (m * r) 1
            (dhsBlockBackUpperTailRowFlat i (U i))
            (dhsBlockBackUpperTailColumn i X)) =
        Y i) :
    ∃ (DeltaRow : Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      higham13_fl_matrixSub fp (Y i)
            (fl_matMul fp r (m * r) 1
              (dhsBlockBackUpperTailRowFlat i (U i))
              (dhsBlockBackUpperTailColumn i X)) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            (U i j + DeltaRow j) * X j = Y i ∧
      (∀ j : Fin m, ¬i.val < j.val → DeltaRow j = 0) ∧
      (∀ j : Fin m, ∀ s t : Fin r,
        |DeltaRow j s t| ≤ rowPerturbBound) ∧
      FirstOrderLe fp.u
        ((((m * r : ℕ) : ℝ) ^ 2 + cRhs) * fp.u * normU)
        rowPerturbBound := by
  by_cases hXTail : infNormVec (dhsBlockBackUpperTailVector i X) = 0
  · have hTailZero : dhsBlockBackUpperTailVector i X = 0 := by
      funext jt
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa [hXTail] using
          abs_le_infNormVec (dhsBlockBackUpperTailVector i X) jt
      · exact abs_nonneg (dhsBlockBackUpperTailVector i X jt)
    have hXZero : ∀ j : Fin m, i.val < j.val → X j = 0 := by
      intro j hij
      ext s k
      fin_cases k
      have hzero := congrFun hTailZero (finProdFinEquiv (j, s))
      simpa [dhsBlockBackUpperTailVector_apply, hij] using hzero
    refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
    · rw [hZeroTail hXTail]
      have hsum :
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
            (U i j + (0 : Matrix (Fin r) (Fin r) ℝ)) * X j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hij : i.val < j.val := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
        rw [hXZero j hij]
        simp
      simpa using congrArg (fun Z => Y i + Z) hsum
    · simp
    · simp
    · apply FirstOrderLe.of_le
      exact mul_nonneg
        (mul_nonneg (add_nonneg (sq_nonneg (((m * r : ℕ) : ℝ))) hcRhs)
          fp.u_nonneg) hNormU
  · exact
      dhs_block_back_upper_row_perturbation_firstOrder_from_conventional_operations
        fp hm hr i cRhs normU (U i) X (Y i) hγ hUTailU hXTail
        (hRhsScale hXTail)

/-- Concrete all-row DHS back-substitution branch from conventional rounded
    strict-upper products/subtractions and every local Eq.13.15 solve.

    The only remaining row-analysis inputs are the source magnitude comparison
    for nonzero tails and the exact operational no-tail relation for zero
    tails.  From them this theorem constructs every row witness, aggregates the
    finite budgets, merges the diagonal perturbations, and reaches the selected
    global branch. -/
theorem dhs_block_back_substitution_firstOrder_from_conventional_upper_rows_and_eq13_15
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (cRhs c₅ cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp (m * r))
    (hcRhs : 0 ≤ cRhs) (hc₅ : 0 ≤ c₅)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) *
      ((((m * r : ℕ) : ℝ) ^ 2 + cRhs) + c₅)) ≤ cBack)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hRhsScale : ∀ i : Fin m,
      infNormVec (dhsBlockBackUpperTailVector i X) ≠ 0 →
        maxEntryNormRect hr (Nat.succ_pos 0) (Y i) +
            maxEntryNormRect hr (Nat.succ_pos 0)
              (dhsBlockBackConventionalUpperProduct fp i U X) ≤
          cRhs * normU * infNormVec (dhsBlockBackUpperTailVector i X))
    (hZeroTail : ∀ i : Fin m,
      infNormVec (dhsBlockBackUpperTailVector i X) = 0 →
        dhsBlockBackConventionalRHS fp i U X Y = Y i)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec fp.u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i)
        (dhsBlockBackConventionalRHS fp i U X Y)) :
    ∃ DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      DHSBlockBackSubstitutionFirstOrderSpec
        fp.u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  apply dhs_block_back_substitution_firstOrder_from_upper_row_witnesses_and_eq13_15
    hm hr fp.u c₅ (((m * r : ℕ) : ℝ) ^ 2 + cRhs) cBack
    normA normL normU normUii Lhat U DeltaDiag X Y
    (fun i => dhsBlockBackConventionalRHS fp i U X Y)
    fp.u_nonneg hc₅ (add_nonneg (sq_nonneg (((m * r : ℕ) : ℝ))) hcRhs)
    hA hL hU hUUpper hNormUii hLhat hc
  · intro i
    simpa [dhsBlockBackConventionalUpperProduct,
      dhsBlockBackConventionalRHS] using
      dhs_block_back_upper_row_witness_from_conventional_or_zero_tail
        fp hm hr i cRhs normU U X Y hγ hcRhs hU (hUTailU i)
        (hRhsScale i) (hZeroTail i)
  · exact hDiagonal

/-- Under the standard small-roundoff regime `(m*r)u <= 1/2`, the actual
    rounded strict-upper row product is bounded by twice the exact dimension
    factor times the global upper-factor scale and full computed suffix norm. -/
theorem dhsBlockBackConventionalUpperProduct_maxEntry_le_two_dim
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (normU : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmall : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hUTailU :
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU) :
    maxEntryNormRect hr (Nat.succ_pos 0)
        (dhsBlockBackConventionalUpperProduct fp i U X) ≤
      2 * ((m * r : ℕ) : ℝ) * normU *
        infNormVec (dhsBlockBackUpperSuffixVector i X) := by
  let A := dhsBlockBackUpperTailRowFlat i (U i)
  let B := dhsBlockBackUpperTailColumn i X
  let suffixNorm := infNormVec (dhsBlockBackUpperSuffixVector i X)
  have hγ : gammaValid fp (m * r) := by
    unfold gammaValid
    linarith
  have hNormU : 0 ≤ normU :=
    le_trans (maxEntryNormRect_nonneg hr (Nat.mul_pos hm hr) A) hUTailU
  have hGammaLeOne : gamma fp (m * r) ≤ 1 := by
    have hgammaLinear :=
      gamma_le_two_mul_n_u_of_nu_le_half fp (m * r) hSmall
    linarith
  have hGammaNonneg : 0 ≤ gamma fp (m * r) := gamma_nonneg fp hγ
  have hTailSuffix :
      infNormVec (dhsBlockBackUpperTailVector i X) ≤ suffixNorm :=
    dhsBlockBackUpperTail_infNormVec_le_suffix i X
  apply maxEntryNormRect_le_of_entry_abs_le
  intro s k
  have hsum :
      (∑ jt : Fin (m * r), |A s jt| * |B jt k|) ≤
        ((m * r : ℕ) : ℝ) * (normU * suffixNorm) := by
    calc
      (∑ jt : Fin (m * r), |A s jt| * |B jt k|) ≤
          ∑ _jt : Fin (m * r), normU * suffixNorm := by
        apply Finset.sum_le_sum
        intro jt _hjt
        apply mul_le_mul
        · exact le_trans
            (entry_le_maxEntryNormRect hr (Nat.mul_pos hm hr) A s jt)
            hUTailU
        · fin_cases k
          exact le_trans
            (abs_le_infNormVec (dhsBlockBackUpperTailVector i X) jt)
            hTailSuffix
        · exact abs_nonneg (B jt k)
        · exact hNormU
      _ = ((m * r : ℕ) : ℝ) * (normU * suffixNorm) := by simp
  have herr := matMul_error_bound fp r (m * r) 1 A B hγ s k
  have hexact :
      |∑ jt : Fin (m * r), A s jt * B jt k| ≤
        ∑ jt : Fin (m * r), |A s jt| * |B jt k| := by
    calc
      |∑ jt : Fin (m * r), A s jt * B jt k| ≤
          ∑ jt : Fin (m * r), |A s jt * B jt k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ jt : Fin (m * r), |A s jt| * |B jt k| := by
        apply Finset.sum_congr rfl
        intro jt _hjt
        rw [abs_mul]
  change |fl_matMul fp r (m * r) 1 A B s k| ≤ _
  calc
    |fl_matMul fp r (m * r) 1 A B s k| =
        |(fl_matMul fp r (m * r) 1 A B s k -
              ∑ jt : Fin (m * r), A s jt * B jt k) +
            ∑ jt : Fin (m * r), A s jt * B jt k| := by ring_nf
    _ ≤ |fl_matMul fp r (m * r) 1 A B s k -
              ∑ jt : Fin (m * r), A s jt * B jt k| +
            |∑ jt : Fin (m * r), A s jt * B jt k| := abs_add_le _ _
    _ ≤ gamma fp (m * r) *
              (∑ jt : Fin (m * r), |A s jt| * |B jt k|) +
            (∑ jt : Fin (m * r), |A s jt| * |B jt k|) :=
      add_le_add herr hexact
    _ ≤ 1 * (((m * r : ℕ) : ℝ) * (normU * suffixNorm)) +
            (((m * r : ℕ) : ℝ) * (normU * suffixNorm)) := by
      apply add_le_add
      · exact mul_le_mul hGammaLeOne hsum
          (Finset.sum_nonneg (fun jt _ =>
            mul_nonneg (abs_nonneg (A s jt)) (abs_nonneg (B jt k))))
          (by norm_num)
      · exact hsum
    _ = 2 * ((m * r : ℕ) : ℝ) * normU * suffixNorm := by ring

/-- Derive the formerly external full-suffix RHS-magnitude comparison from
    the conventional row operations, Eq.13.15, and explicit source-style
    smallness/norm bounds.

    The rounded tail product contributes `2*(m*r)`.  The diagonal equation
    bounds the computed RHS by `2*r`, while the relative subtraction factor is
    bounded away from zero by `(m*r)u <= 1/2`.  Combining these estimates gives
    the concrete coefficient `4*((m*r)+r)`. -/
theorem dhs_block_back_conventional_rhs_scale_of_small_roundoff_and_diagonal_bounds
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r) (i : Fin m)
    (normU : ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hUTailU :
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hUiiU : maxEntryNorm hr (U i i) ≤ normU)
    (hDeltaDiagU : maxEntryNorm hr DeltaDiag ≤ normU)
    (hDiagonalEquation :
      (U i i + DeltaDiag) * X i =
        dhsBlockBackConventionalRHS fp i U X Y) :
    maxEntryNormRect hr (Nat.succ_pos 0) (Y i) +
        maxEntryNormRect hr (Nat.succ_pos 0)
          (dhsBlockBackConventionalUpperProduct fp i U X) ≤
      (4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) * normU *
        infNormVec (dhsBlockBackUpperSuffixVector i X) := by
  let suffixNorm := infNormVec (dhsBlockBackUpperSuffixVector i X)
  let Chat := dhsBlockBackConventionalUpperProduct fp i U X
  let Dhat := dhsBlockBackConventionalRHS fp i U X Y
  have hNormU : 0 ≤ normU :=
    le_trans (maxEntryNorm_nonneg hr (U i i)) hUiiU
  have hSuffixNonneg : 0 ≤ suffixNorm := infNormVec_nonneg _
  have hSmallUnit : fp.u ≤ 1 / 2 := by
    have hone : (1 : ℝ) ≤ ((m * r : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.mul_pos hm hr)
    have hu_le : fp.u ≤ ((m * r : ℕ) : ℝ) * fp.u := by
      calc
        fp.u = 1 * fp.u := by ring
        _ ≤ ((m * r : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right hone fp.u_nonneg
    exact le_trans hu_le hSmallProduct
  have hXiSuffix :
      maxEntryNormRect hr (Nat.succ_pos 0) (X i) ≤ suffixNorm := by
    rw [maxEntryNormRect_single_col_eq_infNormVec]
    exact dhsBlockBackCurrentBlock_infNormVec_le_suffix i X
  have hUPlusDelta :
      maxEntryNormRect hr hr (U i i + DeltaDiag) ≤ 2 * normU := by
    rw [maxEntryNormRect_eq_maxEntryNorm hr]
    calc
      maxEntryNorm hr (U i i + DeltaDiag) ≤
          maxEntryNorm hr (U i i) + maxEntryNorm hr DeltaDiag :=
        maxEntryNorm_add_le hr (U i i) DeltaDiag
      _ ≤ normU + normU := add_le_add hUiiU hDeltaDiagU
      _ = 2 * normU := by ring
  have hDhatNorm :
      maxEntryNormRect hr (Nat.succ_pos 0) Dhat ≤
        2 * (r : ℝ) * normU * suffixNorm := by
    simp only [Dhat]
    rw [← hDiagonalEquation]
    calc
      maxEntryNormRect hr (Nat.succ_pos 0)
          ((U i i + DeltaDiag) * X i) ≤
          (r : ℝ) * maxEntryNormRect hr hr (U i i + DeltaDiag) *
            maxEntryNormRect hr (Nat.succ_pos 0) (X i) := by
        simpa [rectMatMul, Matrix.mul_apply] using
          maxEntryNormRect_rectMatMul_le hr hr (Nat.succ_pos 0)
            (U i i + DeltaDiag) (X i)
      _ ≤ (r : ℝ) * (2 * normU) * suffixNorm := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hUPlusDelta (Nat.cast_nonneg r))
          hXiSuffix
          (maxEntryNormRect_nonneg hr (Nat.succ_pos 0) (X i))
          (mul_nonneg (Nat.cast_nonneg r)
            (mul_nonneg (by norm_num) hNormU))
      _ = 2 * (r : ℝ) * normU * suffixNorm := by ring
  have hChatNorm :
      maxEntryNormRect hr (Nat.succ_pos 0) Chat ≤
        2 * ((m * r : ℕ) : ℝ) * normU * suffixNorm :=
    dhsBlockBackConventionalUpperProduct_maxEntry_le_two_dim
      fp hm hr i normU U X hSmallProduct hUTailU
  have hYNorm :
      maxEntryNormRect hr (Nat.succ_pos 0) (Y i) ≤
        2 * maxEntryNormRect hr (Nat.succ_pos 0) Dhat +
          maxEntryNormRect hr (Nat.succ_pos 0) Chat := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro s k
    fin_cases k
    obtain ⟨delta, hdelta, hsub⟩ := fp.model_sub (Y i s 0) (Chat s 0)
    have hDhatEntry :
        Dhat s 0 = (Y i s 0 - Chat s 0) * (1 + delta) := by
      simpa [Dhat, dhsBlockBackConventionalRHS, higham13_fl_matrixSub,
        Chat] using hsub
    have hFactorHalf : (1 / 2 : ℝ) ≤ |1 + delta| := by
      have hdeltaLower : -(1 / 2 : ℝ) ≤ delta := by
        have hnegabs : -|delta| ≤ delta := neg_abs_le delta
        linarith
      have hfactorNonneg : 0 ≤ 1 + delta := by linarith
      rw [abs_of_nonneg hfactorNonneg]
      linarith
    have hDiff : |Y i s 0 - Chat s 0| ≤ 2 * |Dhat s 0| := by
      have hhalfMul :
          |Y i s 0 - Chat s 0| * (1 / 2 : ℝ) ≤ |Dhat s 0| := by
        calc
          |Y i s 0 - Chat s 0| * (1 / 2 : ℝ) ≤
              |Y i s 0 - Chat s 0| * |1 + delta| :=
            mul_le_mul_of_nonneg_left hFactorHalf (abs_nonneg _)
          _ = |Dhat s 0| := by rw [hDhatEntry, abs_mul]
      linarith
    calc
      |Y i s 0| = |(Y i s 0 - Chat s 0) + Chat s 0| := by ring_nf
      _ ≤ |Y i s 0 - Chat s 0| + |Chat s 0| := abs_add_le _ _
      _ ≤ 2 * |Dhat s 0| + |Chat s 0| := add_le_add hDiff le_rfl
      _ ≤ 2 * maxEntryNormRect hr (Nat.succ_pos 0) Dhat +
          maxEntryNormRect hr (Nat.succ_pos 0) Chat := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) Dhat s 0)
            (by norm_num))
          (entry_le_maxEntryNormRect hr (Nat.succ_pos 0) Chat s 0)
  calc
    maxEntryNormRect hr (Nat.succ_pos 0) (Y i) +
          maxEntryNormRect hr (Nat.succ_pos 0) Chat ≤
        (2 * maxEntryNormRect hr (Nat.succ_pos 0) Dhat +
            maxEntryNormRect hr (Nat.succ_pos 0) Chat) +
          maxEntryNormRect hr (Nat.succ_pos 0) Chat := add_le_add hYNorm le_rfl
    _ ≤ (2 * (2 * (r : ℝ) * normU * suffixNorm) +
            (2 * ((m * r : ℕ) : ℝ) * normU * suffixNorm)) +
          (2 * ((m * r : ℕ) : ℝ) * normU * suffixNorm) := by
      gcongr
    _ = (4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) * normU *
          suffixNorm := by ring

/-- Concrete source-correct all-row DHS back-substitution branch from the
    conventional rounded strict-tail products, following subtractions, and
    every local Eq.13.15 solve.

    Each nonzero full suffix consumes the source RHS-magnitude comparison.
    A zero suffix is discharged internally from `gammaValid` and Eq.13.15.
    The assembled RHS-formation perturbations may occupy `j = i`; they are
    combined exactly once with the local diagonal-solve perturbations before
    the existing fixed-row, flattening, and product-transport layers. -/
theorem dhs_block_back_substitution_firstOrder_from_conventional_suffix_rows_and_eq13_15
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (cRhs c₅ cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hγ : gammaValid fp (m * r))
    (hcRhs : 0 ≤ cRhs) (hc₅ : 0 ≤ c₅)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) *
      ((((m * r : ℕ) : ℝ) ^ 2 + cRhs) + c₅)) ≤ cBack)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hRhsScale : ∀ i : Fin m,
      infNormVec (dhsBlockBackUpperSuffixVector i X) ≠ 0 →
        maxEntryNormRect hr (Nat.succ_pos 0) (Y i) +
            maxEntryNormRect hr (Nat.succ_pos 0)
              (dhsBlockBackConventionalUpperProduct fp i U X) ≤
          cRhs * normU * infNormVec (dhsBlockBackUpperSuffixVector i X))
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec fp.u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i)
        (dhsBlockBackConventionalRHS fp i U X Y)) :
    ∃ DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      DHSBlockBackSubstitutionFirstOrderSpec
        fp.u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  apply dhs_block_back_substitution_firstOrder_from_suffix_row_witnesses_and_eq13_15
    hm hr fp.u c₅ (((m * r : ℕ) : ℝ) ^ 2 + cRhs) cBack
    normA normL normU normUii Lhat U DeltaDiag X Y
    (fun i => dhsBlockBackConventionalRHS fp i U X Y)
    fp.u_nonneg hc₅ (add_nonneg (sq_nonneg (((m * r : ℕ) : ℝ))) hcRhs)
    hA hL hU hUUpper hNormUii hLhat hc
  · intro i
    exact
      dhs_block_back_upper_suffix_row_witness_from_conventional
        fp hm hr i cRhs normU c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i)) U (DeltaDiag i) X Y hγ hcRhs hU
        (hUTailU i) (hRhsScale i) (hDiagonal i)
  · exact hDiagonal

/-- Fully derived conventional block-back-substitution branch under explicit
    DHS small-roundoff and local diagonal-solver bounds.

    This discharges the nonzero-suffix magnitude premise of the preceding
    all-row theorem with coefficient `4*((m*r)+r)`.  The local concrete bound
    `||DeltaDiag_i||max <= c₅*u*normUii_i`, together with `c₅*u <= 1`,
    supplies the diagonal scale needed by the RHS comparison. -/
theorem dhs_block_back_substitution_firstOrder_from_conventional_suffix_rows_of_small_roundoff
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (c₅ cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hc₅ : 0 ≤ c₅) (hSmallDiag : c₅ * fp.u ≤ 1)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) *
      ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) + c₅)) ≤ cBack)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hUiiNorm : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normUii i)
    (hDeltaDiagConcrete : ∀ i : Fin m,
      maxEntryNorm hr (DeltaDiag i) ≤ c₅ * fp.u * normUii i)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec fp.u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i)
        (dhsBlockBackConventionalRHS fp i U X Y)) :
    ∃ DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      DHSBlockBackSubstitutionFirstOrderSpec
        fp.u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  have hγ : gammaValid fp (m * r) := by
    unfold gammaValid
    linarith
  apply
    dhs_block_back_substitution_firstOrder_from_conventional_suffix_rows_and_eq13_15
      fp hm hr (4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) c₅ cBack
      normA normL normU normUii Lhat U DeltaDiag X Y hγ
      (mul_nonneg (by norm_num)
        (add_nonneg (Nat.cast_nonneg (m * r)) (Nat.cast_nonneg r)))
      hc₅ hA hL hU hUUpper hNormUii hLhat hc hUTailU
  · intro i _hSuffixNonzero
    have hUiiU : maxEntryNorm hr (U i i) ≤ normU :=
      le_trans (hUiiNorm i) (hNormUii i)
    have hNormUiiNonneg : 0 ≤ normUii i :=
      le_trans (maxEntryNorm_nonneg hr (U i i)) (hUiiNorm i)
    have hDeltaDiagU : maxEntryNorm hr (DeltaDiag i) ≤ normU := by
      calc
        maxEntryNorm hr (DeltaDiag i) ≤
            c₅ * fp.u * normUii i := hDeltaDiagConcrete i
        _ ≤ 1 * normUii i :=
          mul_le_mul_of_nonneg_right hSmallDiag hNormUiiNonneg
        _ ≤ 1 * normU :=
          mul_le_mul_of_nonneg_left (hNormUii i) (by norm_num)
        _ = normU := one_mul normU
    exact
      dhs_block_back_conventional_rhs_scale_of_small_roundoff_and_diagonal_bounds
        fp hm hr i normU U (DeltaDiag i) X Y hSmallProduct
        (hUTailU i) hUiiU hDeltaDiagU (hDiagonal i).equation
  · exact hDiagonal

/-- The fully derived conventional suffix-row analysis, retaining its
    flattened row certificate as well as the global back-substitution spec.

    This is the entrywise-strengthened companion to
    `dhs_block_back_substitution_firstOrder_from_conventional_suffix_rows_of_small_roundoff`.
    Its row coefficient is the exact assembled
    `n^2 + 4*(n+r) + c₅`, before the final left-product factor `n`. -/
theorem
    dhs_block_back_substitution_rows_and_firstOrder_from_conventional_suffix_rows_of_small_roundoff
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (c₅ cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hc₅ : 0 ≤ c₅) (hSmallDiag : c₅ * fp.u ≤ 1)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) *
      ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) + c₅)) ≤ cBack)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hUiiNorm : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normUii i)
    (hDeltaDiagConcrete : ∀ i : Fin m,
      maxEntryNorm hr (DeltaDiag i) ≤ c₅ * fp.u * normUii i)
    (hDiagonal : ∀ i : Fin m,
      DiagonalBlockSolveFirstOrderSpec fp.u c₅ (normUii i)
        (maxEntryNorm hr (DeltaDiag i))
        (U i i) (DeltaDiag i) (X i)
        (dhsBlockBackConventionalRHS fp i U X Y)) :
    ∃ (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
        (rowPerturbBound : ℝ),
      DHSBlockBackSubstitutionRowsFirstOrderSpec
        fp.u
        ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) + c₅)
        normU rowPerturbBound
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) ∧
      DHSBlockBackSubstitutionFirstOrderSpec
        fp.u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  have hγ : gammaValid fp (m * r) := by
    unfold gammaValid
    linarith
  apply
    dhs_block_back_substitution_rows_and_firstOrder_from_suffix_row_witnesses_and_eq13_15
      hm hr fp.u c₅
      (((m * r : ℕ) : ℝ) ^ 2 +
        4 * (((m * r : ℕ) : ℝ) + (r : ℝ)))
      cBack normA normL normU normUii Lhat U DeltaDiag X Y
      (fun i => dhsBlockBackConventionalRHS fp i U X Y)
      fp.u_nonneg hc₅
      (add_nonneg (sq_nonneg (((m * r : ℕ) : ℝ)))
        (mul_nonneg (by norm_num)
          (add_nonneg (Nat.cast_nonneg (m * r)) (Nat.cast_nonneg r))))
      hA hL hU hUUpper hNormUii hLhat hc
  · intro i
    apply dhs_block_back_upper_suffix_row_witness_from_conventional
      fp hm hr i (4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) normU c₅
      (normUii i) (maxEntryNorm hr (DeltaDiag i)) U (DeltaDiag i)
      X Y hγ
      (mul_nonneg (by norm_num)
        (add_nonneg (Nat.cast_nonneg (m * r)) (Nat.cast_nonneg r)))
      hU (hUTailU i)
    · intro _hSuffixNonzero
      have hUiiU : maxEntryNorm hr (U i i) ≤ normU :=
        le_trans (hUiiNorm i) (hNormUii i)
      have hNormUiiNonneg : 0 ≤ normUii i :=
        le_trans (maxEntryNorm_nonneg hr (U i i)) (hUiiNorm i)
      have hDeltaDiagU : maxEntryNorm hr (DeltaDiag i) ≤ normU := by
        calc
          maxEntryNorm hr (DeltaDiag i) ≤
              c₅ * fp.u * normUii i := hDeltaDiagConcrete i
          _ ≤ 1 * normUii i :=
            mul_le_mul_of_nonneg_right hSmallDiag hNormUiiNonneg
          _ ≤ 1 * normU :=
            mul_le_mul_of_nonneg_left (hNormUii i) (by norm_num)
          _ = normU := one_mul normU
      exact
        dhs_block_back_conventional_rhs_scale_of_small_roundoff_and_diagonal_bounds
          fp hm hr i normU U (DeltaDiag i) X Y hSmallProduct
          (hUTailU i) hUiiU hDeltaDiagU (hDiagonal i).equation
    · exact hDiagonal i
  · exact hDiagonal

/-- Concrete Eq.13.15 diagonal-block solve family from the conventional
    triangular solver used by Algorithm 13.3 Implementation 1.

    If every computed block `X i` is the result of `fl_backSub` on the actual
    rounded block-row right-hand side, the conventional backward-error theorem
    selects one coefficient perturbation per diagonal block.  Under
    `r*u <= 1/2`, these perturbations satisfy the raw leading-term bound
    `||DeltaDiag_i||max <= 2*r*u*normUii_i`, as well as the named first-order
    Eq.13.15 specification consumed by the DHS suffix-row assembly. -/
theorem dhs_conventional_diagonal_block_solve_specs
    {m r : ℕ}
    (fp : FPModel) (hr : 0 < r)
    (normUii : Fin m → ℝ)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallBlock : (r : ℝ) * fp.u ≤ 1 / 2)
    (hUiiNorm : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normUii i)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0)
    (hXExec : ∀ i : Fin m, ∀ a : Fin r,
      X i a 0 = fl_backSub fp r (U i i)
        (fun b : Fin r => dhsBlockBackConventionalRHS fp i U X Y b 0) a) :
    ∃ DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ,
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * normUii i) ∧
      ∀ i : Fin m,
        DiagonalBlockSolveFirstOrderSpec fp.u (2 * (r : ℝ)) (normUii i)
          (maxEntryNorm hr (DeltaDiag i))
          (U i i) (DeltaDiag i) (X i)
          (dhsBlockBackConventionalRHS fp i U X Y) := by
  classical
  have hGammaValid : gammaValid fp r := by
    unfold gammaValid
    linarith
  have hGammaLe : gamma fp r ≤ 2 * ((r : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp r hSmallBlock
  have hWitness : ∀ i : Fin m,
      ∃ Delta : Matrix (Fin r) (Fin r) ℝ,
        (∀ a b : Fin r,
          |Delta a b| ≤ gamma fp r * |U i i a b|) ∧
        (U i i + Delta) * X i =
          dhsBlockBackConventionalRHS fp i U X Y := by
    intro i
    rcases
        backSub_backward_error fp r (U i i)
          (fun b : Fin r => dhsBlockBackConventionalRHS fp i U X Y b 0)
          (hDiag i) (hUpper i) hGammaValid with
      ⟨Delta, hDelta, hEquation⟩
    refine ⟨Delta, hDelta, ?_⟩
    ext a j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simpa [Matrix.mul_apply, hXExec i] using hEquation a
  choose DeltaDiag hDeltaEntry hDeltaEquation using hWitness
  have hDeltaNorm : ∀ i : Fin m,
      maxEntryNorm hr (DeltaDiag i) ≤
        (2 * (r : ℝ)) * fp.u * normUii i := by
    intro i
    have hGammaNonneg : 0 ≤ gamma fp r := gamma_nonneg fp hGammaValid
    have hNormUiiNonneg : 0 ≤ normUii i :=
      le_trans (maxEntryNorm_nonneg hr (U i i)) (hUiiNorm i)
    apply maxEntryNorm_le_of_entry_le_bound
    intro a b
    calc
      |DeltaDiag i a b| ≤ gamma fp r * |U i i a b| :=
        hDeltaEntry i a b
      _ ≤ gamma fp r * maxEntryNorm hr (U i i) :=
        mul_le_mul_of_nonneg_left
          (entry_le_maxEntryNorm hr (U i i) a b) hGammaNonneg
      _ ≤ gamma fp r * normUii i :=
        mul_le_mul_of_nonneg_left (hUiiNorm i) hGammaNonneg
      _ ≤ (2 * ((r : ℝ) * fp.u)) * normUii i :=
        mul_le_mul_of_nonneg_right hGammaLe hNormUiiNonneg
      _ = (2 * (r : ℝ)) * fp.u * normUii i := by ring
  refine ⟨DeltaDiag, hDeltaNorm, ?_⟩
  intro i
  exact ⟨hDeltaEquation i, FirstOrderLe.of_le (hDeltaNorm i)⟩

/-- Source-correct concrete DHS block-back-substitution branch with the local
    Eq.13.15 solves instantiated by conventional per-block back substitution.

    The global small-roundoff condition implies `r*u <= 1/2`; hence the
    preceding theorem supplies all diagonal perturbations with coefficient
    `c₅ = 2*r`.  Those witnesses are then combined with the conventional
    rounded suffix products/subtractions, closing both the local diagonal
    solver bound and the global RHS-scale premise in one executable branch. -/
theorem dhs_block_back_substitution_firstOrder_from_conventional_local_backSub
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) *
      ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) +
        2 * (r : ℝ))) ≤ cBack)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hUiiNorm : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normUii i)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0)
    (hXExec : ∀ i : Fin m, ∀ a : Fin r,
      X i a 0 = fl_backSub fp r (U i i)
        (fun b : Fin r => dhsBlockBackConventionalRHS fp i U X Y b 0) a) :
    ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * normUii i) ∧
      (∀ i : Fin m,
        DiagonalBlockSolveFirstOrderSpec fp.u (2 * (r : ℝ)) (normUii i)
          (maxEntryNorm hr (DeltaDiag i))
          (U i i) (DeltaDiag i) (X i)
          (dhsBlockBackConventionalRHS fp i U X Y)) ∧
      DHSBlockBackSubstitutionFirstOrderSpec
        fp.u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin X) (blockMatrixRowsFlatFin Y) := by
  have hrNat : r ≤ m * r := by
    calc
      r = 1 * r := by simp
      _ ≤ m * r := Nat.mul_le_mul_right r (by omega)
  have hrReal : (r : ℝ) ≤ ((m * r : ℕ) : ℝ) := by
    exact_mod_cast hrNat
  have hSmallBlock : (r : ℝ) * fp.u ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hrReal fp.u_nonneg) hSmallProduct
  rcases
      dhs_conventional_diagonal_block_solve_specs
        fp hr normUii U X Y hSmallBlock hUiiNorm hDiag hUpper hXExec with
    ⟨DeltaDiag, hDeltaDiag, hDiagonal⟩
  have hSmallDiag : (2 * (r : ℝ)) * fp.u ≤ 1 := by
    calc
      (2 * (r : ℝ)) * fp.u = 2 * ((r : ℝ) * fp.u) := by ring
      _ ≤ 2 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hSmallBlock (by norm_num)
      _ = 1 := by norm_num
  rcases
      dhs_block_back_substitution_firstOrder_from_conventional_suffix_rows_of_small_roundoff
        fp hm hr (2 * (r : ℝ)) cBack normA normL normU normUii
        Lhat U DeltaDiag X Y hSmallProduct
        (mul_nonneg (by norm_num) (Nat.cast_nonneg r)) hSmallDiag
        hA hL hU hUUpper hNormUii hLhat hc hUTailU hUiiNorm
        hDeltaDiag hDiagonal with
    ⟨DeltaU, hBack⟩
  exact ⟨DeltaDiag, DeltaU, hDeltaDiag, hDiagonal, hBack⟩

/-- Fully instantiated conventional DHS block-back-substitution branch for
    the descending recursive block solution.

    This removes the last operational premise from
    `dhs_block_back_substitution_firstOrder_from_conventional_local_backSub`:
    the computed blocks are the named recursive solution, whose execution
    equation is proved above.  The conclusion simultaneously supplies every
    local Eq.13.15 perturbation and the flattened global DHS back spec. -/
theorem
    dhs_block_back_substitution_firstOrder_from_conventional_recursive_block_solution
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) *
      ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) +
        2 * (r : ℝ))) ≤ cBack)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hUiiNorm : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normUii i)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0) :
    ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * normUii i) ∧
      (∀ i : Fin m,
        DiagonalBlockSolveFirstOrderSpec fp.u (2 * (r : ℝ)) (normUii i)
          (maxEntryNorm hr (DeltaDiag i))
          (U i i) (DeltaDiag i)
          (dhsBlockBackConventionalSolution fp U Y i)
          (dhsBlockBackConventionalRHS fp i U
            (dhsBlockBackConventionalSolution fp U Y) Y)) ∧
      DHSBlockBackSubstitutionFirstOrderSpec
        fp.u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin (dhsBlockBackConventionalSolution fp U Y))
        (blockMatrixRowsFlatFin Y) := by
  exact
    dhs_block_back_substitution_firstOrder_from_conventional_local_backSub
      fp hm hr cBack normA normL normU normUii Lhat U
      (dhsBlockBackConventionalSolution fp U Y) Y hSmallProduct
      hA hL hU hUUpper hNormUii hLhat hc hUTailU hUiiNorm hDiag hUpper
      (dhsBlockBackConventionalSolution_execution fp U Y)

/-- The recursive conventional block solution together with the retained
    flattened back-row certificate.

    Besides the local Eq.13.15 family and global back spec, this endpoint
    exposes the assembled entrywise perturbation bound needed by the concrete
    forward/back cross-product proof. -/
theorem
    dhs_block_back_substitution_rows_and_firstOrder_from_conventional_recursive_block_solution
    {m r : ℕ}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (cBack normA normL normU : ℝ)
    (normUii : Fin m → ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (Y : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hNormUii : ∀ i : Fin m, normUii i ≤ normU)
    (hLhat : maxEntryNorm (Nat.mul_pos hm hr)
      (blockMatrixFlatFin Lhat) ≤ normL)
    (hc : (((m * r : ℕ) : ℝ) *
      ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) +
        2 * (r : ℝ))) ≤ cBack)
    (hUTailU : ∀ i : Fin m,
      maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤ normU)
    (hUiiNorm : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normUii i)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0) :
    ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
      (rowPerturbBound : ℝ),
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * normUii i) ∧
      (∀ i : Fin m,
        DiagonalBlockSolveFirstOrderSpec fp.u (2 * (r : ℝ)) (normUii i)
          (maxEntryNorm hr (DeltaDiag i))
          (U i i) (DeltaDiag i)
          (dhsBlockBackConventionalSolution fp U Y i)
          (dhsBlockBackConventionalRHS fp i U
            (dhsBlockBackConventionalSolution fp U Y) Y)) ∧
      DHSBlockBackSubstitutionRowsFirstOrderSpec
        fp.u
        ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) + 2 * (r : ℝ))
        normU rowPerturbBound
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin (dhsBlockBackConventionalSolution fp U Y))
        (blockMatrixRowsFlatFin Y) ∧
      DHSBlockBackSubstitutionFirstOrderSpec
        fp.u cBack normA normL normU
        (maxEntryNorm (Nat.mul_pos hm hr)
          (blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU))
        (blockMatrixFlatFin U) (blockMatrixFlatFin DeltaU)
        (blockMatrixRowsFlatFin (dhsBlockBackConventionalSolution fp U Y))
        (blockMatrixRowsFlatFin Y) := by
  have hrNat : r ≤ m * r := by
    calc
      r = 1 * r := by simp
      _ ≤ m * r := Nat.mul_le_mul_right r (by omega)
  have hrReal : (r : ℝ) ≤ ((m * r : ℕ) : ℝ) := by
    exact_mod_cast hrNat
  have hSmallBlock : (r : ℝ) * fp.u ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hrReal fp.u_nonneg) hSmallProduct
  rcases dhs_conventional_diagonal_block_solve_specs
      fp hr normUii U (dhsBlockBackConventionalSolution fp U Y) Y
      hSmallBlock hUiiNorm hDiag hUpper
      (dhsBlockBackConventionalSolution_execution fp U Y) with
    ⟨DeltaDiag, hDeltaDiag, hDiagonal⟩
  have hSmallDiag : (2 * (r : ℝ)) * fp.u ≤ 1 := by
    calc
      (2 * (r : ℝ)) * fp.u = 2 * ((r : ℝ) * fp.u) := by ring
      _ ≤ 2 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hSmallBlock (by norm_num)
      _ = 1 := by norm_num
  rcases
      dhs_block_back_substitution_rows_and_firstOrder_from_conventional_suffix_rows_of_small_roundoff
        fp hm hr (2 * (r : ℝ)) cBack normA normL normU normUii
        Lhat U DeltaDiag (dhsBlockBackConventionalSolution fp U Y) Y
        hSmallProduct (mul_nonneg (by norm_num) (Nat.cast_nonneg r))
        hSmallDiag hA hL hU hUUpper hNormUii hLhat hc hUTailU hUiiNorm
        hDeltaDiag hDiagonal with
    ⟨DeltaU, rowPerturbBound, hRows, hBack⟩
  exact ⟨DeltaDiag, DeltaU, rowPerturbBound,
    hDeltaDiag, hDiagonal, hRows, hBack⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 back-substitution branch for
    the conventional flattened algorithm and one right-hand side.

    The Chapter 8 backward-error theorem supplies one coefficient perturbation
    `DeltaU` shared by the single computed solution column.  Left multiplication
    by `Lhat`, the entrywise max product law, and the exact rational `gamma`
    expansion give the DHS back spec with coefficient `n^2`. -/
theorem
    dhs_block_back_substitution_firstOrder_from_conventional_backSub_single_rhs
    {n : ℕ}
    (fp : FPModel) (hn : 0 < n) (normA : ℝ)
    (Lhat Uhat : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (hA : 0 ≤ normA)
    (hdiag : ∀ i : Fin n, Uhat i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → Uhat i j = 0)
    (hγ : gammaValid fp n) :
    ∃ DeltaU : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, |DeltaU i j| ≤ gamma fp n * |Uhat i j|) ∧
        DHSBlockBackSubstitutionFirstOrderSpec
          fp.u ((n : ℝ) ^ 2)
          normA (maxEntryNorm hn Lhat) (maxEntryNorm hn Uhat)
          (maxEntryNorm hn (Lhat * DeltaU))
          Uhat DeltaU
          (fun i (_j : Fin 1) => fl_backSub fp n Uhat y i)
          (fun i (_j : Fin 1) => y i) := by
  rcases backSub_backward_error fp n Uhat y hdiag hupper hγ with
    ⟨DeltaURaw, hDeltaU, hEquation⟩
  let DeltaU : Matrix (Fin n) (Fin n) ℝ := DeltaURaw
  refine ⟨DeltaU, ?_, dhs_block_back_substitution_firstOrder
    fp.u ((n : ℝ) ^ 2)
    normA (maxEntryNorm hn Lhat) (maxEntryNorm hn Uhat)
    (maxEntryNorm hn (Lhat * DeltaU))
    Uhat DeltaU
    (fun i (_j : Fin 1) => fl_backSub fp n Uhat y i)
    (fun i (_j : Fin 1) => y i) ?_ ?_⟩
  · intro i j
    simpa [DeltaU] using hDeltaU i j
  · ext i j
    simpa [DeltaU, Matrix.mul_apply] using hEquation i
  · have hnormL : 0 ≤ maxEntryNorm hn Lhat := maxEntryNorm_nonneg hn Lhat
    have hnormU : 0 ≤ maxEntryNorm hn Uhat := maxEntryNorm_nonneg hn Uhat
    have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hγ
    have hDeltaNorm :
        maxEntryNorm hn DeltaU ≤ gamma fp n * maxEntryNorm hn Uhat := by
      apply maxEntryNorm_le_of_entry_le_bound
      intro i j
      calc
        |DeltaU i j| ≤ gamma fp n * |Uhat i j| := by
          simpa [DeltaU] using hDeltaU i j
        _ ≤ gamma fp n * maxEntryNorm hn Uhat :=
          mul_le_mul_of_nonneg_left (entry_le_maxEntryNorm hn Uhat i j) hgamma
    have hProduct :
        maxEntryNorm hn (Lhat * DeltaU) ≤
          gamma fp n * (n : ℝ) * maxEntryNorm hn Lhat *
            maxEntryNorm hn Uhat := by
      calc
        maxEntryNorm hn (Lhat * DeltaU) ≤
            (n : ℝ) * maxEntryNorm hn Lhat * maxEntryNorm hn DeltaU :=
          maxEntryNorm_matrix_mul_le_dim hn Lhat DeltaU
        _ ≤ (n : ℝ) * maxEntryNorm hn Lhat *
              (gamma fp n * maxEntryNorm hn Uhat) := by
          exact mul_le_mul_of_nonneg_left hDeltaNorm
            (mul_nonneg (Nat.cast_nonneg n) hnormL)
        _ = gamma fp n * (n : ℝ) * maxEntryNorm hn Lhat *
              maxEntryNorm hn Uhat := by ring
    have hFirst : FirstOrderLe fp.u
        (((n : ℝ) ^ 2) * fp.u * maxEntryNorm hn Lhat *
          maxEntryNorm hn Uhat)
        (maxEntryNorm hn (Lhat * DeltaU)) :=
      FirstOrderLe.of_gamma_dim_mul fp n hγ hnormL hnormU hProduct
    refine hFirst.mono_leading ?_
    have hscale :
        maxEntryNorm hn Lhat * maxEntryNorm hn Uhat ≤
          normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat := by
      linarith
    have hfactor : 0 ≤ ((n : ℝ) ^ 2) * fp.u :=
      mul_nonneg (sq_nonneg (n : ℝ)) fp.u_nonneg
    calc
      ((n : ℝ) ^ 2) * fp.u * maxEntryNorm hn Lhat * maxEntryNorm hn Uhat =
          (((n : ℝ) ^ 2) * fp.u) *
            (maxEntryNorm hn Lhat * maxEntryNorm hn Uhat) := by ring
      _ ≤ (((n : ℝ) ^ 2) * fp.u) *
            (normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat) :=
          mul_le_mul_of_nonneg_left hscale hfactor
      _ = ((n : ℝ) ^ 2) * fp.u *
            (normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat) := by ring

/-- The product of the conventional forward- and back-substitution
    coefficient perturbations is a genuine second-order DHS remainder. -/
theorem dhs_cross_product_firstOrder_of_componentwise_backward {n : ℕ}
    (fp : FPModel) (hn : 0 < n)
    (Lhat Uhat DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (hγ : gammaValid fp n)
    (hDeltaL : ∀ i j : Fin n,
      |DeltaL i j| ≤ gamma fp n * |Lhat i j|)
    (hDeltaU : ∀ i j : Fin n,
      |DeltaU i j| ≤ gamma fp n * |Uhat i j|) :
    FirstOrderLe fp.u 0 (maxEntryNorm hn (DeltaL * DeltaU)) := by
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hγ
  have hnormL : 0 ≤ maxEntryNorm hn Lhat := maxEntryNorm_nonneg hn Lhat
  have hnormU : 0 ≤ maxEntryNorm hn Uhat := maxEntryNorm_nonneg hn Uhat
  have hDeltaLNorm :
      maxEntryNorm hn DeltaL ≤ gamma fp n * maxEntryNorm hn Lhat := by
    apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    calc
      |DeltaL i j| ≤ gamma fp n * |Lhat i j| := hDeltaL i j
      _ ≤ gamma fp n * maxEntryNorm hn Lhat :=
        mul_le_mul_of_nonneg_left (entry_le_maxEntryNorm hn Lhat i j) hgamma
  have hDeltaUNorm :
      maxEntryNorm hn DeltaU ≤ gamma fp n * maxEntryNorm hn Uhat := by
    apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    calc
      |DeltaU i j| ≤ gamma fp n * |Uhat i j| := hDeltaU i j
      _ ≤ gamma fp n * maxEntryNorm hn Uhat :=
        mul_le_mul_of_nonneg_left (entry_le_maxEntryNorm hn Uhat i j) hgamma
  apply FirstOrderLe.of_gamma_sq_dim_mul fp n hγ hnormL hnormU
  calc
    maxEntryNorm hn (DeltaL * DeltaU) ≤
        (n : ℝ) * maxEntryNorm hn DeltaL * maxEntryNorm hn DeltaU :=
      maxEntryNorm_matrix_mul_le_dim hn DeltaL DeltaU
    _ ≤ (n : ℝ) * (gamma fp n * maxEntryNorm hn Lhat) *
          (gamma fp n * maxEntryNorm hn Uhat) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hDeltaLNorm (Nat.cast_nonneg n))
        hDeltaUNorm (maxEntryNorm_nonneg hn DeltaU)
        (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hgamma hnormL))
    _ = (n : ℝ) * gamma fp n ^ 2 * maxEntryNorm hn Lhat *
          maxEntryNorm hn Uhat := by ring

/-- The concrete conventional forward perturbation and the assembled block
    back-row certificate make their cross product purely second order.

    The forward componentwise `gamma` bound supplies a first-order max norm;
    the retained row entry bound supplies the corresponding first-order norm
    for the flattened `DeltaU`.  The matrix-product dimension factor is folded
    into the first coefficient before applying
    `FirstOrderLe.mul_is_secondOrder`. -/
theorem
    dhs_cross_product_firstOrder_of_forward_componentwise_and_back_rows
    {n : ℕ} {p : Type*}
    (fp : FPModel) (hn : 0 < n)
    (cRows normU rowPerturbBound : ℝ)
    (Lhat DeltaL Uhat DeltaU : Matrix (Fin n) (Fin n) ℝ)
    (Xhat Yhat : Matrix (Fin n) p ℝ)
    (hγ : gammaValid fp n)
    (hcRows : 0 ≤ cRows) (hNormU : 0 ≤ normU)
    (hDeltaL : ∀ i j : Fin n,
      |DeltaL i j| ≤ gamma fp n * |Lhat i j|)
    (hRows : DHSBlockBackSubstitutionRowsFirstOrderSpec
      fp.u cRows normU rowPerturbBound Uhat DeltaU Xhat Yhat) :
    FirstOrderLe fp.u 0 (maxEntryNorm hn (DeltaL * DeltaU)) := by
  have hGammaNonneg : 0 ≤ gamma fp n := gamma_nonneg fp hγ
  have hNormLNonneg : 0 ≤ maxEntryNorm hn Lhat :=
    maxEntryNorm_nonneg hn Lhat
  have hDeltaLNorm :
      maxEntryNorm hn DeltaL ≤ gamma fp n * maxEntryNorm hn Lhat := by
    apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    exact le_trans (hDeltaL i j)
      (mul_le_mul_of_nonneg_left
        (entry_le_maxEntryNorm hn Lhat i j) hGammaNonneg)
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hDeltaLFirst : FirstOrderLe fp.u
      (((n : ℝ) ^ 2) * fp.u * maxEntryNorm hn Lhat * 1)
      (maxEntryNorm hn DeltaL) :=
    FirstOrderLe.of_gamma_dim_mul fp n hγ hNormLNonneg (by norm_num) <| by
      calc
        maxEntryNorm hn DeltaL ≤ gamma fp n * maxEntryNorm hn Lhat :=
          hDeltaLNorm
        _ ≤ gamma fp n * (n : ℝ) * maxEntryNorm hn Lhat * 1 := by
          have := mul_le_mul_of_nonneg_left hnOne hGammaNonneg
          nlinarith [hNormLNonneg]
  have hDeltaUFirst : FirstOrderLe fp.u
      (cRows * fp.u * normU) (maxEntryNorm hn DeltaU) :=
    hRows.norm_bound.mono_value
      (maxEntryNorm_le_of_entry_le_bound hn DeltaU rowPerturbBound
        hRows.entry_bound)
  have hDeltaLScaled : FirstOrderLe fp.u
      ((((n : ℝ) ^ 2) * fp.u * maxEntryNorm hn Lhat * 1) * (n : ℝ))
      ((n : ℝ) * maxEntryNorm hn DeltaL) := by
    exact hDeltaLFirst.bound_mul_nonneg_right (Nat.cast_nonneg n) (by
      rw [mul_comm])
  have hDeltaLScaled' : FirstOrderLe fp.u
      (((n : ℝ) ^ 3 * maxEntryNorm hn Lhat) * fp.u)
      ((n : ℝ) * maxEntryNorm hn DeltaL) := by
    convert hDeltaLScaled using 1
    ring
  have hDeltaUFirst' : FirstOrderLe fp.u
      ((cRows * normU) * fp.u) (maxEntryNorm hn DeltaU) := by
    convert hDeltaUFirst using 1
    ring
  apply FirstOrderLe.mul_is_secondOrder fp.u_nonneg
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 3) hNormLNonneg)
    (mul_nonneg hcRows hNormU)
    (maxEntryNorm_nonneg hn DeltaU) hDeltaLScaled' hDeltaUFirst'
  exact maxEntryNorm_matrix_mul_le_dim hn DeltaL DeltaU

/-- Higham Theorem 13.6 / Eq.13.16 for Implementation 1, with the solve path
    executed by the repository's conventional algorithms.

    Starting from the checked partitioned-factorization spec and the local
    Eq.13.14 block-solve spec, this theorem constructs the conventional
    flattened forward solution, the descending conventional block-back
    solution, every Eq.13.15 perturbation, the assembled global `DeltaU`, and
    the forward `DeltaL`.  It proves the cross product is second order and
    uses the concrete four-term max-entry inequality for the total solve
    perturbation.  The conclusion contains the exact factorization and solve
    equations, the Eq.13.14/Eq.13.15 source facts, and all three displayed
    Eq.13.16 first-order bounds.  No abstract DHS source-path proposition or
    assumed forward/back branch spec remains. -/
theorem
    higham13_theorem13_6_implementation1_from_partitioned_factorization_and_conventional_recursive_solve
    {m r : ℕ} {s : Type*}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (δ θ dFact dn normA : ℝ)
    (A DeltaFact : Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : Fin (m * r) → ℝ)
    (c₄ normLhat21 normA11 normE21 : ℝ)
    (Lhat21 A21 E21 : Matrix s (Fin r) ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hA : 0 ≤ normA)
    (hδ : δ ≤ dFact) (hθ : θ ≤ dFact)
    (hdFact : dFact ≤ dn)
    (hdSolve : dFact + (((m * r : ℕ) : ℝ) ^ 2) +
      (((m * r : ℕ) : ℝ) *
        ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) +
          2 * (r : ℝ))) ≤ dn)
    (hFactSpec : PartitionedLUFirstOrderSpec
      fp.u δ θ normA
      (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat))
      (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U))
      (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact) A DeltaFact
      (blockMatrixFlatFin Lhat) (blockMatrixFlatFin U))
    (hStep2 : BlockSolveFirstOrderSpec
      fp.u c₄ normLhat21 normA11 normE21 Lhat21 A21 E21 A11)
    (hLdiag : ∀ i : Fin (m * r), blockMatrixFlatFin Lhat i i ≠ 0)
    (hLower : ∀ i j : Fin (m * r), i.val < j.val →
      blockMatrixFlatFin Lhat i j = 0)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0) :
    ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaL : Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
      (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * maxEntryNorm hr (U i i)) ∧
      (∀ i j : Fin (m * r),
        |DeltaL i j| ≤ gamma fp (m * r) *
          |blockMatrixFlatFin Lhat i j|) ∧
      (blockMatrixFlatFin Lhat * blockMatrixFlatFin U = A + DeltaFact) ∧
      ((A + (DeltaFact + DeltaL * blockMatrixFlatFin U +
          blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
          DeltaL * blockMatrixFlatFin DeltaU)) *
          blockMatrixRowsFlatFin
            (dhsBlockBackConventionalSolution fp U
              (dhsBlockForwardConventionalSolution fp Lhat b)) =
        (fun i (_k : Fin 1) => b i)) ∧
      ((Lhat21 * A11 = A21 + E21 ∧
          BlockSolveFirstOrderBound fp.u c₄ normLhat21 normA11 normE21) ∧
        (∀ i : Fin m,
          (U i i + DeltaDiag i) *
              dhsBlockBackConventionalSolution fp U
                (dhsBlockForwardConventionalSolution fp Lhat b) i =
            dhsBlockBackConventionalRHS fp i U
              (dhsBlockBackConventionalSolution fp U
                (dhsBlockForwardConventionalSolution fp Lhat b))
              (dhsBlockForwardConventionalSolution fp Lhat b) ∧
          DiagonalBlockSolveFirstOrderBound fp.u (2 * (r : ℝ))
            (maxEntryNorm hr (U i i))
            (maxEntryNorm hr (DeltaDiag i)))) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (normA +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (normA +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (maxEntryNorm (Nat.mul_pos hm hr)
          (DeltaFact + DeltaL * blockMatrixFlatFin U +
            blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
            DeltaL * blockMatrixFlatFin DeltaU)) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (normA +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (max (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact)
          (maxEntryNorm (Nat.mul_pos hm hr)
            (DeltaFact + DeltaL * blockMatrixFlatFin U +
              blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
              DeltaL * blockMatrixFlatFin DeltaU))) := by
  let hn : 0 < m * r := Nat.mul_pos hm hr
  let Lflat := blockMatrixFlatFin Lhat
  let Uflat := blockMatrixFlatFin U
  let normL := maxEntryNorm hn Lflat
  let normU := maxEntryNorm hn Uflat
  let Y := dhsBlockForwardConventionalSolution fp Lhat b
  let X := dhsBlockBackConventionalSolution fp U Y
  let cRows : ℝ := (((m * r : ℕ) : ℝ) ^ 2 +
    4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) + 2 * (r : ℝ)
  let cBack : ℝ := ((m * r : ℕ) : ℝ) * cRows
  let cForward : ℝ := ((m * r : ℕ) : ℝ) ^ 2
  let dSolve : ℝ := dFact + cForward + cBack
  have hγ : gammaValid fp (m * r) := by
    unfold gammaValid
    linarith
  have hNormL : 0 ≤ normL := maxEntryNorm_nonneg hn Lflat
  have hNormU : 0 ≤ normU := maxEntryNorm_nonneg hn Uflat
  rcases
      dhs_block_forward_substitution_firstOrder_from_conventional_forwardSub_single_rhs
        fp hn normA Lflat Uflat b hA hLdiag hLower hγ with
    ⟨DeltaL, hDeltaL, hForwardRaw⟩
  have hYFlat : blockMatrixRowsFlatFin Y =
      (fun i (_k : Fin 1) => fl_forwardSub fp (m * r) Lflat b i) := by
    simpa only [Y, Lflat] using
      dhsBlockForwardConventionalSolution_flat fp Lhat b
  have hForward : DHSBlockForwardSubstitutionFirstOrderSpec
      fp.u cForward normA normL normU
      (maxEntryNorm hn (DeltaL * Uflat)) Lflat DeltaL
      (blockMatrixRowsFlatFin Y) (fun i (_k : Fin 1) => b i) := by
    rw [hYFlat]
    simpa only [cForward, normL, normU, Lflat, Uflat] using hForwardRaw
  have hNormUii : ∀ i : Fin m, maxEntryNorm hr (U i i) ≤ normU := by
    intro i
    simpa only [normU, Uflat, hn] using
      maxEntryNorm_diagonalBlock_le_blockMatrixFlatFin hm hr U i
  have hUTail : ∀ i : Fin m,
      maxEntryNormRect hr hn (dhsBlockBackUpperTailRowFlat i (U i)) ≤
        normU := by
    intro i
    simpa only [normU, Uflat, hn] using
      maxEntryNorm_upperTailRowFlat_le_blockMatrixFlatFin hm hr U i
  rcases
      dhs_block_back_substitution_rows_and_firstOrder_from_conventional_recursive_block_solution
        fp hm hr cBack normA normL normU
        (fun i => maxEntryNorm hr (U i i)) Lhat U Y hSmallProduct
        hA hNormL hNormU hUUpper hNormUii
        (by
          change maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) ≤
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat)
          exact le_rfl)
        (by
          dsimp only [cBack, cRows]
          exact le_rfl)
        hUTail (fun _i => le_rfl) hDiag hUpper with
    ⟨DeltaDiag, DeltaU, rowPerturbBound,
      hDeltaDiag, hDiagonal, hRows, hBack⟩
  have hcRows : 0 ≤ cRows := by
    dsimp only [cRows]
    positivity
  have hCross : FirstOrderLe fp.u 0
      (maxEntryNorm hn (DeltaL * blockMatrixFlatFin DeltaU)) := by
    exact
      dhs_cross_product_firstOrder_of_forward_componentwise_and_back_rows
        fp hn cRows normU rowPerturbBound Lflat DeltaL Uflat
        (blockMatrixFlatFin DeltaU) (blockMatrixRowsFlatFin X)
        (blockMatrixRowsFlatFin Y) hγ hcRows hNormU hDeltaL hRows
  let normSolve := maxEntryNorm hn
    (DeltaFact + DeltaL * Uflat + Lflat * blockMatrixFlatFin DeltaU +
      DeltaL * blockMatrixFlatFin DeltaU)
  have hTotal : normSolve ≤
      maxEntryNorm hn DeltaFact + maxEntryNorm hn (DeltaL * Uflat) +
        maxEntryNorm hn (Lflat * blockMatrixFlatFin DeltaU) +
        maxEntryNorm hn (DeltaL * blockMatrixFlatFin DeltaU) := by
    simpa only [normSolve] using
      maxEntryNorm_four_add_le hn DeltaFact (DeltaL * Uflat)
        (Lflat * blockMatrixFlatFin DeltaU)
        (DeltaL * blockMatrixFlatFin DeltaU)
  have hFactLeading : FirstOrderLe fp.u
      (dFact * fp.u * (normA + normL * normU))
      (maxEntryNorm hn DeltaFact) :=
    hFactSpec.norm_bound.mono_leading
      (demmelHighamSchreiber13_6_partitioned_leading_term_le_of_coeff_bounds
        fp.u δ θ dFact normA normL normU fp.u_nonneg hA hNormL hNormU
        hδ hθ)
  have hSolveLeading : FirstOrderLe fp.u
      (dSolve * fp.u * (normA + normL * normU)) normSolve := by
    apply dhs_lu_solve_perturbation_firstOrder
      normSolve (maxEntryNorm hn DeltaFact) (maxEntryNorm hn (DeltaL * Uflat))
      (maxEntryNorm hn (Lflat * blockMatrixFlatFin DeltaU))
      (maxEntryNorm hn (DeltaL * blockMatrixFlatFin DeltaU))
      normA normL normU fp.u dFact cForward cBack dSolve
      fp.u_nonneg hA hNormL hNormU
    · exact le_rfl
    · exact hFactLeading
    · exact hForward.norm_bound
    · exact hBack.norm_bound
    · exact hCross
    · exact hTotal
  have hSolveEquation :
      (A + (DeltaFact + DeltaL * Uflat +
          Lflat * blockMatrixFlatFin DeltaU +
          DeltaL * blockMatrixFlatFin DeltaU)) *
          blockMatrixRowsFlatFin X =
        (fun i (_k : Fin 1) => b i) :=
    dhs_lu_solve_perturbation_identity A DeltaFact Lflat Uflat
      DeltaL (blockMatrixFlatFin DeltaU) (blockMatrixRowsFlatFin X)
      (fun i (_k : Fin 1) => b i) (blockMatrixRowsFlatFin Y)
      hFactSpec.equation hForward.equation hBack.equation
  have hFinal :=
    higham13_theorem13_6_eq13_16_firstOrder_from_factor_solve_estimates
      (maxEntryNorm hn DeltaFact) normSolve normA normL normU
      fp.u dFact dSolve dn
      fp.u_nonneg hA hNormL hNormU hdFact (by
        simpa only [dSolve, cForward, cBack, cRows] using hdSolve)
      hFactLeading hSolveLeading
  refine ⟨DeltaDiag, DeltaL, DeltaU, ?_, hDeltaL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only using hDeltaDiag
  · simpa only [Lflat, Uflat] using hFactSpec.equation
  · simpa only [X, Y, Lflat, Uflat] using hSolveEquation
  · refine ⟨higham13_eq13_14_from_block_solve_spec
      fp.u c₄ normLhat21 normA11 normE21 Lhat21 A21 E21 A11 hStep2, ?_⟩
    intro i
    exact higham13_eq13_15_from_diagonal_block_solve_spec
      fp.u (2 * (r : ℝ)) (maxEntryNorm hr (U i i))
      (maxEntryNorm hr (DeltaDiag i)) (U i i) (DeltaDiag i) (X i)
      (dhsBlockBackConventionalRHS fp i U X Y) (hDiagonal i)
  · simpa only [normL, normU, Lflat, Uflat, hn] using hFinal.1
  · simpa only [normSolve, normL, normU, Lflat, Uflat, hn] using hFinal.2.1
  · simpa only [normSolve, normL, normU, Lflat, Uflat, hn] using hFinal.2.2

/-- Concrete conventional single-right-hand-side specialization of the two
    named DHS triangular-solve branches.

    The witnesses are the actual coefficient perturbations produced by the
    repository's forward- and back-substitution algorithms.  Besides the two
    exact perturbed equations and `n^2` first-order transported budgets, the
    conclusion supplies the second-order cross-product fact consumed by
    `demmelHighamSchreiber13_6_solve_result_from_forward_back_substitution_specs`.
    This is a flattened scalar specialization; the fixed block-row/local-solve
    Implementation 1 execution required for full Theorem 13.6 remains a
    separate source obligation. -/
theorem
    dhs_block_forward_back_substitution_firstOrder_from_conventional_single_rhs
    {n : ℕ}
    (fp : FPModel) (hn : 0 < n) (normA : ℝ)
    (Lhat Uhat : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hA : 0 ≤ normA)
    (hLdiag : ∀ i : Fin n, Lhat i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → Lhat i j = 0)
    (hUdiag : ∀ i : Fin n, Uhat i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → Uhat i j = 0)
    (hγ : gammaValid fp n) :
    ∃ (DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ),
      ((∀ i j : Fin n, |DeltaL i j| ≤ gamma fp n * |Lhat i j|) ∧
        DHSBlockForwardSubstitutionFirstOrderSpec
          fp.u ((n : ℝ) ^ 2)
          normA (maxEntryNorm hn Lhat) (maxEntryNorm hn Uhat)
          (maxEntryNorm hn (DeltaL * Uhat))
          Lhat DeltaL
          (fun i (_j : Fin 1) => fl_forwardSub fp n Lhat b i)
          (fun i (_j : Fin 1) => b i)) ∧
      ((∀ i j : Fin n, |DeltaU i j| ≤ gamma fp n * |Uhat i j|) ∧
        DHSBlockBackSubstitutionFirstOrderSpec
          fp.u ((n : ℝ) ^ 2)
          normA (maxEntryNorm hn Lhat) (maxEntryNorm hn Uhat)
          (maxEntryNorm hn (Lhat * DeltaU))
          Uhat DeltaU
          (fun i (_j : Fin 1) =>
            fl_backSub fp n Uhat (fl_forwardSub fp n Lhat b) i)
          (fun i (_j : Fin 1) => fl_forwardSub fp n Lhat b i)) ∧
      FirstOrderLe fp.u 0 (maxEntryNorm hn (DeltaL * DeltaU)) := by
  rcases
      dhs_block_forward_substitution_firstOrder_from_conventional_forwardSub_single_rhs
        fp hn normA Lhat Uhat b hA hLdiag hlower hγ with
    ⟨DeltaL, hDeltaL, hForward⟩
  rcases
      dhs_block_back_substitution_firstOrder_from_conventional_backSub_single_rhs
        fp hn normA Lhat Uhat (fl_forwardSub fp n Lhat b)
        hA hUdiag hupper hγ with
    ⟨DeltaU, hDeltaU, hBack⟩
  exact
    ⟨DeltaL, DeltaU, ⟨hDeltaL, hForward⟩, ⟨hDeltaU, hBack⟩,
      dhs_cross_product_firstOrder_of_componentwise_backward
        fp hn Lhat Uhat DeltaL DeltaU hγ hDeltaL hDeltaU⟩

/-- Concrete conventional single-right-hand-side DHS solve perturbation.

    Starting from an exact factorization residual `Lhat * Uhat = A + E`, this
    theorem runs the repository's scalar forward and back substitutions,
    constructs their coefficient perturbations, proves the exact perturbed
    solve, and bounds the actual max-entry norm of
    `E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU` to first order.

    This closes the mathematical solve-composition layer for the flattened
    one-right-hand-side specialization.  It deliberately leaves the source's
    fixed block-row/local-solve execution and its audited DHS source-path facts
    outside the conclusion. -/
theorem dhs_lu_solve_perturbation_firstOrder_from_conventional_single_rhs
    {n : ℕ}
    (fp : FPModel) (hn : 0 < n) (normA cFact dSolve : ℝ)
    (A E Lhat Uhat : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hA : 0 ≤ normA)
    (hLdiag : ∀ i : Fin n, Lhat i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → Lhat i j = 0)
    (hUdiag : ∀ i : Fin n, Uhat i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → Uhat i j = 0)
    (hγ : gammaValid fp n)
    (hc : cFact + (n : ℝ) ^ 2 + (n : ℝ) ^ 2 ≤ dSolve)
    (hFact : Lhat * Uhat = A + E)
    (hE : FirstOrderLe fp.u
      (cFact * fp.u *
        (normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat))
      (maxEntryNorm hn E)) :
    ∃ (DeltaL DeltaU : Matrix (Fin n) (Fin n) ℝ),
      (rectMatMul
          (A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU))
          ((fun i (_j : Fin 1) =>
            fl_backSub fp n Uhat (fl_forwardSub fp n Lhat b) i) :
              Matrix (Fin n) (Fin 1) ℝ)) =
        ((fun i (_j : Fin 1) => b i) : Matrix (Fin n) (Fin 1) ℝ) ∧
      FirstOrderLe fp.u
        (dSolve * fp.u *
          (normA + maxEntryNorm hn Lhat * maxEntryNorm hn Uhat))
        (maxEntryNorm hn
          (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU)) := by
  rcases
      dhs_block_forward_back_substitution_firstOrder_from_conventional_single_rhs
        fp hn normA Lhat Uhat b hA hLdiag hlower hUdiag hupper hγ with
    ⟨DeltaL, DeltaU, ⟨_hDeltaL, hForward⟩, ⟨_hDeltaU, hBack⟩, hCross⟩
  refine ⟨DeltaL, DeltaU, ?_, ?_⟩
  · simpa [rectMatMul, Matrix.mul_apply] using
      (dhs_lu_solve_perturbation_identity
        A E Lhat Uhat DeltaL DeltaU
        (fun i (_j : Fin 1) =>
          fl_backSub fp n Uhat (fl_forwardSub fp n Lhat b) i)
        (fun i (_j : Fin 1) => b i)
        (fun i (_j : Fin 1) => fl_forwardSub fp n Lhat b i)
        hFact hForward.equation hBack.equation)
  · have hTotal :
        maxEntryNorm hn
            (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU) ≤
          maxEntryNorm hn E + maxEntryNorm hn (DeltaL * Uhat) +
            maxEntryNorm hn (Lhat * DeltaU) +
              maxEntryNorm hn (DeltaL * DeltaU) :=
      maxEntryNorm_four_add_le hn E (DeltaL * Uhat)
        (Lhat * DeltaU) (DeltaL * DeltaU)
    exact dhs_lu_solve_perturbation_firstOrder
      (maxEntryNorm hn
        (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU))
      (maxEntryNorm hn E)
      (maxEntryNorm hn (DeltaL * Uhat))
      (maxEntryNorm hn (Lhat * DeltaU))
      (maxEntryNorm hn (DeltaL * DeltaU))
      normA (maxEntryNorm hn Lhat) (maxEntryNorm hn Uhat)
      fp.u cFact ((n : ℝ) ^ 2) ((n : ℝ) ^ 2) dSolve
      fp.u_nonneg hA (maxEntryNorm_nonneg hn Lhat)
      (maxEntryNorm_nonneg hn Uhat) hc hE hForward.norm_bound
      hBack.norm_bound hCross hTotal

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 back-substitution branch:
    scalar comparison from local Eq.13.15 coefficients.

    This discharges the raw leading-term comparison for a diagonal-block solve
    when the source analysis has bounded the local coefficient `c₅` by the
    global back-substitution coefficient and has compared the local diagonal
    block scale to `‖A‖ + ‖Lhat‖‖Uhat‖`. -/
theorem dhs_block_back_substitution_leading_term_le_of_coeff_bounds
    (u c₅ cBack normA normL normU normUii : ℝ)
    (hu : 0 ≤ u) (hc₅_nonneg : 0 ≤ c₅)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc₅_le : c₅ ≤ cBack)
    (hLocalScale : normUii ≤ normA + normL * normU) :
    c₅ * u * normUii ≤ cBack * u * (normA + normL * normU) := by
  have hsum : 0 ≤ normA + normL * normU := by
    linarith [mul_nonneg hL hU]
  have hc₅u : 0 ≤ c₅ * u := mul_nonneg hc₅_nonneg hu
  have hscale : 0 ≤ u * (normA + normL * normU) :=
    mul_nonneg hu hsum
  calc
    c₅ * u * normUii
        = (c₅ * u) * normUii := by ring
    _ ≤ (c₅ * u) * (normA + normL * normU) :=
        mul_le_mul_of_nonneg_left hLocalScale hc₅u
    _ = c₅ * (u * (normA + normL * normU)) := by ring
    _ ≤ cBack * (u * (normA + normL * normU)) :=
        mul_le_mul_of_nonneg_right hc₅_le hscale
    _ = cBack * u * (normA + normL * normU) := by ring

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 back-substitution branch
    from a local diagonal-block solve specification.

    Higham's local equation (13.15) supplies the exact perturbed diagonal solve
    and a first-order bound for its local perturbation.  To use that solve as
    the DHS block-back-substitution branch, callers must still provide the
    product-law/value comparison that transports the local perturbation to the
    left-multiplied budget `normLDeltaU`, plus the scalar comparison from the
    local leading term to the global DHS branch leading term.  This keeps the
    max-entry/product obligation visible instead of hiding it in the branch
    constructor. -/
theorem dhs_block_back_substitution_firstOrder_from_diagonal_block_solve_spec
    {n p : Type*} [Fintype n]
    (u c₅ cBack normA normL normU normUii normDeltaUii normLDeltaU : ℝ)
    (Uii DeltaUii : Matrix n n ℝ) (Xhat D : Matrix n p ℝ)
    (hProductLaw : normLDeltaU ≤ normDeltaUii)
    (hLeading :
      c₅ * u * normUii ≤ cBack * u * (normA + normL * normU))
    (hSpec :
      DiagonalBlockSolveFirstOrderSpec
        u c₅ normUii normDeltaUii Uii DeltaUii Xhat D) :
    DHSBlockBackSubstitutionFirstOrderSpec
      u cBack normA normL normU normLDeltaU Uii DeltaUii Xhat D :=
  ⟨hSpec.equation,
    (hSpec.norm_bound.mono_value hProductLaw).mono_leading hLeading⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 back-substitution branch
    from a local diagonal-block solve specification, with the scalar comparison
    derived from source-shaped coefficient and norm comparisons. -/
theorem dhs_block_back_substitution_firstOrder_from_diagonal_block_solve_spec_of_coeff_bounds
    {n p : Type*} [Fintype n]
    (u c₅ cBack normA normL normU normUii normDeltaUii normLDeltaU : ℝ)
    (Uii DeltaUii : Matrix n n ℝ) (Xhat D : Matrix n p ℝ)
    (hProductLaw : normLDeltaU ≤ normDeltaUii)
    (hu : 0 ≤ u) (hc₅_nonneg : 0 ≤ c₅)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc₅_le : c₅ ≤ cBack)
    (hLocalScale : normUii ≤ normA + normL * normU)
    (hSpec :
      DiagonalBlockSolveFirstOrderSpec
        u c₅ normUii normDeltaUii Uii DeltaUii Xhat D) :
    DHSBlockBackSubstitutionFirstOrderSpec
      u cBack normA normL normU normLDeltaU Uii DeltaUii Xhat D :=
  dhs_block_back_substitution_firstOrder_from_diagonal_block_solve_spec
    u c₅ cBack normA normL normU normUii normDeltaUii normLDeltaU
    Uii DeltaUii Xhat D hProductLaw
    (dhs_block_back_substitution_leading_term_le_of_coeff_bounds
      u c₅ cBack normA normL normU normUii
      hu hc₅_nonneg hA hL hU hc₅_le hLocalScale)
    hSpec

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 solve route:
    package the exact solve perturbation and first-order budget into the audited
    DHS solve-result boundary.

    This is the next source-facing layer after
    `dhs_lu_solve_perturbation_identity`: once the factorization residual,
    forward solve, and back substitution have supplied their exact equations and
    component first-order budgets, this theorem produces the separated
    `DemmelHighamSchreiber13_6SolveResult`.  The implementation-facing kernel
    facts remain explicit hypotheses; they are not hidden in the solve estimate. -/
theorem demmelHighamSchreiber13_6_solve_result_from_perturbation_layers
    {n p : Type*} [Fintype n]
    (A E Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (Xhat B Yhat : Matrix n p ℝ)
    (normDeltaA_solve normE normDeltaLU normLDeltaU normDeltaLDeltaU
      normA normL normU u cFact cForward cBack d_solve : ℝ)
    (blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws : Prop)
    (hBlockRowRHS : blockRowRHS)
    (hForwardPath : forwardSubstitution)
    (hBackPath : blockBackSubstitution)
    (hSolveSuccess : localSolveSuccess)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc : cFact + cForward + cBack ≤ d_solve)
    (hFact : Lhat * Uhat = A + E)
    (hForward : (Lhat + DeltaL) * Yhat = B)
    (hBack : (Uhat + DeltaU) * Xhat = Yhat)
    (hE : FirstOrderLe u (cFact * u * (normA + normL * normU)) normE)
    (hDeltaLU : FirstOrderLe u
      (cForward * u * (normA + normL * normU)) normDeltaLU)
    (hLDeltaU : FirstOrderLe u
      (cBack * u * (normA + normL * normU)) normLDeltaU)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤ normE + normDeltaLU + normLDeltaU + normDeltaLDeltaU) :
    ((A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU)) * Xhat = B) ∧
      DemmelHighamSchreiber13_6SolveResult
        u d_solve normA normL normU normDeltaA_solve
        blockRowRHS forwardSubstitution blockBackSubstitution
        localSolveSuccess maxEntryProductLaws := by
  exact
    ⟨dhs_lu_solve_perturbation_identity
        A E Lhat Uhat DeltaL DeltaU Xhat B Yhat hFact hForward hBack,
      ⟨hBlockRowRHS, hForwardPath, hBackPath, hSolveSuccess,
        hMaxEntryProductLaws,
        dhs_lu_solve_perturbation_firstOrder
          normDeltaA_solve normE normDeltaLU normLDeltaU normDeltaLDeltaU
          normA normL normU u cFact cForward cBack d_solve
          hu hA hL hU hc hE hDeltaLU hLDeltaU hDeltaLDeltaU hTotal⟩⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 solve route, with the
    forward and block-back substitution branches passed as named specs.

    This is the selected-scope companion to
    `demmelHighamSchreiber13_6_solve_result_from_perturbation_layers`.  The
    recovered strict Pro audit singled out the back-substitution branch as a
    genuine independent proof component.  This theorem exposes that component
    as `DHSBlockBackSubstitutionFirstOrderSpec` instead of a raw equation and
    bound pair, while still leaving the eventual operational row-by-row proof
    as a visible upstream obligation. -/
theorem demmelHighamSchreiber13_6_solve_result_from_forward_back_substitution_specs
    {n p : Type*} [Fintype n]
    (A E Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (Xhat B Yhat : Matrix n p ℝ)
    (normDeltaA_solve normE normDeltaLU normLDeltaU normDeltaLDeltaU
      normA normL normU u cFact cForward cBack d_solve : ℝ)
    (blockRowRHS localSolveSuccess maxEntryProductLaws : Prop)
    (hBlockRowRHS : blockRowRHS)
    (hSolveSuccess : localSolveSuccess)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc : cFact + cForward + cBack ≤ d_solve)
    (hFact : Lhat * Uhat = A + E)
    (hForward :
      DHSBlockForwardSubstitutionFirstOrderSpec
        u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
    (hBack :
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
    (hE : FirstOrderLe u (cFact * u * (normA + normL * normU)) normE)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤ normE + normDeltaLU + normLDeltaU + normDeltaLDeltaU) :
    ((A + (E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU)) * Xhat = B) ∧
      DemmelHighamSchreiber13_6SolveResult
        u d_solve normA normL normU normDeltaA_solve
        blockRowRHS
        (DHSBlockForwardSubstitutionFirstOrderSpec
          u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
        (DHSBlockBackSubstitutionFirstOrderSpec
          u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
        localSolveSuccess maxEntryProductLaws := by
  exact
    demmelHighamSchreiber13_6_solve_result_from_perturbation_layers
      A E Lhat Uhat DeltaL DeltaU Xhat B Yhat
      normDeltaA_solve normE normDeltaLU normLDeltaU normDeltaLDeltaU
      normA normL normU u cFact cForward cBack d_solve
      blockRowRHS
      (DHSBlockForwardSubstitutionFirstOrderSpec
        u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
      (DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
      localSolveSuccess maxEntryProductLaws hBlockRowRHS hForward hBack
      hSolveSuccess hMaxEntryProductLaws hu hA hL hU hc hFact
      hForward.equation hBack.equation hE hForward.norm_bound
      hBack.norm_bound hDeltaLDeltaU hTotal

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 packaging route from the
    checked partitioned factorization layer and the named forward/back
    substitution branch specs.

    This is the stricter branch-surface companion to
    `demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_and_solve_perturbation_layers`.
    It carries the recovered Pro split of the solve proof all the way into the
    audited DHS Theorem 2.1 result object: the solve source-path fields are the
    `DHSBlockForwardSubstitutionFirstOrderSpec` and
    `DHSBlockBackSubstitutionFirstOrderSpec` propositions, not unnamed raw
    equations and bounds.  The row-by-row execution proof for those specs,
    rounded Schur update, product laws, and scalar comparisons remain visible
    upstream obligations. -/
theorem demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_forward_back_substitution_specs
    {n p : Type*} [Fintype n]
    (A DeltaA_fact Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (Xhat B Yhat : Matrix n p ℝ)
    (u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack : ℝ)
    (recursiveExecution schurUpdate blockRowRHS localSolveSuccess
      maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hBlockRowRHS : blockRowRHS)
    (hSolveSuccess : localSolveSuccess)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc : d_fact + cForward + cBack ≤ d_solve)
    (hFactSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA_fact Lhat Uhat)
    (hLeading :
      u * (δ * normA + θ * normL * normU) ≤
        d_fact * u * (normA + normL * normU))
    (hForward :
      DHSBlockForwardSubstitutionFirstOrderSpec
        u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
    (hBack :
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤
        normDeltaA_fact + normDeltaLU + normLDeltaU + normDeltaLDeltaU) :
    (Lhat * Uhat = A + DeltaA_fact) ∧
      ((A + (DeltaA_fact + DeltaL * Uhat + Lhat * DeltaU +
        DeltaL * DeltaU)) * Xhat = B) ∧
      DemmelHighamSchreiber13_6Theorem2_1Result
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve
        recursiveExecution schurUpdate blockRowRHS
        (DHSBlockForwardSubstitutionFirstOrderSpec
          u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
        (DHSBlockBackSubstitutionFirstOrderSpec
          u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
        localSolveSuccess maxEntryProductLaws := by
  rcases
    demmelHighamSchreiber13_6_factorization_result_from_partitioned_layer
      A DeltaA_fact Lhat Uhat u δ θ d_fact normA normL normU
      normDeltaA_fact recursiveExecution schurUpdate maxEntryProductLaws
      hRecursiveExecution hSchurUpdate hMaxEntryProductLaws hFactSpec
      hLeading with
    ⟨hFactorEq, hFactResult⟩
  rcases
    demmelHighamSchreiber13_6_solve_result_from_forward_back_substitution_specs
      A DeltaA_fact Lhat Uhat DeltaL DeltaU Xhat B Yhat
      normDeltaA_solve normDeltaA_fact normDeltaLU normLDeltaU
      normDeltaLDeltaU normA normL normU u d_fact cForward cBack d_solve
      blockRowRHS localSolveSuccess maxEntryProductLaws hBlockRowRHS
      hSolveSuccess hMaxEntryProductLaws hu hA hL hU hc hFactorEq
      hForward hBack hFactResult.factorization hDeltaLDeltaU hTotal with
    ⟨hSolveEq, hSolveResult⟩
  exact
    ⟨hFactorEq, hSolveEq,
      demmelHighamSchreiber13_6_theorem2_1_result_from_factorization_solve_results
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve recursiveExecution schurUpdate
        blockRowRHS
        (DHSBlockForwardSubstitutionFirstOrderSpec
          u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
        (DHSBlockBackSubstitutionFirstOrderSpec
          u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
        localSolveSuccess maxEntryProductLaws hFactResult hSolveResult⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 packaging route from the
    checked partitioned factorization layer and named forward/back branch
    specs, with the factorization scalar comparison derived from coefficient
    bounds.

    Compared with
    `demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_forward_back_substitution_specs`,
    this version replaces the raw leading-term comparison by the source-shaped
    coefficient premises `δ ≤ d_fact` and `θ ≤ d_fact`.  The remaining solve
    aggregation, branch execution, block-row RHS, solve-success, product-law,
    and recursive-execution obligations stay explicit. -/
theorem demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_forward_back_substitution_specs_of_coeff_bounds
    {n p : Type*} [Fintype n]
    (A DeltaA_fact Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (Xhat B Yhat : Matrix n p ℝ)
    (u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack : ℝ)
    (recursiveExecution schurUpdate blockRowRHS localSolveSuccess
      maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hBlockRowRHS : blockRowRHS)
    (hSolveSuccess : localSolveSuccess)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hδ : δ ≤ d_fact) (hθ : θ ≤ d_fact)
    (hc : d_fact + cForward + cBack ≤ d_solve)
    (hFactSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA_fact Lhat Uhat)
    (hForward :
      DHSBlockForwardSubstitutionFirstOrderSpec
        u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
    (hBack :
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤
        normDeltaA_fact + normDeltaLU + normLDeltaU + normDeltaLDeltaU) :
    (Lhat * Uhat = A + DeltaA_fact) ∧
      ((A + (DeltaA_fact + DeltaL * Uhat + Lhat * DeltaU +
        DeltaL * DeltaU)) * Xhat = B) ∧
      DemmelHighamSchreiber13_6Theorem2_1Result
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve
        recursiveExecution schurUpdate blockRowRHS
        (DHSBlockForwardSubstitutionFirstOrderSpec
          u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
        (DHSBlockBackSubstitutionFirstOrderSpec
          u cBack normA normL normU normLDeltaU Uhat DeltaU Xhat Yhat)
        localSolveSuccess maxEntryProductLaws := by
  exact
    demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_forward_back_substitution_specs
      A DeltaA_fact Lhat Uhat DeltaL DeltaU Xhat B Yhat
      u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack recursiveExecution schurUpdate blockRowRHS
      localSolveSuccess maxEntryProductLaws hRecursiveExecution hSchurUpdate
      hBlockRowRHS hSolveSuccess hMaxEntryProductLaws hu hA hL hU hc
      hFactSpec
      (demmelHighamSchreiber13_6_partitioned_leading_term_le_of_coeff_bounds
        u δ θ d_fact normA normL normU hu hA hL hU hδ hθ)
      hForward hBack hDeltaLDeltaU hTotal

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 packaging route from the
    two checked layers recovered in the Pro audit.

    The partitioned first-order factorization layer supplies both the
    factorization equation and the factorization perturbation budget used as
    the solve route's `E` term.  The solve perturbation layer then supplies the
    solve equation and solve estimate.  The result is the audited DHS
    Theorem 2.1 boundary object, while recursive execution, Schur update,
    block-row RHS, local solve path, product laws, and scalar comparisons stay
    explicit on the theorem surface. -/
theorem demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_and_solve_perturbation_layers
    {n p : Type*} [Fintype n]
    (A DeltaA_fact Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (Xhat B Yhat : Matrix n p ℝ)
    (u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack : ℝ)
    (recursiveExecution schurUpdate blockRowRHS forwardSubstitution
      blockBackSubstitution localSolveSuccess maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hBlockRowRHS : blockRowRHS)
    (hForwardPath : forwardSubstitution)
    (hBackPath : blockBackSubstitution)
    (hSolveSuccess : localSolveSuccess)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc : d_fact + cForward + cBack ≤ d_solve)
    (hFactSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA_fact Lhat Uhat)
    (hLeading :
      u * (δ * normA + θ * normL * normU) ≤
        d_fact * u * (normA + normL * normU))
    (hForward : (Lhat + DeltaL) * Yhat = B)
    (hBack : (Uhat + DeltaU) * Xhat = Yhat)
    (hDeltaLU : FirstOrderLe u
      (cForward * u * (normA + normL * normU)) normDeltaLU)
    (hLDeltaU : FirstOrderLe u
      (cBack * u * (normA + normL * normU)) normLDeltaU)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤
        normDeltaA_fact + normDeltaLU + normLDeltaU + normDeltaLDeltaU) :
    (Lhat * Uhat = A + DeltaA_fact) ∧
      ((A + (DeltaA_fact + DeltaL * Uhat + Lhat * DeltaU +
        DeltaL * DeltaU)) * Xhat = B) ∧
      DemmelHighamSchreiber13_6Theorem2_1Result
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve
        recursiveExecution schurUpdate blockRowRHS forwardSubstitution
        blockBackSubstitution localSolveSuccess maxEntryProductLaws := by
  rcases
    demmelHighamSchreiber13_6_factorization_result_from_partitioned_layer
      A DeltaA_fact Lhat Uhat u δ θ d_fact normA normL normU
      normDeltaA_fact recursiveExecution schurUpdate maxEntryProductLaws
      hRecursiveExecution hSchurUpdate hMaxEntryProductLaws hFactSpec
      hLeading with
    ⟨hFactorEq, hFactResult⟩
  rcases
    demmelHighamSchreiber13_6_solve_result_from_perturbation_layers
      A DeltaA_fact Lhat Uhat DeltaL DeltaU Xhat B Yhat
      normDeltaA_solve normDeltaA_fact normDeltaLU normLDeltaU
      normDeltaLDeltaU normA normL normU u d_fact cForward cBack d_solve
      blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
      maxEntryProductLaws hBlockRowRHS hForwardPath hBackPath hSolveSuccess
      hMaxEntryProductLaws hu hA hL hU hc hFactorEq hForward hBack
      hFactResult.factorization hDeltaLU hLDeltaU hDeltaLDeltaU hTotal with
    ⟨hSolveEq, hSolveResult⟩
  exact
    ⟨hFactorEq, hSolveEq,
      demmelHighamSchreiber13_6_theorem2_1_result_from_factorization_solve_results
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve recursiveExecution schurUpdate
        blockRowRHS forwardSubstitution blockBackSubstitution localSolveSuccess
        maxEntryProductLaws hFactResult hSolveResult⟩

/-- Demmel--Higham--Schreiber [326], Theorem 2.1 packaging route from the
    checked partitioned factorization and solve perturbation layers, with the
    Higham Algorithm 13.3 Implementation 1 local source path instantiated.

    This is the concrete-source-path companion to
    `demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_and_solve_perturbation_layers`.
    The block-row/forward and block-back/local-solve slots of the audited DHS
    source path are exactly the Eq.13.14 and Eq.13.15 facts supplied by
    `Algorithm13_3Implementation1LocalSpec`; recursive execution, rounded Schur
    update, product laws, scalar comparisons, and the solve perturbation
    hypotheses remain explicit. -/
theorem demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_solve_layers_and_implementation1_local_spec
    {n p r s q : Type*} [Fintype n] [Fintype r]
    (A DeltaA_fact Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (XhatSolve B Yhat : Matrix n p ℝ)
    (u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack : ℝ)
    (c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (XhatLocal D : Matrix r q ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hc : d_fact + cForward + cBack ≤ d_solve)
    (hFactSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA_fact Lhat Uhat)
    (hLeading :
      u * (δ * normA + θ * normL * normU) ≤
        d_fact * u * (normA + normL * normU))
    (hForward : (Lhat + DeltaL) * Yhat = B)
    (hBack : (Uhat + DeltaU) * XhatSolve = Yhat)
    (hDeltaLU : FirstOrderLe u
      (cForward * u * (normA + normL * normU)) normDeltaLU)
    (hLDeltaU : FirstOrderLe u
      (cBack * u * (normA + normL * normU)) normLDeltaU)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤
        normDeltaA_fact + normDeltaLU + normLDeltaU + normDeltaLDeltaU)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D) :
    (Lhat * Uhat = A + DeltaA_fact) ∧
      ((A + (DeltaA_fact + DeltaL * Uhat + Lhat * DeltaU +
        DeltaL * DeltaU)) * XhatSolve = B) ∧
      DemmelHighamSchreiber13_6Theorem2_1Result
        u d_fact d_solve normA normL normU
        normDeltaA_fact normDeltaA_solve
        recursiveExecution schurUpdate
        (Lhat21 * A11 = A21 + E21)
        (BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21)
        ((Uii + DeltaUii) * XhatLocal = D)
        (DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)
        maxEntryProductLaws := by
  rcases
    higham13_algorithm13_3_implementation1_eq13_14_15_from_spec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D hLocal with
    ⟨hBlock, hDiag⟩
  exact
    demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_and_solve_perturbation_layers
      A DeltaA_fact Lhat Uhat DeltaL DeltaU XhatSolve B Yhat
      u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack recursiveExecution schurUpdate
      (Lhat21 * A11 = A21 + E21)
      (BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21)
      ((Uii + DeltaUii) * XhatLocal = D)
      (DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)
      maxEntryProductLaws hRecursiveExecution hSchurUpdate hBlock.1
      hBlock.2 hDiag.1 hDiag.2 hMaxEntryProductLaws hu hA hL hU hc
      hFactSpec hLeading hForward hBack hDeltaLU hLDeltaU
      hDeltaLDeltaU hTotal

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 / equation (13.16), routed through the checked partitioned
    factorization layer and the named DHS forward/back substitution branch
    specs.

    This wrapper keeps the Algorithm 13.3 local Eq.13.14/Eq.13.15 facts
    supplied by `Algorithm13_3Implementation1LocalSpec`, while the DHS
    Theorem 2.1 source-path fields are the stricter global forward/back branch
    specs recovered from the Pro audit.  It is dependency progress only: the
    operational construction of those branch specs, recursive execution,
    rounded Schur update, product laws, and scalar comparisons remain explicit
    premises. -/
theorem higham13_theorem13_6_implementation1_from_DHS_partitioned_forward_back_substitution_specs_and_implementation1_local_spec
    {n p r s q : Type*} [Fintype n] [Fintype r]
    (A DeltaA_fact Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (XhatSolve B Yhat : Matrix n p ℝ)
    (u δ θ d_fact d_solve dn normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack : ℝ)
    (c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (XhatLocal D : Matrix r q ℝ)
    (recursiveExecution schurUpdate blockRowRHS localSolveSuccess
      maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hBlockRowRHS : blockRowRHS)
    (hSolveSuccess : localSolveSuccess)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hc : d_fact + cForward + cBack ≤ d_solve)
    (hFactSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA_fact Lhat Uhat)
    (hLeading :
      u * (δ * normA + θ * normL * normU) ≤
        d_fact * u * (normA + normL * normU))
    (hForward :
      DHSBlockForwardSubstitutionFirstOrderSpec
        u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
    (hBack :
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU normLDeltaU Uhat DeltaU XhatSolve Yhat)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤
        normDeltaA_fact + normDeltaLU + normLDeltaU + normDeltaLDeltaU)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D) :
    (Lhat * Uhat = A + DeltaA_fact) ∧
      ((A + (DeltaA_fact + DeltaL * Uhat + Lhat * DeltaU +
        DeltaL * DeltaU)) * XhatSolve = B) ∧
      (((Lhat21 * A11 = A21 + E21 ∧
          BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21) ∧
        ((Uii + DeltaUii) * XhatLocal = D ∧
          DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)) ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          normDeltaA_fact ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          normDeltaA_solve ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          (max normDeltaA_fact normDeltaA_solve)) := by
  rcases
    demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_forward_back_substitution_specs
      A DeltaA_fact Lhat Uhat DeltaL DeltaU XhatSolve B Yhat
      u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack recursiveExecution schurUpdate blockRowRHS
      localSolveSuccess maxEntryProductLaws hRecursiveExecution hSchurUpdate
      hBlockRowRHS hSolveSuccess hMaxEntryProductLaws hu hA hL hU hc
      hFactSpec hLeading hForward hBack hDeltaLDeltaU hTotal with
    ⟨hFactEq, hSolveEq, hDHS⟩
  exact
    ⟨hFactEq, hSolveEq,
      higham13_theorem13_6_implementation1_from_DHS_theorem2_1_result
        u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
        Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D
        normDeltaA_fact normDeltaA_solve normA normL normU
        d_fact d_solve dn recursiveExecution schurUpdate blockRowRHS
        (DHSBlockForwardSubstitutionFirstOrderSpec
          u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
        (DHSBlockBackSubstitutionFirstOrderSpec
          u cBack normA normL normU normLDeltaU Uhat DeltaU XhatSolve Yhat)
        localSolveSuccess maxEntryProductLaws hu hA hL hU hd_fact hd_solve
        hLocal hDHS⟩

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 / equation (13.16), routed through named DHS forward/back
    branch specs, with the factorization scalar comparison derived from
    coefficient bounds.

    This is the coefficient-bound companion to
    `higham13_theorem13_6_implementation1_from_DHS_partitioned_forward_back_substitution_specs_and_implementation1_local_spec`.
    It removes the raw partitioned leading-term comparison from the
    implementation-facing surface when the source proof has supplied
    `δ ≤ d_fact` and `θ ≤ d_fact`. -/
theorem higham13_theorem13_6_implementation1_from_DHS_partitioned_forward_back_substitution_specs_of_coeff_bounds_and_implementation1_local_spec
    {n p r s q : Type*} [Fintype n] [Fintype r]
    (A DeltaA_fact Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (XhatSolve B Yhat : Matrix n p ℝ)
    (u δ θ d_fact d_solve dn normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack : ℝ)
    (c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (XhatLocal D : Matrix r q ℝ)
    (recursiveExecution schurUpdate blockRowRHS localSolveSuccess
      maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hBlockRowRHS : blockRowRHS)
    (hSolveSuccess : localSolveSuccess)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hδ : δ ≤ d_fact) (hθ : θ ≤ d_fact)
    (hc : d_fact + cForward + cBack ≤ d_solve)
    (hFactSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA_fact Lhat Uhat)
    (hForward :
      DHSBlockForwardSubstitutionFirstOrderSpec
        u cForward normA normL normU normDeltaLU Lhat DeltaL Yhat B)
    (hBack :
      DHSBlockBackSubstitutionFirstOrderSpec
        u cBack normA normL normU normLDeltaU Uhat DeltaU XhatSolve Yhat)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤
        normDeltaA_fact + normDeltaLU + normLDeltaU + normDeltaLDeltaU)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D) :
    (Lhat * Uhat = A + DeltaA_fact) ∧
      ((A + (DeltaA_fact + DeltaL * Uhat + Lhat * DeltaU +
        DeltaL * DeltaU)) * XhatSolve = B) ∧
      (((Lhat21 * A11 = A21 + E21 ∧
          BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21) ∧
        ((Uii + DeltaUii) * XhatLocal = D ∧
          DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)) ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          normDeltaA_fact ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          normDeltaA_solve ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          (max normDeltaA_fact normDeltaA_solve)) := by
  exact
    higham13_theorem13_6_implementation1_from_DHS_partitioned_forward_back_substitution_specs_and_implementation1_local_spec
      A DeltaA_fact Lhat Uhat DeltaL DeltaU XhatSolve B Yhat
      u δ θ d_fact d_solve dn normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack c₄ c₅ normLhat21 normA11 normE21 normUii
      normDeltaUii Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D
      recursiveExecution schurUpdate blockRowRHS localSolveSuccess
      maxEntryProductLaws hRecursiveExecution hSchurUpdate hBlockRowRHS
      hSolveSuccess hMaxEntryProductLaws hu hA hL hU hd_fact hd_solve hc
      hFactSpec
      (demmelHighamSchreiber13_6_partitioned_leading_term_le_of_coeff_bounds
        u δ θ d_fact normA normL normU hu hA hL hU hδ hθ)
      hForward hBack hDeltaLDeltaU hTotal hLocal

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 / equation (13.16), routed through the checked partitioned
    factorization and solve perturbation layers with the concrete
    Eq.13.14/Eq.13.15 local source path.

    This is still not the omitted DHS implementation proof: it keeps recursive
    execution, rounded Schur update, product laws, scalar comparisons, and solve
    perturbation hypotheses explicit.  Its role is to prevent the final
    Implementation 1 wrapper from accepting arbitrary DHS source-path facts once
    `Algorithm13_3Implementation1LocalSpec` is available. -/
theorem higham13_theorem13_6_implementation1_from_DHS_partitioned_solve_layers_and_implementation1_local_spec
    {n p r s q : Type*} [Fintype n] [Fintype r]
    (A DeltaA_fact Lhat Uhat DeltaL DeltaU : Matrix n n ℝ)
    (XhatSolve B Yhat : Matrix n p ℝ)
    (u δ θ d_fact d_solve dn normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack : ℝ)
    (c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (XhatLocal D : Matrix r q ℝ)
    (recursiveExecution schurUpdate maxEntryProductLaws : Prop)
    (hRecursiveExecution : recursiveExecution)
    (hSchurUpdate : schurUpdate)
    (hMaxEntryProductLaws : maxEntryProductLaws)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hc : d_fact + cForward + cBack ≤ d_solve)
    (hFactSpec : PartitionedLUFirstOrderSpec u δ θ normA normL normU
      normDeltaA_fact A DeltaA_fact Lhat Uhat)
    (hLeading :
      u * (δ * normA + θ * normL * normU) ≤
        d_fact * u * (normA + normL * normU))
    (hForward : (Lhat + DeltaL) * Yhat = B)
    (hBack : (Uhat + DeltaU) * XhatSolve = Yhat)
    (hDeltaLU : FirstOrderLe u
      (cForward * u * (normA + normL * normU)) normDeltaLU)
    (hLDeltaU : FirstOrderLe u
      (cBack * u * (normA + normL * normU)) normLDeltaU)
    (hDeltaLDeltaU : FirstOrderLe u 0 normDeltaLDeltaU)
    (hTotal :
      normDeltaA_solve ≤
        normDeltaA_fact + normDeltaLU + normLDeltaU + normDeltaLDeltaU)
    (hLocal : Algorithm13_3Implementation1LocalSpec
      u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
      Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D) :
    (Lhat * Uhat = A + DeltaA_fact) ∧
      ((A + (DeltaA_fact + DeltaL * Uhat + Lhat * DeltaU +
        DeltaL * DeltaU)) * XhatSolve = B) ∧
      (((Lhat21 * A11 = A21 + E21 ∧
          BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21) ∧
        ((Uii + DeltaUii) * XhatLocal = D ∧
          DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)) ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          normDeltaA_fact ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          normDeltaA_solve ∧
        FirstOrderLe u (dn * u * (normA + normL * normU))
          (max normDeltaA_fact normDeltaA_solve)) := by
  rcases
    demmelHighamSchreiber13_6_theorem2_1_result_from_partitioned_solve_layers_and_implementation1_local_spec
      A DeltaA_fact Lhat Uhat DeltaL DeltaU XhatSolve B Yhat
      u δ θ d_fact d_solve normA normL normU normDeltaA_fact
      normDeltaA_solve normDeltaLU normLDeltaU normDeltaLDeltaU
      cForward cBack c₄ c₅ normLhat21 normA11 normE21 normUii
      normDeltaUii Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D
      recursiveExecution schurUpdate maxEntryProductLaws
      hRecursiveExecution hSchurUpdate hMaxEntryProductLaws
      hu hA hL hU hc hFactSpec hLeading hForward hBack hDeltaLU
      hLDeltaU hDeltaLDeltaU hTotal hLocal with
    ⟨hFactEq, hSolveEq, hDHS⟩
  exact
    ⟨hFactEq, hSolveEq,
      higham13_theorem13_6_implementation1_from_DHS_theorem2_1_result
        u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
        Lhat21 A21 E21 A11 Uii DeltaUii XhatLocal D
        normDeltaA_fact normDeltaA_solve normA normL normU
        d_fact d_solve dn recursiveExecution schurUpdate
        (Lhat21 * A11 = A21 + E21)
        (BlockSolveFirstOrderBound u c₄ normLhat21 normA11 normE21)
        ((Uii + DeltaUii) * XhatLocal = D)
        (DiagonalBlockSolveFirstOrderBound u c₅ normUii normDeltaUii)
        maxEntryProductLaws hu hA hL hU hd_fact hd_solve hLocal hDHS⟩

/-- Higham, 2nd ed., Chapter 13, Theorem 13.6 / equation (13.16), conditional
    on the Demmel--Higham--Schreiber [326] implementation estimates.

    This theorem is deliberately conditional: it packages the existing scalar
    aggregation around the named [326]-level estimate predicate.  It does not
    prove the cited implementation analysis and therefore does not close the
    Theorem 13.6 source row by itself. -/
theorem higham13_theorem13_6_eq13_16_firstOrder_from_DHS_estimates
    (normDeltaA_fact normDeltaA_solve : ℝ)
    (normA normL normU u d_fact d_solve dn : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hd_fact : d_fact ≤ dn) (hd_solve : d_solve ≤ dn)
    (hEst : DemmelHighamSchreiber13_6Estimates
      u d_fact d_solve normA normL normU normDeltaA_fact normDeltaA_solve) :
    FirstOrderLe u (dn * u * (normA + normL * normU)) normDeltaA_fact ∧
      FirstOrderLe u (dn * u * (normA + normL * normU)) normDeltaA_solve ∧
      FirstOrderLe u (dn * u * (normA + normL * normU))
        (max normDeltaA_fact normDeltaA_solve) := by
  exact higham13_theorem13_6_eq13_16_firstOrder_from_factor_solve_estimates
    normDeltaA_fact normDeltaA_solve normA normL normU u d_fact d_solve dn
    hu hA hL hU hd_fact hd_solve hEst.factorization hEst.solve

/-- Higham, 2nd ed., Chapter 13, Algorithm 13.3 Implementation 1 and
    Theorem 13.6 / equation (13.16), conditional on the cited
    Demmel--Higham--Schreiber [326] estimates.

    This source-facing wrapper keeps both sides of the conditional theorem
    visible: the local computed path supplies equations (13.14) and (13.15),
    while `DemmelHighamSchreiber13_6Estimates` is the still-open
    implementation analysis needed to obtain the two first-order Eq.13.16
    backward-error bounds. -/
theorem higham13_theorem13_6_implementation1_conditional_from_DHS_estimates
    {r s p : Type*} [Fintype r]
    (u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ)
    (normDeltaA_fact normDeltaA_solve : ℝ)
    (normA normL normU d_fact d_solve dn : ℝ)
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
    ⟨higham13_algorithm13_3_implementation1_eq13_14_15_from_spec
        u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii
        Lhat21 A21 E21 A11 Uii DeltaUii Xhat D hLocal,
      higham13_theorem13_6_eq13_16_firstOrder_from_DHS_estimates
        normDeltaA_fact normDeltaA_solve normA normL normU u
        d_fact d_solve dn hu hA hL hU hd_fact hd_solve hEst⟩

/-- Higham, 2nd ed., Chapter 13, p.251, Algorithm 13.3 Implementation 2:
    if the exact-inverse local analysis has multiplied the factorization and
    solve first-order terms in (13.16) by a common condition-number majorant
    `max_i κ(Ûᵢᵢ)`, then the combined scalar first-order (13.16) bound carries
    precisely that multiplier.

    This is a scalar consequence of the source-facing first-order premises.  It
    does not prove that a concrete explicit-inverse implementation supplies
    those conditioned local bounds. -/
theorem higham13_algorithm13_3_implementation2_eq13_16_firstOrder_multiplier
    (normΔA_fact normΔA_solve : ℝ)
    (normA normL normU u d_fact d_solve kappaMax : ℝ)
    (hu : 0 ≤ u) (hkappa : 0 ≤ kappaMax)
    (hA : 0 ≤ normA) (hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (hFact : FirstOrderLe u
      ((kappaMax * d_fact) * u * (normA + normL * normU)) normΔA_fact)
    (hSolve : FirstOrderLe u
      ((kappaMax * d_solve) * u * (normA + normL * normU)) normΔA_solve) :
    FirstOrderLe u
      (kappaMax * (max d_fact d_solve * u * (normA + normL * normU)))
      (max normΔA_fact normΔA_solve) := by
  have hbase :
      FirstOrderLe u
        (max (kappaMax * d_fact) (kappaMax * d_solve) *
          u * (normA + normL * normU))
        (max normΔA_fact normΔA_solve) :=
    block_lu_solve_backward_error_firstOrder
      normΔA_fact normΔA_solve normA normL normU u
      (kappaMax * d_fact) (kappaMax * d_solve)
      hu hA hL hU hFact hSolve
  refine hbase.mono_leading ?_
  have hsum : 0 ≤ normA + normL * normU := by
    linarith [mul_nonneg hL hU]
  have husum : 0 ≤ u * (normA + normL * normU) := mul_nonneg hu hsum
  have hmax :
      max (kappaMax * d_fact) (kappaMax * d_solve) ≤
        kappaMax * max d_fact d_solve := by
    apply max_le
    · exact mul_le_mul_of_nonneg_left (le_max_left d_fact d_solve) hkappa
    · exact mul_le_mul_of_nonneg_left (le_max_right d_fact d_solve) hkappa
  calc
    max (kappaMax * d_fact) (kappaMax * d_solve) *
        u * (normA + normL * normU)
        = max (kappaMax * d_fact) (kappaMax * d_solve) *
          (u * (normA + normL * normU)) := by ring
    _ ≤ (kappaMax * max d_fact d_solve) *
          (u * (normA + normL * normU)) :=
        mul_le_mul_of_nonneg_right hmax husum
    _ = kappaMax * (max d_fact d_solve * u * (normA + normL * normU)) := by ring

end NumStability
